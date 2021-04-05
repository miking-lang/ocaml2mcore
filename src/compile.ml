open Format
open Printf
open Boot.Ast
open Boot.Msg
open Boot.Pprint
open Boot.Ustring
open Boot.Intrinsics
open Lambda
open Asttypes

(** Compiles an OCaml source file (.ml file) into MCore **)

module SS = Set.Make (String)
module IM = Map.Make (Int)
module SM = Map.Make (String)

(* Command line options *)
let enable_debug_parsed = ref false

let enable_debug_typed = ref false

let enable_debug_lambda = ref false

let enable_compile_mcore = ref false

let output_file = ref "stdout"

(* Default file info names *)
let prefix = "test"

let filename = prefix ^ ".ml"

let modulename = "Test"

(* MCore no-op instruction *)
let mcore_noop = tmUnit

(* Pretty print an MExpr AST *)
let pprint_mcore tm = to_utf8 (ustring_of_tm tm)

(* AST helper functions *)
let int2ustring = Boot.Ustring.Op.ustring_of_int

let mk_ident m ident = from_utf8 (m ^ Ident.name ident)

let mk_string str =
  TmSeq
    ( NoInfo
    , Mseq.Helpers.map
        (fun x -> TmConst (NoInfo, CChar x))
        (from_latin1 str |> Mseq.Helpers.of_ustring) )

let mk_let ident body inexpr =
  TmLet (NoInfo, ident, Symb.Helpers.nosym, TyUnknown NoInfo, body, inexpr)

let mk_lam ident body =
  TmLam (NoInfo, ident, Symb.Helpers.nosym, TyUnknown NoInfo, body)

let mk_seq body inexpr = mk_let (from_utf8 "") body inexpr

let mk_ite cnd thn els = TmMatch (NoInfo, cnd, PatBool (NoInfo, true), thn, els)

let mk_var m s = TmVar (NoInfo, from_utf8 (m ^ s), Symb.Helpers.nosym)

let mk_var_ident m ident = mk_var m (Ident.name ident)

let record_from_list binds =
  List.fold_left (fun a (k, v) -> Record.add k v a) Record.empty binds

let record_ binds = TmRecord (NoInfo, record_from_list binds)

let tyrecord_ binds = TyRecord (NoInfo, record_from_list binds)

let precord_ binds = PatRecord (NoInfo, record_from_list binds)

let tyarrow_ l h = TyArrow (NoInfo, l, h)

let tyvar_ s = TyVar (NoInfo, from_utf8 s, Symb.Helpers.nosym)

let tyunknown_ = TyUnknown NoInfo

let pcon_ c p = PatCon (NoInfo, from_utf8 c, Symb.Helpers.nosym, p)

let pnamed_ s = PatNamed (NoInfo, NameStr (s, Symb.Helpers.nosym))

let mk_tuple fields =
  let rec work n binds = function
    | [] ->
        record_ binds
    | x :: xs ->
        work (n + 1) ((int2ustring n, x) :: binds) xs
  in
  work 0 [] fields

let mk_tuple_proj n r =
  TmMatch
    ( NoInfo
    , r
    , PatRecord
        ( NoInfo
        , record_from_list
            [ ( int2ustring n
              , PatNamed (NoInfo, NameStr (from_utf8 "x", Symb.Helpers.nosym))
              ) ] )
    , mk_var "" "x"
    , TmNever NoInfo )

let fail_constapp f args =
  failwith
    ( "Incorrect application. Function: "
    ^ to_utf8 (ustring_of_const f)
    ^ ", arguments: "
    ^ String.concat " " (List.map (fun x -> ustring_of_tm x |> to_utf8) args)
    )

let mk_constapp1 op args =
  match args with
  | [a] ->
      TmApp (NoInfo, TmConst (NoInfo, op), a)
  | _ ->
      fail_constapp op args

let mk_constapp2 op args =
  match args with
  | [a1; a2] ->
      TmApp (NoInfo, TmApp (NoInfo, TmConst (NoInfo, op), a1), a2)
  | _ ->
      fail_constapp op args

let int_ = function
  | i when i < 0 ->
      (* NOTE(Linnea, 2021-03-17): Use negi to ensure parsability *)
      TmApp (NoInfo, TmConst (NoInfo, Cnegi), TmConst (NoInfo, CInt (-i)))
  | i ->
      TmConst (NoInfo, CInt i)

let pint_ n = PatInt (NoInfo, n)

let true_ = TmConst (NoInfo, CBool true)

let false_ = TmConst (NoInfo, CBool false)

let land_ b1 b2 = mk_ite b1 b2 false_

let lor_ b1 b2 = mk_ite b1 true_ b2

let not_ b = mk_ite b false_ true_

(* Prelude *)
(* TODO(linnea, 2021-03-19): Some (all?) of these functions should be included
   from stdlib once they compile. *)
let print_ln = "let printLn = lam s. print s; print \"\\n\""

let include_print_ln = ref false

let int2string =
  "let int2string = lam n.\n\
  \  recursive\n\
  \  let int2string_rechelper = lam n.\n\
  \    if lti n 10\n\
  \    then [int2char (addi n (char2int '0'))]\n\
  \    else\n\
  \      let d = [int2char (addi (modi n 10) (char2int '0'))] in\n\
  \      concat (int2string_rechelper (divi n 10)) d\n\
  \  in\n\
  \  if lti n 0\n\
  \  then cons '-' (int2string_rechelper (negi n))\n\
  \  else int2string_rechelper n\n"

let include_int2string = ref false

let string2int =
  "let head = lam seq. get seq 0\n\n\
   let tail = lam seq. subsequence seq 1 (subi (length seq) 1)\n\n\
   let string2int = lam s.\n\
  \  recursive\n\
  \  let string2int_rechelper = lam s.\n\
  \    let len = length s in\n\
  \    let last = subi len 1 in\n\
  \    if eqi len 0\n\
  \    then 0\n\
  \    else\n\
  \      let lsd = subi (char2int (get s last)) (char2int '0') in\n\
  \      let rest = muli 10 (string2int_rechelper (subsequence s 0 last)) in\n\
  \      addi rest lsd\n\
  \  in\n\
  \  match s with [] then 0 else\n\
  \  if eqc '-' (head s)\n\
  \  then negi (string2int_rechelper (tail s))\n\
  \  else string2int_rechelper s\n"

let include_string2int = ref false

let prelude () =
  String.concat ""
    (List.map
       (fun (r, f) -> if !r then f ^ "\n" else "")
       [ (include_print_ln, print_ln)
       ; (include_int2string, int2string)
       ; (include_string2int, string2int) ] )

(* Global set of MCore files to include *)
let includes_ref = ref SS.empty

let add_include filename =
  includes_ref := SS.add (sprintf "include \"%s\"" filename) !includes_ref

(* Global set of in-file defined modules *)
(* TODO(Linnea, 2021-03-16): Module aliases are not yet supported *)
let modules_defined = ref SS.empty

let add_module_def ident = modules_defined := SS.add ident !modules_defined

let module_is_defined ident = SS.mem ident !modules_defined

(* Global map of error handlers *)
(* NOTE(linnea, 2021-03-17): "exit n" will be replaced by the error handler n *)
let error_handlers = ref (IM.empty : tm IM.t)

let add_error_handler n handler =
  error_handlers := IM.add n handler !error_handlers

let get_error_handler n = IM.find_opt n !error_handlers

(* Set of global type declarations *)
let typedecl = ref (SM.empty : tm SM.t)

let add_tagged_type name binds =
  let t =
    TmConDef
      ( NoInfo
      , from_utf8 name
      , Symb.Helpers.nosym
      , tyarrow_ (tyrecord_ binds) (tyvar_ "Tagged")
      , record_ [] )
  in
  typedecl := SM.add name t !typedecl

let get_typedecl () =
  let remove_suffix suffix str =
    String.sub str 0 (String.length str - String.length suffix)
  in
  let constr =
    List.map
      (fun (_, v) -> pprint_mcore v |> remove_suffix " in ()")
      (SM.bindings !typedecl)
  in
  match constr with
  | [] ->
      ""
  | _ ->
      String.concat "\n" ("type Tagged" :: constr) ^ "\n"

(* Get the module name from a fully qualified identifier *)
let get_module ident =
  String.split_on_char '.' ident
  |> List.rev |> List.tl |> List.rev |> String.concat "."

(* Parse an OCaml .ml file *)
let parse_file filename =
  let ast = Parse.implementation (open_in filename |> Lexing.from_channel) in
  if !enable_debug_parsed then (
    printf "\n--- After parsing of OCaml source file ---\n" ;
    print_endline (Pprintast.string_of_structure ast) )
  else () ;
  ast

(* Typecheck an OCaml AST *)
let typecheck ast =
  let typed =
    Typemod.type_implementation filename prefix modulename
      (Compmisc.initial_env ()) ast
  in
  if !enable_debug_typed then (
    printf "\n--- After type checking ---\n" ;
    Printtyped.implementation_with_coercion std_formatter typed ;
    print_newline () )
  else () ;
  typed

(* Pretty print a Lambda program *)
let pprint_lambda lam =
  Printlambda.lambda std_formatter lam ;
  print_newline ()

(* Convert a typed AST to Lambda IR *)
let typed2lambda typed =
  let lamprog = Translmod.transl_implementation modulename typed in
  if !enable_debug_lambda then (
    printf "\n--- After conversion to Lambda IR ---\n" ;
    pprint_lambda lamprog.code )
  else () ;
  lamprog

(* Compile a Lambda constant *)
let compile_constant = function
  | Const_int i ->
      int_ i
  | Const_char c ->
      (* NOTE(Linnea, 2021-03-18): handle chars as ints, as chars are translated
         into ints in pattern matching. This might raise other problems and might
         therefore change in the future. *)
      int_ (int_of_char c)
  | Const_float f ->
      TmConst (NoInfo, CFloat (float_of_string f))
  (* TODO(Linnea, 2021-03-10): What does the delim do? *)
  | Const_string (str, delim) ->
      mk_string str
  | Const_int32 i ->
      failwith "int32"
  | Const_int64 i ->
      failwith "int64"
  | Const_nativeint i ->
      failwith "nativeint"

(* Compile a Lambda structured constant *)
let rec compile_structured_constant = function
  | Const_base c ->
      compile_constant c
  (* NOTE(Linnea, 2021-03-10): {true, false} are represented as Const_pointer
     {1, 0} respectively. *)
  (* TODO(Linnea, 2021-03-10): Unit has the same representation as false. We
     probably need to make a distinction when compiling to MExpr, so we will
     need to track from the typed tree whether the value was unit *)
  | Const_pointer 0 ->
      false_
  | Const_pointer 1 ->
      true_
  | Const_pointer _ ->
      failwith "const_pointer"
  | Const_block (tag, str_const_list, (Tag_record | Tag_tuple)) ->
      let consts = List.map compile_structured_constant str_const_list in
      mk_tuple consts
  | Const_block (tag, str_const_list, Tag_con name) ->
      let consts = List.map compile_structured_constant str_const_list in
      add_tagged_type name
        (List.mapi (fun i _ -> (int2ustring i, tyunknown_)) str_const_list) ;
      TmConApp (NoInfo, from_utf8 name, Symb.Helpers.nosym, mk_tuple consts)
  | Const_block (tag, str_const_list, Tag_none) ->
      failwith "Unknown tag"
  | Const_float_array _ ->
      failwith "float_array"
  | Const_immstring _ ->
      failwith "immstring"

(* Compile a Lambda primitive *)
let rec compile_primitive (p : Lambda.primitive) args =
  (* NOTE(Linnea, 2021-03-10): Applications of primitive functions are never
     curried here *)
  match p with
  | Pidentity ->
      failwith "identity"
  | Pbytes_to_string ->
      failwith "bytes_to_string"
  | Pbytes_of_string ->
      failwith "bytes_of_string"
  | Pignore -> (
    match args with
    | [a] ->
        mk_seq a tmUnit
    | _ ->
        failwith "Expected one argument to ignore" )
  | Prevapply -> (
    match args with
    | [rhs; lhs] ->
        TmApp (NoInfo, lhs, rhs)
    | _ ->
        failwith "Expected two arguments to revapply" )
  | Pdirapply ->
      failwith "dirapply"
  (* Operations on heap blocks *)
  | Pmakeblock (_tag, _mut, _shape) ->
      mk_tuple args
  | Pfield (n, Pointer, Immutable, Fmodule_access s) -> (
    (* Hard coded module accesses *)
    match s with
    | "Stdlib.print_endline" ->
        include_print_ln := true ;
        mk_var "" "printLn"
    | "Stdlib.string_of_int" ->
        include_int2string := true ;
        mk_var "" "int2string"
    | "Stdlib.^" ->
        TmConst (NoInfo, Cconcat None)
    | "Stdlib.Char.escaped" ->
        add_include "char.mc" ;
        Boot.Parserutils.parse_mexpr_string
          (from_utf8 "lam c. escapeChar (int2char c)")
    | "Stdlib.read_line" ->
        mk_var "" "readLine"
    | _ when module_is_defined (get_module s) ->
        mk_var "" s
    | _ ->
        (* TODO(Linnea, 2021-03-16): External dependency, should be marked in some
           way. *)
        mk_var "" s )
  | Pfield (n, (Pointer | Immediate), Immutable, (Frecord_access _ | Ftuple))
    -> (
    match args with
    | [r] ->
        mk_tuple_proj n r
    | _ ->
        failwith "Expected one argument to Pfield immediate" )
  | Pfield (n, Pointer, Immutable, _) -> (
    (* NOTE(Linnea, 2021-03-26): Assume for now it's an access in a tagged
       structure *)
    match args with
    | [r] ->
        mk_tuple_proj n r
    | _ ->
        failwith "Expected one argument to Pfield immediate" )
  | Pfield (_, _, _, _) ->
      failwith "Pfield"
  | Pfield_computed
  | Psetfield (_, _, _)
  | Psetfield_computed (_, _)
  | Pfloatfield _
  | Psetfloatfield (_, _)
  | Pduprecord (_, _) ->
      failwith "Operation on heap blocks not implemented"
  (* Context switches *)
  | Prunstack | Pperform | Presume | Preperform ->
      failwith "Context swith operations not implemented"
  (* External call *)
  | Pccall {prim_name= "caml_int_of_string"} -> (
    match args with
    | [a] ->
        include_string2int := true ;
        TmApp (NoInfo, mk_var "" "string2int", a)
    | _ ->
        failwith "Expected one argument to caml_int_of_string" )
  | Pccall desc ->
      failwith ("External call " ^ desc.prim_name ^ " not implemented")
  (* Exceptions *)
  | Praise raise_kind ->
      failwith "Raise not implemented"
  (* Boolean operations *)
  | Psequand -> (
    (* if b1 then b2 else false *)
    match args with
    | [b1; b2] ->
        land_ b1 b2
    | _ ->
        failwith "Expected two arguments to Boolean and" )
  | Psequor -> (
    (* if b1 then true else b2 *)
    match args with
    | [b1; b2] ->
        lor_ b1 b2
    | _ ->
        failwith "Expected two arguments to Boolean and" )
  | Pnot -> (
    (* if b then false else true *)
    match args with
    | [b] ->
        not_ b
    | _ ->
        failwith "Expected one argument to Boolean not" )
  (* Globals *)
  | Psetglobal ident -> (
    match args with [instr] -> instr | _ -> failwith "setglobal" )
  | Pgetglobal ident ->
      mk_var_ident "" ident
  (* Integer operations *)
  | Paddint ->
      mk_constapp2 (Caddi None) args
  | Psubint ->
      mk_constapp2 (Csubi None) args
  | Pmulint ->
      mk_constapp2 (Cmuli None) args
  | Pdivint _ ->
      mk_constapp2 (Cdivi None) args
  | Pmodint _ ->
      mk_constapp2 (Cmodi None) args
  | Pandint ->
      failwith "andint"
  | Porint ->
      failwith "orint"
  | Pxorint ->
      failwith "xorint"
  | Plslint ->
      mk_constapp2 (Cslli None) args
  | Plsrint ->
      mk_constapp2 (Csrli None) args
  | Pasrint ->
      mk_constapp2 (Csrai None) args
  | Pintcomp Ceq ->
      mk_constapp2 (Ceqi None) args
  | Pintcomp Cne ->
      mk_constapp2 (Cneqi None) args
  | Pintcomp Clt ->
      mk_constapp2 (Clti None) args
  | Pintcomp Cgt ->
      mk_constapp2 (Cgti None) args
  | Pintcomp Cle ->
      mk_constapp2 (Cleqi None) args
  | Pintcomp Cge ->
      mk_constapp2 (Cgeqi None) args
  | Pnegint ->
      mk_constapp1 Cnegi args
  | Poffsetint i ->
      mk_constapp2 (Caddi None) (int_ i :: args)
  | Poffsetref i ->
      failwith "offsetref"
  (* Float operations *)
  | Pintoffloat ->
      mk_constapp1 Cfloorfi args
  | Pfloatofint ->
      mk_constapp1 Cint2float args
  | Pnegfloat ->
      mk_constapp1 Cnegf args
  | Paddfloat ->
      mk_constapp2 (Caddf None) args
  | Psubfloat ->
      mk_constapp2 (Csubf None) args
  | Pmulfloat ->
      mk_constapp2 (Cmulf None) args
  | Pdivfloat ->
      mk_constapp2 (Cdivf None) args
  | Pabsfloat ->
      (* TODO(linnea, 2021-03-24): Rediscover this pattern in OCaml compiler *)
      (* if 0.0 <= f then f else -f *)
      TmMatch
        ( NoInfo
        , mk_constapp2 (Cleqf None) (TmConst (NoInfo, CFloat 0.0) :: args)
        , PatBool (NoInfo, true)
        , List.hd args
        , mk_constapp1 Cnegf args )
  | Pfloatcomp CFeq ->
      mk_constapp2 (Ceqf None) args
  | Pfloatcomp CFneq ->
      mk_constapp2 (Cneqf None) args
  | Pfloatcomp CFlt ->
      mk_constapp2 (Cltf None) args
  | Pfloatcomp CFle ->
      mk_constapp2 (Cleqf None) args
  | Pfloatcomp CFgt ->
      mk_constapp2 (Cgtf None) args
  | Pfloatcomp CFge ->
      mk_constapp2 (Cgeqf None) args
  (* TODO(Linnea, 2021-03-21): negated float comparisons, when are they used?
     Not tested. *)
  | Pfloatcomp CFnlt ->
      (* mk_constapp2 (Cgeqf None) args *)
      failwith "CFnlt"
  | Pfloatcomp CFnle ->
      (* mk_constapp2 (Cgtf None) args *)
      failwith "CFnle"
  | Pfloatcomp CFngt ->
      (* mk_constapp2 (Cleqf None) args *)
      failwith "CFngt"
  | Pfloatcomp CFnge ->
      (* mk_constapp2 (Cltf None) args *)
      failwith "CFnge"
  (* String operations *)
  | Pstringlength ->
      mk_constapp1 Clength args
  | Pstringrefs ->
      mk_constapp2 (Cget None) args
  (* TODO(Linnea, 2021-03-14): Unsafe strings *)
  | Pstringrefu ->
      failwith "Unsafe strings not implemented"
  (* TODO(Linnea, 2021-03-14): Mutable byte strings, compile into tensors? *)
  | Pbyteslength | Pbytesrefu | Pbytessetu | Pbytesrefs | Pbytessets ->
      failwith "Operations on bytes not implemented"
  (* Array operations *)
  | Pmakearray (array_kind, mutable_flag) | Pduparray (array_kind, mutable_flag)
    ->
      failwith "Array operation not implemented"
  (* For [Pduparray], the argument must be an immutable array.
      The arguments of [Pduparray] give the kind and mutability of the
      array being *produced* by the duplication. *)
  | Parraylength array_kind
  | Parrayrefu array_kind
  | Parraysetu array_kind
  | Parrayrefs array_kind
  | Parraysets array_kind ->
      failwith "Array operation not implemented"
  | Pisint ->
      failwith "Array operation not implemented"
  (* Test if the (integer) argument is outside an interval *)
  | Pisout -> (
    match args with
    | [_upper; n] ->
        lor_
          (mk_constapp2 (Clti None) args)
          (mk_constapp2 (Clti None) [n; int_ 0])
    | _ ->
        failwith "Expected two arguments to isout" )
  (* Operations on boxed integers (Nativeint.t, Int32.t, Int64.t) *)
  | Pbintofint boxed_integer
  | Pintofbint boxed_integer
  | Pnegbint boxed_integer
  | Paddbint boxed_integer
  | Psubbint boxed_integer
  | Pmulbint boxed_integer
  | Pandbint boxed_integer
  | Porbint boxed_integer
  | Pxorbint boxed_integer
  | Plslbint boxed_integer
  | Plsrbint boxed_integer
  | Pasrbint boxed_integer ->
      failwith "Boxed integer operation not implemented"
  | Pcvtbint (source, destination) ->
      failwith "Boxed integer operation not implemented"
  | Pdivbint {size= boxed_integer; is_safe}
  | Pmodbint {size= boxed_integer; is_safe} ->
      failwith "Boxed integer operation not implemented"
  | Pbintcomp (boxed_integer, integer_comparison) ->
      failwith "Boxed integer operation not implemented"
  (* Operations on Bigarrays: (unsafe, #dimensions, kind, layout) *)
  | Pbigarrayref (unsafe, dimension, kind, layout)
  | Pbigarrayset (unsafe, dimension, kind, layout) ->
      failwith "Big array operation not implemented"
  | Pbigarraydim i ->
      failwith "Big array operation not implemented"
  (* load/set 16,32,64 bits from a string: (unsafe)*)
  | Pstring_load_16 unsafe
  | Pstring_load_32 unsafe
  | Pstring_load_64 unsafe
  | Pbytes_load_16 unsafe
  | Pbytes_load_32 unsafe
  | Pbytes_load_64 unsafe
  | Pbytes_set_16 unsafe
  | Pbytes_set_32 unsafe
  | Pbytes_set_64 unsafe ->
      failwith "String bit operation not implemented"
  (* load/set 16,32,64 bits from a
     (char, int8_unsigned_elt, c_layout) Bigarray.Array1.t : (unsafe) *)
  | Pbigstring_load_16 unsafe
  | Pbigstring_load_32 unsafe
  | Pbigstring_load_64 unsafe
  | Pbigstring_set_16 unsafe
  | Pbigstring_set_32 unsafe
  | Pbigstring_set_64 unsafe ->
      failwith "Bit operation not implemented"
  (* Compile time constants *)
  | Pctconst
      ( Big_endian
      | Word_size
      | Int_size
      | Max_wosize
      | Ostype_unix
      | Ostype_win32
      | Ostype_cygwin
      | Backend_type ) ->
      failwith "Compile tiem constant not implemented"
  (* byte swap *)
  | Pbswap16 ->
      failwith "bswap16"
  | Pbbswap boxed_integer ->
      failwith "bbswap"
  (* Integer to external pointer *)
  | Pint_as_pointer ->
      failwith "Pint_as_pointer"
  (* Atomic operations *)
  | Patomic_load {immediate_or_pointer= Immediate | Pointer} ->
      failwith "atomic_load"
  | Patomic_exchange | Patomic_cas | Patomic_fetch_add ->
      failwith "Atomic operation not implemented"
  (* Inhibition of optimisation *)
  | Popaque ->
      failwith "opaque"
  (* Polling for interrupts *)
  | Ppoll ->
      failwith "poll"
  (* nop instruction for debugging *)
  | Pnop ->
      failwith "nop"

(* Entry point for Lambda->MCore compilation *)
and lambda2mcore (lam : Lambda.program) =
  let rec lambda2mcore' m = function
    | Lvar ident ->
        mk_var_ident m ident
    | Lconst c ->
        compile_structured_constant c
    | Lapply {ap_func= f; ap_args= args} ->
        let rec mk_app = function
          | [] ->
              failwith "Application without a lhs"
          | [a] ->
              lambda2mcore' m a
          | a :: args ->
              TmApp (NoInfo, mk_app args, lambda2mcore' m a)
        in
        mk_app (List.rev (f :: args))
    | Lfunction {params; body} ->
        let rec mk_lambda params body =
          match params with
          | [] ->
              lambda2mcore' m body
          | (ident, _vkind) :: ps ->
              mk_lam (mk_ident m ident) (mk_lambda ps body)
        in
        mk_lambda params body
    | Llet
        (* Module definition *)
        ( _
        , _
        , ident
        , Levent (lam, {lev_kind= Lev_module_definition mident})
        , inexpr ) ->
        let b = lambda2mcore' (m ^ Ident.name ident ^ ".") lam in
        let i = lambda2mcore' m inexpr in
        (* NOTE(linnea, 2021-03-17): Inserts a dummy "<modulename> = ()" because
           the module name is referred to in makeblock *)
        mk_let (mk_ident m ident) mcore_noop (mk_seq b i)
    | Llet (_kind, _value_kind, ident, body, inexpr) ->
        mk_let (mk_ident m ident) (lambda2mcore' m body)
          (lambda2mcore' m inexpr)
    | Lletrec (binds, inexpr) ->
        TmRecLets
          ( NoInfo
          , List.map
              (fun (ident, body) ->
                ( NoInfo
                , mk_ident m ident
                , Symb.Helpers.nosym
                , TyUnknown NoInfo
                , lambda2mcore' m body ) )
              binds
          , lambda2mcore' m inexpr )
    | Lprim (p, lamlist, loc) ->
        let args = List.map (lambda2mcore' m) lamlist in
        compile_primitive p args
    | Lifthenelse (cnd, thn, els) ->
        TmMatch
          ( NoInfo
          , lambda2mcore' m cnd
          , PatBool (NoInfo, true)
          , lambda2mcore' m thn
          , lambda2mcore' m els )
    | Lswitch (arg, sw, _loc) ->
        if Option.is_some sw.sw_failaction then
          failwith "switch failaction not supported"
        else if sw.sw_numblocks > 0 then (
          assert (sw.sw_numconsts = 0) ;
          let block_names =
            match sw.sw_names with
            | Some {blocks} ->
                blocks
            | None ->
                failwith "Name missing for block"
          in
          assert (sw.sw_numblocks == Array.length block_names) ;
          let rec mk_tag_matches target = function
            | [] ->
                TmNever NoInfo
            | ((_tag, branch), name) :: xs ->
                let target_str =
                  match target with
                  | TmVar (_, us, _) ->
                      us
                  | _ ->
                      failwith ("Expected TmVar, got " ^ pprint_mcore target)
                in
                TmMatch
                  ( NoInfo
                  , target
                  , pcon_ name (pnamed_ target_str)
                  , lambda2mcore' m branch
                  , mk_tag_matches target xs )
          in
          mk_tag_matches (lambda2mcore' m arg)
            (List.map2
               (fun x y -> (x, y))
               sw.sw_blocks
               (Array.to_list block_names) ) )
        else
          let rec mk_int_matches var = function
            | [] ->
                TmNever NoInfo
            | (n, branch) :: xs ->
                TmMatch
                  ( NoInfo
                  , var
                  , pint_ n
                  , lambda2mcore' m branch
                  , mk_int_matches var xs )
          in
          mk_int_matches (lambda2mcore' m arg) sw.sw_consts
    (* NOTE(Linnea, 2021-03-09): Many lambda program are wrapped in a sequence
       operator with an empty makeblock node as rhs. To get nicer output we
       simply ignore this empty block (otherwise the program would end with
       "...; ()") *)
    | Lsequence (l1, Lprim (Pmakeblock (_, _, _), [], _)) ->
        lambda2mcore' m l1
    | Lsequence (l1, l2) ->
        mk_seq (lambda2mcore' m l1) (lambda2mcore' m l2)
    | Lstaticraise (n, []) -> (
      match get_error_handler n with
      | Some h ->
          h
      | None ->
          TmApp (NoInfo, TmConst (NoInfo, Cexit), TmConst (NoInfo, CInt n)) )
    | Lstaticraise (_, _) ->
        failwith "staticraise"
    | Lstaticcatch (body, (i, _vars), handler) ->
        add_error_handler i (lambda2mcore' m handler) ;
        lambda2mcore' m body
    | Levent _ ->
        failwith "event"
    | Lstringswitch _ ->
        failwith "stringswitch"
    | Ltrywith _ ->
        failwith "trywith"
    | Lwhile _ ->
        failwith "while"
    | Lfor _ ->
        failwith "for"
    | Lassign _ ->
        failwith "assign"
    | Lsend _ ->
        failwith "send"
    | Lifused _ ->
        failwith "ifused"
  in
  lambda2mcore' "" lam.code

let ocaml_out_file f =
  match Filename.chop_suffix_opt ".mc" f with
  | Some s ->
      s
  | None ->
      filename ^ ".out"

let to_output str =
  let outfile = !output_file in
  if outfile = "stdout" then print_endline str
  else
    let oc = open_out outfile in
    fprintf oc "%s\n" str ; close_out oc

let mcore_compile str =
  if !enable_compile_mcore then
    match Sys.getenv_opt "MCORE_STDLIB" with
    | Some mcore_stdlib ->
        (* Write output to temporary file *)
        let ocaml_out_prefix =
          if !output_file = "stdout" then "prog"
          else ocaml_out_file !output_file
        in
        let oc = open_out (ocaml_out_prefix ^ ".mc") in
        fprintf oc "%s\n" str ;
        close_out oc ;
        Sys.command
          (sprintf "mi %s/../src/main/mi.mc -- compile %s.mc" mcore_stdlib
             ocaml_out_prefix )
        |> ignore
    | None ->
        failwith "Source-to-source compilation requires MCORE_STDLIB to be set"
  else ()

let ocaml2mcore filename =
  Compmisc.init_path () ;
  Matching.names_from_construct_pattern :=
    Matching_polyfill.names_from_construct_pattern ;
  let mcore_prog =
    filename |> parse_file |> typecheck |> typed2lambda |> lambda2mcore
    |> pprint_mcore
  in
  let includes = String.concat "\n" (SS.elements !includes_ref) in
  let full_prog =
    String.concat "\n"
      [includes; get_typedecl (); prelude (); "mexpr"; mcore_prog]
  in
  to_output full_prog ; mcore_compile full_prog
