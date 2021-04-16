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

let int2ustring = Boot.Ustring.Op.ustring_of_int

let pprint_mcore tm = to_utf8 (ustring_of_tm tm)

(* Name mangling *)
let ident2varstr m ident =
  match m with "" -> Ident.unique_name ident | _ -> Ident.name ident

(* Module strings are already unique *)
let ident2modstr ident = Ident.name ident

let append_module_ident m ident = m ^ ident2modstr ident ^ "."

let mangle m s = m ^ s

let ident2mangled m ident =
  ident |> ident2varstr m |> mangle m |> Boot.Ustring.from_utf8

module AstHelpers = struct
  let mcore_noop = tmUnit

  let mk_string str =
    TmSeq
      ( NoInfo
      , Mseq.Helpers.map
          (fun x -> TmConst (NoInfo, CChar x))
          (from_latin1 str |> Mseq.Helpers.of_ustring) )

  let mk_let ident body inexpr =
    TmLet (NoInfo, ident, Symb.Helpers.nosym, TyUnknown NoInfo, body, inexpr)

  let lam_ ident body =
    TmLam (NoInfo, ident, Symb.Helpers.nosym, TyUnknown NoInfo, body)

  let mk_seq body inexpr = mk_let (from_utf8 "") body inexpr

  let mk_ite cnd thn els =
    TmMatch (NoInfo, cnd, PatBool (NoInfo, true), thn, els)

  let mk_var m s = TmVar (NoInfo, from_utf8 (mangle m s), Symb.Helpers.nosym)

  let mk_var_ident m ident = mk_var m (ident2varstr m ident)

  let record_from_list binds =
    List.fold_left (fun a (k, v) -> Record.add k v a) Record.empty binds

  let const_ c = TmConst (NoInfo, c)

  let app_ a b = TmApp (NoInfo, a, b)

  let app2_ a b c = app_ (app_ a b) c

  let conapp_ a b = TmConApp (NoInfo, a, Symb.Helpers.nosym, b)

  let record_ binds = TmRecord (NoInfo, record_from_list binds)

  let tyrecord_ binds = TyRecord (NoInfo, record_from_list binds)

  let precord_ binds = PatRecord (NoInfo, record_from_list binds)

  let tyarrow_ l h = TyArrow (NoInfo, l, h)

  let tyvar_ s = TyVar (NoInfo, from_utf8 s, Symb.Helpers.nosym)

  let tyunknown_ = TyUnknown NoInfo

  let pcon_ c p = PatCon (NoInfo, from_utf8 c, Symb.Helpers.nosym, p)

  let pnamed_ s = PatNamed (NoInfo, NameStr (s, Symb.Helpers.nosym))

  let pwild_ = PatNamed (NoInfo, NameWildcard)

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

  let seq_ tms = TmSeq (NoInfo, Mseq.Helpers.of_list tms)
end

open AstHelpers

let get_args2 args =
  match args with
  | [a1; a2] ->
      (a1, a2)
  | _ ->
      failwith "Expected two arguments"

(* Compile arrays into tensors *)
module Array2Tensor = struct
  (* Translation of Array.init *)
  let init args =
    let a1, a2 = get_args2 args in
    let shape = seq_ [a1] in
    let f =
      lam_ (from_utf8 "x")
        (app_ a2 (app2_ (const_ (Cget None)) (mk_var "" "x") (int_ 0)))
    in
    app2_ (const_ (CtensorCreate None)) shape f

  (* Translation of Array.make *)
  let make args =
    let a1, a2 = get_args2 args in
    let shape = seq_ [a1] in
    let f = lam_ (from_utf8 "") a2 in
    app2_ (const_ (CtensorCreate None)) shape f

  (* Translation of Array.iter *)
  let iter args =
    let a1, a2 = get_args2 args in
    (* lam x. x -> lam _. lam x. x *)
    let f =
      lam_ (from_utf8 "")
        (lam_ (from_utf8 "x")
           (app_ a1
              (app2_ (const_ (CtensorGetExn None)) (mk_var "" "x") (seq_ [])) ) )
    in
    app2_ (const_ (CtensorIteri None)) f a2
end

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

(* Access in modules, either external or in-file defined *)
(* Arrays are handled in compile_lambda *)
let rec compile_module_access = function
  (* Standard library I/O and strings *)
  | "Stdlib.print_endline" ->
      add_include "common.mc" ; mk_var "" "printLn"
  | "Stdlib.print_int" ->
      lam_ (from_utf8 "x")
        (app_ (const_ Cprint)
           (app_
              (compile_module_access "Stdlib.string_of_int")
              (mk_var "" "x") ) )
  | "Stdlib.read_line" ->
      const_ CreadLine
  | "Stdlib.string_of_int" ->
      add_include "string.mc" ; mk_var "" "int2string"
  | "Stdlib.^" ->
      TmConst (NoInfo, Cconcat None)
  | "Stdlib.Char.escaped" ->
      add_include "char.mc" ;
      Boot.Parserutils.parse_mexpr_string
        (from_utf8 "lam c. escapeChar (int2char c)")
  | "Stdlib.String.concat" ->
      add_include "string.mc" ; mk_var "" "strJoin"
  (* Standard library lists *)
  | "Stdlib.List.init" ->
      const_ (Ccreate None)
  | "Stdlib.List.map" ->
      add_include "seq.mc" ; mk_var "" "map"
  | "Stdlib.List.partition" ->
      add_include "seq.mc" ; mk_var "" "partition"
  | "Stdlib.@" ->
      const_ (Cconcat None)
  | "Stdlib.List.cons" ->
      const_ (Ccons None)
  | "Stdlib.List.length" ->
      const_ Clength
  | "Stdlib.List.iter" ->
      add_include "seq.mc" ; mk_var "" "iter"
  (* Standard library random numbers *)
  | "Stdlib.Random.init" ->
      const_ CrandSetSeed
  | "Stdlib.Random.int" ->
      app_ (const_ (CrandIntU None)) (int_ 0)
  (* In-file defined modules *)
  | s when module_is_defined (get_module s) ->
      mk_var "" s
  | s ->
      (* TODO(Linnea, 2021-03-16): External dependency, should be marked in some
         way. *)
      mk_var "" s

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
  | Const_pointer (0, Ptr_unit) ->
      tmUnit
  | Const_pointer (0, Ptr_nil) ->
      TmSeq (NoInfo, Mseq.empty)
  | Const_pointer (0, Ptr_con name) ->
      add_tagged_type name [] ;
      TmConApp (NoInfo, from_utf8 name, Symb.Helpers.nosym, tmUnit)
  | Const_pointer (0, Ptr_bool) ->
      false_
  | Const_pointer (1, Ptr_bool) ->
      true_
  | Const_pointer _ ->
      failwith "const_pointer"
  | Const_block (tag, str_const_list, (Tag_record | Tag_tuple)) ->
      let consts = List.map compile_structured_constant str_const_list in
      mk_tuple consts
  | Const_block (tag, str_const_list, Tag_con "::") as c ->
      let rec collect_list acc const =
        match const with
        | Const_pointer (0, Ptr_nil) ->
            acc
        | Const_block (_, cs, Tag_con "::") -> (
          match cs with
          | [elem; const] ->
              collect_list (compile_structured_constant elem :: acc) const
          | _ ->
              failwith "Expected two arguments to '::'" )
        | _ ->
            failwith "Expected cons or empty list"
      in
      let elems = collect_list [] c in
      TmSeq (NoInfo, Mseq.Helpers.of_list elems)
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
  | Pmakeblock (_tag, _mut, _shape, Tag_con "::") ->
      mk_constapp2 (Ccons None) args
  | Pmakeblock (_tag, _mut, _shape, Tag_con s) ->
      conapp_ (from_utf8 s) (mk_tuple args)
  | Pmakeblock (_tag, _mut, _shape, _) ->
      (* TODO(Linnea, 2021-04-08): handle other tags *)
      mk_tuple args
  | Pfield (n, Pointer, Immutable, Fmodule s) ->
      compile_module_access s
  | Pfield (n, (Pointer | Immediate), Immutable, (Frecord _ | Ftuple)) -> (
    match args with
    | [r] ->
        mk_tuple_proj n r
    | _ ->
        failwith "Expected one argument to Pfield immediate" )
  | Pfield (n, Pointer, Immutable, Fcon _) -> (
    match args with
    | [r] ->
        mk_tuple_proj n r
    | _ ->
        failwith "Expected one argument to Pfield immediate" )
  | Pfield (n, Pointer, Immutable, Fcons) -> (
    match args with
    | [r] -> (
      match n with
      | 0 ->
          add_include "seq.mc" ;
          TmApp (NoInfo, mk_var "" "head", r)
      | 1 ->
          add_include "seq.mc" ;
          TmApp (NoInfo, mk_var "" "tail", r)
      | _ ->
          failwith (sprintf "Out of bounds access in cons: %d" n) )
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
        add_include "string.mc" ;
        TmApp (NoInfo, mk_var "" "string2int", a)
    | _ ->
        failwith "Expected one argument to caml_int_of_string" )
  | Pccall {prim_name= "caml_lessthan"} ->
      (* NOTE(Linnea, 2021-04-08): Assume integer <, and hope that it fails
         spectacularly if not true *)
      mk_constapp2 (Clti None) args
  | Pccall {prim_name= "caml_make_vect"} ->
      Array2Tensor.make args
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
    | Lfunction {params; body} ->
        let rec mk_lambda params body =
          match params with
          | [] ->
              lambda2mcore' m body
          | (ident, _vkind) :: ps ->
              lam_ (ident2mangled m ident) (mk_lambda ps body)
        in
        mk_lambda params body
    | Llet
        (* Module definition *)
        ( _
        , _
        , ident
        , Levent (lam, {lev_kind= Lev_module_definition mident})
        , inexpr ) ->
        let b = lambda2mcore' (append_module_ident m ident) lam in
        let i = lambda2mcore' m inexpr in
        (* NOTE(linnea, 2021-03-17): Inserts a dummy "<modulename> = ()" because
           the module name is referred to in makeblock *)
        mk_let (ident2mangled m ident) mcore_noop (mk_seq b i)
    | Llet (_kind, _value_kind, ident, body, inexpr) ->
        mk_let (ident2mangled m ident) (lambda2mcore' m body)
          (lambda2mcore' m inexpr)
    | Lletrec (binds, inexpr) ->
        TmRecLets
          ( NoInfo
          , List.map
              (fun (ident, body) ->
                ( NoInfo
                , ident2mangled m ident
                , Symb.Helpers.nosym
                , TyUnknown NoInfo
                , lambda2mcore' m body ) )
              binds
          , lambda2mcore' m inexpr )
    | Lprim (p, lamlist, loc) ->
        let args = List.map (lambda2mcore' m) lamlist in
        compile_primitive p args
    | Lifthenelse (cnd, thn, els, (Match_nil | Match_con "::")) ->
        TmMatch
          ( NoInfo
          , lambda2mcore' m cnd
          , PatSeqTot (NoInfo, Mseq.empty)
          , lambda2mcore' m els
          , lambda2mcore' m thn )
    | Lifthenelse (cnd, thn, els, Match_con name) ->
        let thn_branch = lambda2mcore' m els in
        let els_branch = lambda2mcore' m thn in
        let cnd = lambda2mcore' m cnd in
        let wrap_els_branch els_branch =
          (* NOTE(Linnea, 2021-04-06): This covers the case of matching on None /
             Some _ constructors but is not a fully general solution for handling
             empty constructors. When we see that the else branch contains a field
             access of a constructor, we wrap it into a match on the constructor
             name. *)
          let con_name =
            match thn with
            | Llet (_, _, _, Lprim (Pfield (_, _, _, Fcon name), _, _), _) ->
                Some name
            | _ ->
                None
          in
          match con_name with
          | Some name ->
              let cnd_str =
                match cnd with
                | TmVar (_, us, _) ->
                    us
                | _ ->
                    failwith ("Expected variable, got " ^ pprint_mcore cnd)
              in
              TmMatch
                ( NoInfo
                , cnd
                , pcon_ name (pnamed_ cnd_str)
                , els_branch
                , TmNever NoInfo )
          | None ->
              els_branch
        in
        TmMatch
          ( NoInfo
          , cnd
          , pcon_ name pwild_
          , thn_branch
          , wrap_els_branch els_branch )
    | Lifthenelse (cnd, thn, els, _) ->
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
                      failwith ("Expected variable, got " ^ pprint_mcore target)
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
    | Lsequence (l1, Lprim (Pmakeblock _, [], _)) ->
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
    (* Application of array functions *)
    | Lapply
        { ap_func= Lprim (Pfield (_, _, _, Fmodule "Stdlib.Array.init"), _, _)
        ; ap_args= args } ->
        Array2Tensor.init (List.map (lambda2mcore' m) args)
    | Lapply
        { ap_func= Lprim (Pfield (_, _, _, Fmodule "Stdlib.Array.iter"), _, _)
        ; ap_args= args } ->
        Array2Tensor.iter (List.map (lambda2mcore' m) args)
    (* General application *)
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
    String.concat "\n" [includes; get_typedecl (); "mexpr"; mcore_prog]
  in
  to_output full_prog ; mcore_compile full_prog
