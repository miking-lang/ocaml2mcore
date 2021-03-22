open Compile

(* Add support for source-to-source compilation *)

(* Main menu *)
let usage_msg = "Usage: ocaml2mcore <filename>\n\nOptions:"

let main =
  (* Keyword arguments *)
  let speclist =
    [ ( "--debug-parsed"
      , Arg.Set enable_debug_parsed
      , " Enables output of parsing." )
    ; ( "--debug-typed"
      , Arg.Set enable_debug_typed
      , " Enables output after type check." )
    ; ( "--debug-lambda"
      , Arg.Set enable_debug_lambda
      , " Enables output after conversion to lambda." )
    ; ( "--output-file"
      , Arg.Set_string output_file
      , " Write MCore output to this file (defaults to stdout if not given)."
      )
    ; ( "-o"
      , Arg.Set_string output_file
      , " Write MCore output to this file (defaults to stdout if not given)."
      ) ]
  in
  (* Align the command line description list *)
  let speclist = Arg.align speclist in
  (* When non-option argument is encountered, simply save it to lst *)
  let lst = ref [] in
  let anon_fun arg = lst := arg :: !lst in
  (* Parse command line *)
  ( try Arg.parse speclist anon_fun usage_msg
    with Arg.Bad m | Arg.Help m -> print_endline m ; exit 0 ) ;
  if List.length !lst = 0 then Arg.usage speclist usage_msg
  else
    match !lst with
    (* Convert OCaml program to MCore *)
    | [filename] ->
        Compile.ocaml2mcore filename
    (* Show the menu *)
    | _ ->
        Arg.usage speclist usage_msg
