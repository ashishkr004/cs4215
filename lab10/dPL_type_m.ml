(* PLEASE DO NOT CHANGE THIS FILE *)

open DPL_type
open Debug.Basic
open DPLc
module S = DPL


(* let set_source_file (arg:string) =  *)
(*   source_files := arg :: !source_files *)

(* let process_cmd_line () =  *)
(*   Arg.parse option_flag set_source_file usage *)

let usage = "usage: " ^ Sys.argv.(0) ^ " [options] <filename>"

let triple_to_type_decl (t: (string * string list * (string * S.dPL_type list) list)): S.id * S.dPL_type_decl = 
  match t with
    | (id0,tvars,data) ->
         (id0, {S.ty_def_name = id0; S.ty_def_param = tvars; S.ty_def_data = data })

let add_type_decl_to_env (t: (string * string list * (string * S.dPL_type list) list) list) =      
  let rec helper lst =
    match lst with
      |  x::xs -> 
             let (id,td) = triple_to_type_decl x in
             S.ty_dict#add id td; helper xs 
      | [] -> () in
  helper t

(* calling dPL parser *)
let parse_file (filename:string) : (string * ('a list * S.dPL_expr)) =
  DPL_parser.parse_file filename

(* set up for command argument
   using Sys and Arg modules *)

(* main program *)
let main =
  (* Read the arguments of command *)
  Arg.parse [] (fun s -> file := s) usage; 
  if String.length !file == 0 then print_endline usage else 
    let _ = print_endline "LOADING dPL program .." in
    let (s,(tdl,p)) = parse_file !file in
    let _ = add_type_decl_to_env tdl in
    let _ = print_endline ("  "^s) in
    let _ = print_endline (" AS ==> ") in
    let tdl = List.map (fun (s,args,ptns) -> 
        { S.ty_def_name = s; S.ty_def_param=args; S.ty_def_data=ptns} ) tdl in
    let _ = print_endline (("\t type declarations: ") ^ 
        (pr_list S.string_of_dPL_type_decl tdl)) in
    let _ = print_endline (("\t expression: ") ^ (S.string_of_dPL p)) in
    let _ = print_endline "TYPE CHECKING program .." in
    try
      let ((subs,t),np) = type_infer [] p in
      (* | None -> print_endline " ==> type error detected" *)
      print_endline (" ==> inferred type "^(S.string_of_dPL_type t));
      print_endline (" ==> subst "^(pr_subs subs));
      print_endline (" ==> typed expr "^(S.string_of_dPL np));
      let _ = print_string "TRANSFORMING ==> " in
      let np = trans_exp np in
      let _ = print_endline (string_of_dPL np) in
      ()
    with 
      | Type_error s ->   print_endline (" ==> type error detected " ^ s)
      (* | e -> print_endline " ==> unknown type error" *)
