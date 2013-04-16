(* PLEASE DO NOT CHANGE THIS FILE *)

open Debug.Basic
open DPL
module C = DPLc


(* let set_source_file (arg:string) =  *)
(*   source_files := arg :: !source_files *)

(* let process_cmd_line () =  *)
(*   Arg.parse option_flag set_source_file usage *)

let usage = "usage: " ^ Sys.argv.(0) ^ " [options] <filename>"

(* let triple_to_type_decl (t: (string * string list * (string * dPL_type list) list)): id * dPL_type_decl =  *)
(*   match t with *)
(*     | (id0,tvars,data) -> *)
(*          (id0, {ty_def_name = id0; ty_def_param = tvars; ty_def_data = data }) *)

(* let add_type_decl_to_env (t: (string * string list * (string * dPL_type list) list) list) =       *)
(*   let rec helper lst = *)
(*     match lst with *)
(*       |  x::xs ->  *)
(*              let (id,td) = triple_to_type_decl x in *)
(*              ty_dict#add id td; helper xs  *)
(*       | [] -> () in *)
(*   helper t *)

(* calling dPL parser *)

let parse_file (filename:string) : string * dPL_nexpr =
  let (s,e) = DPL_preprocess.parse_file filename in
  (s,e)

let pre_proc e = DPL_preprocess.pre_proc e

(* set up for command argument
   using Sys and Arg modules *)

(* main program *)
let main =
  (* Read the arguments of command *)
  Arg.parse [] (fun s -> file := s) usage; 
  if String.length !file == 0 then print_endline usage else 
    let _ = print_endline "LOADING dPL program .." in
    let (s,p) = parse_file !file in
    (* let _ = add_type_decl_to_env tdl in *)
    let _ = print_endline ("  "^s) in
    let _ = print_endline (" AS ==> ") in
    let _ = print_endline (("\t Type Declarations: ") ^
        (( Environ.string_of DPL.string_of_dPL_type_decl ) ( ty_dict # get_env) )) in
    let _ = print_endline (("\t Expression: ") ^ (string_of_ndPL p)) in
    let _ = print_endline "PRE-PROCESSING .." in
    try
      let p2 = pre_proc p in
      print_endline (" ==> pre-proc : "^(string_of_dPL p2))
    with 
      | _ ->   print_endline (" ==> pre-processing error detected " ^ s)
