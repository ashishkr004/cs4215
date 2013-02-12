open EPL

(* translating command *)
let trans_cmd op =
  match op with
    | "+" -> PLUS
    | "-" -> MINUS
    | "*" -> TIMES
    | "/" -> DIV
    | "\\" -> NOT
    | "~" -> NEG
    | "|" -> OR  
    | "&" -> AND 
    | "<" -> LT 
    | ">" -> GT 
    | "=" -> EQ
    | _ -> failwith ("no such operator "^op)

(* compiling to eVML instrs *)
let compile (e:ePL_expr) : eVML_inst list =
  let rec helper e =
    match e with
      | IntConst i -> [LDCI i]
      | BoolConst b -> 
            failwith "TO BE IMPLEMENTED"
      | UnaryPrimApp (op,arg) ->
            let s = helper arg in
            s@[trans_cmd op]
      | BinaryPrimApp (op,arg1,arg2) ->
            failwith "TO BE IMPLEMENTED"
  in
  (helper e)@[DONE]

(* output evm bytecode to a file *)
let generate_bytecode(elist: eVML_inst list) (filename:string) = 
  let out_channel = open_out_bin filename in
  output_value out_channel (Array.of_list elist);
  close_out out_channel


(* test driver for writing bytecode file *)
let testGenerateBytecode e filename =
  let s = (string_of_ePL e) in
  let c = compile e in
  generate_bytecode c filename;
  print_endline ("ePL : "^s);
  print_endline ("Bytecode Generated in "^filename)

(* calling ePL parser *)
let parse_file (filename:string) : (string * ePL_expr) =
  EPL_parser.parse_file filename
 
(* set up for command argument
   using Sys and Arg modules *)
let usage = "usage: " ^ Sys.argv.(0) ^ " <filename>"
let file = ref "" 

(* check that s is of form <fname>.epl *)
(* return <fname> as result *)
(* throw an execption otherwise *)
(* use OCaml methods of String module *)
let extract_filename (s:string) : string =
  let v = String.length s in
  if v<5 then
    failwith "filename at least one char"
  else 
    let fn = String.sub s 0 (v-4) in
    let extn = String.sub s (v-4) 4 in
    if extn = ".epl" then fn
    else failwith "filename must have .epl extn"
;;

(* test driver for extract_argument *)
let test_extract_filename () =
  print_endline (extract_filename "hello.epl");
  (* should return "hello" *)
  print_endline (extract_filename ".epl");
  (* should return Failure("filename at least one char") *)
  print_endline (extract_filename "hello.ep")
  (* should return Failure("filename must have .epl extn") *)
;;

(* test_extr_filename ();; *)

(* main program *)
let main =
  (* Read the arguments of command *)
  Arg.parse [] (fun s -> file := s) usage; 
  if String.length !file == 0 then print_endline usage else 
  let _ = print_endline "Loading ePL program .." in
  let (s,p) = parse_file !file in
  let _ = print_endline ("  "^s) in
  let _ = print_endline ("  as "^(string_of_ePL p)) in
  (* let _ = print_endline "Type checking program .." in *)
  (* let _ = testType p in *)
  let r = compile p in
  let fn = extract_filename !file in
  let bytefn = fn^".evm" in
  let _ = print_endline ("Compiling ==> "^bytefn) in
  let _ = generate_bytecode r bytefn in
  print_endline (string_of_eVML_list r)
