open EPL

(* read evm bytecode from a file *)
let read_bytecode (filename:string) : eVML_inst array = 
  let in_channel = open_in_bin filename in
  let elist = input_value in_channel in
  let _ = close_in in_channel in elist

(* test driver for reading bytecode file *)
let testReadBytecode filename =
  let earray = read_bytecode filename in
  let elist = Array.to_list earray in
  print_endline ("Bytecode Read from "^filename);
  print_endline ("eVML : "^(string_of_eVML_list elist))

(* binary operator over integer values *)
let binary_operate (c:eVML_inst) (a1:int) (a2:int) : int =
  match c with
    | PLUS -> a1+a2
    | MINUS -> a1+a2
    | TIMES -> a1*a2
    | DIV -> a1/a2
    | OR -> 
          failwith "TO BE IMPLEMENTED"
    | AND -> 
          failwith "TO BE IMPLEMENTED"
    | EQ -> 
          failwith "TO BE IMPLEMENTED"
    | LT -> 
          failwith "TO BE IMPLEMENTED"
    | GT -> 
          failwith "TO BE IMPLEMENTED"
    | _ -> failwith "not possible"

(* unary operator over integer values *)
let unary_operate (c:eVML_inst) (a1:int) : int =
  match c with
    | NEG -> -a1
    | NOT -> 
          failwith "TO BE IMPLEMENTED"
    | _ -> failwith "not possible"

(* perform operation over a stack *)
(* see mutable OCaml Stack module *)
let proc_inst (stk:int Stack.t) (c:eVML_inst) : unit =
  match c with
    | LDCI i -> Stack.push i stk
    | LDCB i -> Stack.push i stk
    | PLUS | MINUS | TIMES | DIV | AND | OR 
    | GT | LT | EQ
          -> 
          failwith "TO BE IMPLEMENTED"
    | NEG | NOT -> 
          let a1 = Stack.pop stk in
          Stack.push (unary_operate c a1) stk
    | DONE -> ()

(* evm virtual machine *)
(* a value is returned on execution *)
let eVML_mc (instArr:eVML_inst array) : int =
  let stk = Stack.create () in
  let rec execute pc =
    let c = Array.get instArr pc in
    match c with
      | DONE -> Stack.pop stk
      | _ -> (proc_inst stk c; execute (pc+1))
  in execute 0 

(* evm virtual machine implemented as a class *)
class eVML (instSeq:eVML_inst list) =
   object (mc)
     val mutable pc = 0
     val stk = Stack.create ()
     val instArr = Array.of_list instSeq
     (* method to check if next inst is DONE *)
     method finish () : bool = 
       let c = Array.get instArr pc in
       c == DONE
     (* method to execute one step *)
     method oneStep () : unit =
       let c = Array.get instArr pc in
       proc_inst stk c;
       pc <- pc + 1
     (* method to execute till DONE encountered *)
     (* and return the value on top of its stack *)
     method execute () : int =
       if mc # finish () then Stack.pop stk
       else begin mc # oneStep(); mc # execute () end
   end;;


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
  let bytefn = !file^".evm" in
  let _ = print_endline ("Loading eVM code from .."^bytefn) in
  let instr = read_bytecode bytefn in
  let _ = print_endline ("Loaded "^(string_of_eVML_list (Array.to_list instr))) in
  let r = eVML_mc instr in
  print_endline ("Executing ==> "^(string_of_int r))
