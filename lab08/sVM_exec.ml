open SVM
open SPLc
open Debug.Basic

(* read evm bytecode from a file *)
let read_bytecode (filename:string) : sVML_inst_mc array = 
  let in_channel = open_in_bin filename in
  let elist = input_value in_channel in
  let _ = close_in in_channel in elist

let get_ints v1 v2 =
  match v1,v2 with
    | VInt v1,VInt v2 -> v1,v2
    | _ -> failwith "type_error : impossible (expecting ints)"

let get_bools v1 v2 =
  match v1,v2 with
    | VBool v1,VBool v2 -> v1,v2
    | _ -> failwith "type_error : impossible (expecting bools)"

let get_bool v1 =
  match v1 with
    | VBool v1 -> v1
    | _ -> failwith "type_error : impossible (expecting bool)"

let get_int v1 =
  match v1 with
    | VInt v1 -> v1
    | _ -> failwith "type_error : impossible (expecting int)"

(* binary operator over integer values *)
let binary_operate (c:sVML_inst_mc) (a1:value_mc) (a2:value_mc) : value_mc =
  match c with
    | PLUS -> let (a1,a2) = get_ints a1 a2 in VInt(a1+a2)
    | MINUS -> let (a1,a2) = get_ints a1 a2 in VInt(a1-a2) 
    | TIMES -> let (a1,a2) = get_ints a1 a2 in VInt(a1*a2)
    | DIV -> 
          let (a1,a2) = get_ints a1 a2 in 
          if a2=0 then BOT
          else VInt(a1/a2)
    | OR ->  
          let (a1,a2) = get_bools a1 a2 in VBool (a1||a2)
    | AND -> 
          let (a1,a2) = get_bools a1 a2 in VBool (a1&&a2)
    | EQ -> 
          let (a1,a2) = get_ints a1 a2 in VBool (a1=a2)
    | LT -> 
          let (a1,a2) = get_ints a1 a2 in VBool (a1<a2)
    | GT -> 
          let (a1,a2) = get_ints a1 a2 in VBool (a1>a2)
    | _ -> failwith "not possible"

(* unary operator over integer values *)
let unary_operate (c:sVML_inst_mc) (a1:value_mc) : value_mc =
  match c with
    | NEG -> 
          let a1 = get_int a1 in VInt (-a1)
    | NOT -> 
          let a1 = get_bool a1 in VBool (not(a1))
    | _ -> failwith "not possible"

(* perform operation over a stack *)
(* see mutable OCaml Stack module *)
let proc_inst (stk:value_mc Stack.t) (c:sVML_inst_mc) : unit =
  match c with
    | LDCI i -> Stack.push (VInt i) stk
    | LDCB b -> Stack.push (VBool b) stk
    | PLUS | MINUS | TIMES | AND | OR 
    | GT | LT | EQ
          -> 
          let a2 = Stack.pop stk in
          let a1 = Stack.pop stk in
          Stack.push (binary_operate c a1 a2) stk
    | NEG | NOT -> 
          let a1 = Stack.pop stk in
          Stack.push (unary_operate c a1) stk
    | DIV ->
          begin
          let a2 = Stack.pop stk in
          match a2 with
            | VInt 0 -> 
                  Stack.push BOT stk;
                  failwith "Divide by Zero"
            | _ -> 
                  let a1 = Stack.pop stk in
                  Stack.push (binary_operate c a1 a2) stk
          end
    | _ -> ()


let pop_2_venv stk e m r =
  let rec aux m =
    if m=r then ()
    else 
      let v = Stack.pop stk in
      let _ = Array.set e m v in
      aux (m+1)
  in aux m 

(* evm virtual machine implemented as a class *)
class sVML (instSeq:sVML_inst_mc list) =
object (mc)
  val mutable pc = 0
  val stk = Stack.create ()
  val mutable venv = Array.make 0 BOT
  val rs = Stack.create ()
  val instArr = Array.of_list instSeq
    (* method to check if next inst is DONE *)
  method finish : bool = 
    let c = Array.get instArr pc in
    c == DONE
        (* method to execute one step *)
  method oneStep : unit =
    let c = Array.get instArr pc in
    let pr = string_of_int in
    Debug.ninfo_hprint (add_str "inst" string_of_sVML_list) [c];
    Debug.ninfo_hprint (add_str "pc,venv" (pr_pair pr pr)) (pc,Array.length venv);
    match c with
      | DIV ->
            let a2 = Stack.pop stk in
            let a1 = Stack.pop stk in
            let (a1,a2) = get_ints a1 a2 in 
            if a2=0 then 
              begin
                Stack.push BOT stk;
                failwith "Divide-by-Zero"
              end
            else 
              begin
                Stack.push (VInt(a1/a2)) stk;
                pc <- pc+1;
              end
      | GOTO r -> pc <- r
      | JOF r -> 
            let a = Stack.pop stk in
            let b = get_bool a in
            if b then pc<-pc+1
            else pc <- r
      | LD (_,i) ->
            if i<0 then failwith "LD : unrecognized var"
            else 
              let v = Array.get venv i in
              Stack.push v stk; pc<-pc+1
      | TAILCALL n ->
            (*            S(pc) = Call n   *)
            (* -------------------------------------------- *)
            (*  (CLS(e1,x1..xs,addr).v1..vs.os,pc,e,rs) *)
            (*  --> (os,addr,e1+[x<-v]*,(n-s,pc+1,e).rs) *)
            (*            S(pc) = TailCall n   s<=r+n              *)
            (* --------------------------------------------        *)
            (*  (CLS(e1,x1..xs,addr).v1..vs.os,pc,e,(r,npc,ne).rs) *)
            (*  --> (os,addr,e1+[x<-v]*,(r+n-s,npc,ne).rs) *)
            failwith "TAILCALL : TO BE IMPLEMENTED"
      | CALL n ->
            (*            S(pc) = Call n  s<=n *)
            (* -------------------------------------------- *)
            (*  (CLS(e1,x1..xs,addr).v1..vs.os,pc,e,rs) *)
            (*  --> (os,addr,e1+[x<-v]*,(n-s,pc+1,e).rs) *)

            (*            S(pc) = Call n  n<s *)
            (* -------------------------------------------- *)
            (*  (CLS(e1,x1..xs,addr).v1..vn.os,pc,e,rs) *)
            (*  --> (CLS(e1+[x->v],s-n,addr).os,pc,e,rs) *)
            begin
              match Stack.pop stk with
                | CLS(addr,s,e) ->
                      let m = Array.length e in
                      if n<s then
                        (* partial application *)
                        failwith "CALL -partial : TO BE IMPLEMENTED"
                      else
                        (* full/over application *)
                        let r = m+s in
                        let e2= Array.init r (fun i -> if i<m then Array.get e i else BOT) in
                        let _ = pop_2_venv stk e2 m r in
                        let _ = Stack.push (ref (n-s),pc+1,venv) rs in
                        let _ = venv <- e2 in
                        pc <- addr
                | _ -> failwith "CALL : not a function"
            end
      | RTN -> 
            (*          S(pc) = RTN *)
            (* ------------------------------ *)
            (*  (v.os,pc,e,(0,pc',e').rs) *)
            (*      --> (v.os,pc',e',rs) *)

            (*             S(pc) = RTN    0<s<=r *)
            (* -------------------------------------------------------- *)
            (*  (CLS(e1,x1..xs,addr).v1..vs.os,pc,e,(r,pc',e').rs) *)
            (*  --> (os,addr,e1[x<-v]*,(r-s,pc',e').rs) *)
            let (n_ref,npc,ne) = Stack.top rs in
            if !n_ref=0 then (let _ = Stack.pop rs in pc<-npc; venv<-ne)
            else 
              begin
                match Stack.pop stk with
                  | CLS(addr,s,e) ->
                        let m = Array.length e in
                        let r = m+s in
                        let e2= Array.init r (fun i -> if i<m then Array.get e i else BOT) in
                        let _ = pop_2_venv stk e2 m r in
                        let _ = n_ref := !n_ref-s in
                        (* let _ = Stack.push (n-s,npc,ne) rs in *)
                        let _ = venv <- e2 in
                        pc <- addr
                  | _ -> failwith "RTN 0<s<=n : not a closure"
              end
      | LDF(gvs,vs_len,l) ->
            (*     S(pc) = LDF(gvs,vs,l) *)
            (* ----------------------------------------------- *)
            (*  (os,pc,e,rs) --> ([CLS e[gvs],l].os,pc+1,e,rs) *)
            let gvs_len = List.length gvs in
            let e = Array.init gvs_len 
              (fun i-> 
                  let g = snd(List.nth gvs i) in
                  try
                    Array.get venv g
                  with v ->
                      begin
                        print_endline ("mkClosure problem "^(string_of_int g));
                        raise v
                      end) in
            Stack.push (CLS (l,vs_len,e)) stk;
            pc <- pc+1
      | LDFR(gvs,f,vs_len,l) ->
            (*     S(pc) = LDFR(gvs,vs,l) *)
            (* ----------------------------------------------- *)
            (*  (os,pc,e,rs) --> ([CLS e[gvs],l].os,pc+1,e,rs) *)
            let gvs_len = List.length gvs in
            let e = Array.init (gvs_len+1) 
              (fun i-> 
                  if i<gvs_len 
                  then 
                    let g = snd(List.nth gvs i) in
                    try
                      Array.get venv g
                    with v ->
                        begin
                          print_endline ("mkClosure "^(string_of_int g));
                          raise v
                        end
                  else BOT) in
            let cls = CLS (l,vs_len,e) in
            Array.set e gvs_len cls;
            Stack.push cls stk;
            pc <- pc+1
      | _ -> 
            begin
              proc_inst stk c;
              pc <- pc + 1
            end
                (* method to execute till DONE encountered *)
                (* and return the value on top of its stack *)
  method execute : value_mc =
    if mc # finish then Stack.pop stk
    else begin mc # oneStep; mc # execute end
end;;

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
  Arg.parse SPL_type.option_flag (fun s -> file := s) usage; 
  if String.length !file == 0 then print_endline usage else 
  let bytefn = !file^".svm" in
  let _ = print_endline ("Loading sVM code from .."^bytefn) in
  let instr = read_bytecode bytefn in
  let instr_lst = Array.to_list instr in
  let _ = print_endline ("Loaded "^(string_of_sVML_list instr_lst)) in
  let mc = new sVML instr_lst in
  let r = mc # execute in
  print_endline ("Executing ==> "^(string_of_sVML_value_mc r))
