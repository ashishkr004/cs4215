open Debug.Basic

open Camlp4
open DPL
open DPL_token

module M = DPL_lexer.Make(DPL_token)
(* type op_id = string *)

(* (\* abstract syntax tree for ePL *\) *)
(* type ePL_expr = *)
(*   | BoolConst of bool *)
(*   | IntConst of int *)
(*   | UnaryPrimApp of op_id * ePL_expr *)
(*   | BinaryPrimApp of op_id * ePL_expr * ePL_expr *)

(* (\* display ePL expr in prefix form *\) *)
(* let rec string_of_ePL (e:ePL_expr):string = *)
(*   match e with *)
(*     | BoolConst v -> "BoolConst("^(string_of_bool v)^")" *)
(*     | IntConst v -> "IntConst("^(string_of_int v)^")" *)
(*     | UnaryPrimApp (op,arg) -> op^(string_of_ePL arg) *)
(*     | BinaryPrimApp (op,arg1,arg2) -> op^"["^(string_of_ePL arg1)^","^(string_of_ePL arg2)^"]" *)

(*
Concrete syntax:
  type = Bool | Int 
         | type "->" type
         | "(" type ")"
  args =  v | v " " args
  ldecl = (type v "=" expr)+
  expr = "let" ldecl "in" type expr "end"
       | expr expr1 .. exprn
       | "(" expr ")"
       | "fun" type args "->" expr "end"
       | "recfun" v type args "->" expr "end"
*)

module DPLGram = Camlp4.Struct.Grammar.Static.Make(DPL_lexer.Make(DPL_token))

let prog = DPLGram.Entry.mk "prog"

let peek_typ = 
 DPLGram.Entry.of_parser "peek_typ" 
     (fun strm ->
       match Stream.npeek 2 strm with
          | [OPAREN,_;OPAREN,_] | [OPAREN,_;BOOL_TYP,_] | [OPAREN,_;INT_TYP,_] 
          | [OPAREN,_; UNIT_TYP,_] | [OPAREN,_;ERROR_TYP,_]-> ()
          | _ -> raise Stream.Failure)

let peek_ctyp = 
 DPLGram.Entry.of_parser "peek_typ" 
     (fun strm ->
       match Stream.npeek 2 strm with
          | [OBRACE,_;BOOL_TYP,_] | [OBRACE,_;INT_TYP,_] 
          | [OBRACE,_; UNIT_TYP,_] | [OBRACE,_;ERROR_TYP,_]-> raise Stream.Failure
          | _ -> ())

let peek_bool = 
 DPLGram.Entry.of_parser "peek_bool" 
     (fun strm ->
         (* Stream.npeek 2 strm; *)
           match Stream.npeek 2 strm with
             | [OR, one_case0] -> raise Stream.Failure
             | _ -> ()) 

let code_A = Char.code('A') 

let code_Z = Char.code('Z') 

(* convert binary application to vector application *)
let rec flatten_appln e acc =
  match e with
    | Appln (f,_,arg) -> flatten_appln f (arg@acc)
    (* | Var i ->    let c = Char.code(String.get i 0) in *)
    (*      if (code_A<=c) && (c<=code_Z) then Constr(i,acc) *)
    (*      else Appln(e,None,acc) *)
   | Constr (i,tag,arg) -> Constr(i,tag,arg@acc)
   | _ -> Appln(e,None,acc)

(* convert binary application to vector application *)
let rec flatten_appln_pat p acc =
  match p with
   |  PCons (i,tag,arg) -> PCons(i,tag,arg@acc)

let get_opt_list lst = match lst with Some p -> p | None -> [] 

EXTEND DPLGram
  GLOBAL: prog;

  (* list of algebraic type declar *)
  tdecl: [[adt_lst = LIST1 adtyp -> adt_lst]  ]; 

  ooo : [[`OR -> ()]];

  (* algebraic data type declaration *)
  adtyp: [ [`TYPEWORD; `IDENTIFIER s; param =  LIST0 typ_var; `EQ; OPT ooo; dl = data_list; `SEMICOLON -> (s,param,dl)]];

   (*list of new data  *)
  data_list: [[dl = LIST1 data SEP `OR -> dl]];

  (*new data*)
  data: [[`UIDENTIFIER s; dl = LIST0 datat -> (s,dl) ]];

  datat: [ 
    [t = typ-> t]
     |
    [`OPAREN; t = typ0; `CPAREN -> t]
  ];

  (* typ or algebraic data type with its param *)
  typ0: [[t = typ -> t]
    | [`IDENTIFIER s; param = LIST0 typ ->  TDef(s,param)]];

  exp: [[e = expr;`EOF ->  e]  ];

  typ_var : [[`QUOTE; `IDENTIFIER s -> ("'"^s)]];

  typ: [[`BOOL_TYP   -> BoolType
        | `INT_TYP   -> IntType
        | `UNIT_TYP  -> Void
        | `ERROR_TYP -> TError
        | `QUOTE; `IDENTIFIER s -> TVar("'"^s)]
        | RIGHTA
          [t1=SELF;`RARROW;t2=SELF -> Arrow(t1,t2)]
        | [peek_typ;`OPAREN;t=SELF; `CPAREN -> t
  ]];

  ctype:[[`OBRACE;t=typ;`CBRACE -> t  ]];

  args: [[ al = LIST1 [s = identfs -> s] -> al
  ]];

  identfs: [[`UIDENTIFIER s -> s] | [`IDENTIFIER s -> s]];
  
  decl: [[t=OPT ctype; s = identfs ; `EQ; e = expr -> (t,s,e) ]];

  ldecl: [[ld = LIST1 decl -> ld]];

  match_case: [[ld = LIST1 one_case SEP `SEMICOLON -> ld]];

  (* one_case: [[`UIDENTIFIER s; p = LIST0 [ s = identfs -> s]; `RARROW; e = expr -> ((s,0, p),e)]]; *)
  (* one_case: [[`OPAREN; `UIDENTIFIER s; p = one_case_pattern_param;`CPAREN; `RARROW; e = expr -> ((s,0, p),e)] | *)
  (*         [`UIDENTIFIER s; p = one_case_pattern_param; `RARROW; e = expr -> ((s,0, p),e)]]; *)

  (* one_case: [[ p = nest_pat; `RARROW; e = expr -> (p,e)]]; *)

  one_case: [[`OPAREN; p = nest_pat;`CPAREN; `RARROW; e = expr -> (p, e)] |
          [p = nest_pat; `RARROW; e = expr -> (p,e)]];

  nest_pat: 
     [
      [`UIDENTIFIER s; p = LIST0 nested_pat ->  PCons(s,0, p)]];

  nested_pat: 
      [
        [`OPAREN ;`UIDENTIFIER s; p = LIST0 nested_pat;`CPAREN ->  PCons(s,0, p)]
        | [`IDENTIFIER s -> PVar(s)]
        | [`UIDENTIFIER s ->  PCons(s,0, [])]];

  (* nest_pat:  *)
  (*        [ *)
  (*          [`OPAREN ; p = nest_pat;`CPAREN ->  p]  *)
  (*        | [`IDENTIFIER s -> PVar(s)] *)
  (*        | [`UIDENTIFIER s; p = LIST0 nest_pat ->  PCons(s,0, p)]]; *)



  (* one_case_pattern_param:  *)
  (*     [[s = OPT [s = LIST1 identfs -> s];  *)
  (*     p = OPT [`OPAREN; p =  one_case_pattern_param; `CPAREN -> p] -> (get_opt_list s)@(get_opt_list p)]]; *)


  (* one_case0: [[`UIDENTIFIER s; p = LIST0 [`IDENTIFIER s -> s]; `RARROW -> (s,p)]]; *)
  
  expr:
       [ 
          [e1 = SELF; e2 = SELF -> flatten_appln e1 [e2]]
       | "Boolean" NONA 
            [e1 = SELF; `EQ ; e2 = SELF -> BinaryPrimApp ("=",e1,e2)]
          | [e1 = SELF; `LT ; e2 = SELF -> BinaryPrimApp ("<",e1,e2)
          |  e1 = SELF; `GT ; e2 = SELF -> BinaryPrimApp (">",e1,e2)]
          | [e1 = SELF; `AND ; e2 = SELF -> BinaryPrimApp ("&",e1,e2)
          |  e1 = SELF; (* peek_bool; *) `OR ;  e2 = SELF -> BinaryPrimApp ("|",e1,e2)
          ]
        | "Unary" NONA
          [ `UMINUS ; e=SELF -> UnaryPrimApp("~",e)
          | `NEG ; e=SELF -> UnaryPrimApp("\\",e)
          ]
        |  "Sub" LEFTA
          [ e1 = SELF; `MINUS ;  e2 = SELF -> BinaryPrimApp ("-",e1,e2) ]
        | "Add" LEFTA
          [ e1 = SELF; `PLUS ; e2 = SELF -> BinaryPrimApp ("+",e1,e2) ]
        | "Mul" LEFTA
          [ e1 = SELF; `STAR ; e2 = SELF -> BinaryPrimApp ("*",e1,e2) ]
        |  "Div" LEFTA
          [e1 = SELF; `DIV ;  e2 = SELF -> BinaryPrimApp ("/",e1,e2) ]
        | [`LETWORD; ld = ldecl ; `INWORD ; t=OPT ctype;e = SELF ; `ENDWORD -> Let(ld,t,e) 
        |  `FUN; t = OPT ctype ; al = args;`RARROW; e = SELF; `ENDWORD -> Func(t,al,e)
        |  `RECFUN; s = identfs ; t = OPT ctype; al = args; `RARROW; e = SELF; `ENDWORD 
          -> RecFunc(t,s,al,e)
        (* |  e = SELF; t = OPT typ; el = LIST1 SELF -> Appln(e,t,el) *)
          ]
        | LEFTA 
            [`IFWORD; e1 = SELF; `THENWORD; e2 = SELF; `ELSEWORD; e3 = SELF;`ENDWORD -> Cond(e1,e2,e3)]
        | "TryCatch" LEFTA 
            [`TRYWORD;  e1 = SELF; `CATCHWORD;  s = identfs ; `WITHWORD; e3 = SELF; `ENDWORD -> TryCatch(e1,s,e3)]
        | "Match" LEFTA 
            [`MATCHWORD;  e1 = SELF; `WITHWORD; OPT ooo; cases = match_case; `ENDWORD -> Match(e1,cases)] 
        | "Throw" 
           [`THROWWORD; e = SELF -> Throw(e)]
        | "HasType" 
           [peek_ctyp;`OBRACE; e = SELF; `COLON; t = typ; `CBRACE  ->  HasType(e,t) ]
        | "Bracket" 
           [ `OPAREN; e=SELF; `CPAREN -> e]
        | NONA 
          [ `INT_LIT (i, _) -> IntConst(i)
          | `TRUE -> BoolConst(true)
          | `FALSE -> BoolConst(false)
          | `UIDENTIFIER s -> Constr(s,0,[])
          | `IDENTIFIER s -> Var(s) 
          ]
      ];

  prog: [
      [tdec = OPT tdecl; e = exp ->
          begin
          match tdec with
            | Some l -> (l,e)
            | None -> ([],e)
          end
      ]
  ];
  END
;;
let _loc = PreCast.Loc.mk "<string>" 

(* parse from a string *)
let parse fname str =
try 
  let e = DPLGram.parse_string prog _loc str in e 
with
      End_of_file -> exit 0
    | M.Loc.Exc_located (l,t)->
      (print_string ("Parse Error in "^(Camlp4.PreCast.Loc.to_string l)^"\n");
       raise t)

(* let main = *)
(*    print_string "# "; *)
(*   let str = read_line () in *)
(*   let e = parse str in		 *)
(*   print_string (string_of_dPL e) *)

(* parse from a file *)
let parse_file (filename:string) : (string * ( 'a * dPL_nexpr)) =
  let contents =
    let lines = ref [] in
    let chan = open_in filename in
    try
      while true; do
        lines := input_line chan :: !lines
      done; []
    with End_of_file ->
        close_in chan;List.rev !lines in
  let str = String.concat "" contents in
  let chan = open_in filename in
  let istream = Stream.of_channel chan in
  try 
    let (tdl,e) = DPLGram.parse prog (PreCast.Loc.mk filename) istream in
    (str,(tdl,e))
  with M.Loc.Exc_located (l,t)->
      (print_string ("Parse Error in "^(Camlp4.PreCast.Loc.to_string l)^"\n");
       raise t)
