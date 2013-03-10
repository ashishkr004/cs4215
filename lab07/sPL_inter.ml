open SPL_type
open SPLc
open Debug.Basic

(* use primitive rule to contract op[v1,v2] or op[v] to a value *)
(* raise an exception if we cannot directly contract *)
let rec contract (e:sPL_expr): sPL_expr = 
    match e with
    | BoolConst _ | IntConst _ -> e
    | UnaryPrimApp (op,arg) ->
        begin
            match op with
            | "~" ->
                begin
                    match arg with
                    | IntConst v -> IntConst (-v)
                    | _ -> failwith ("unable to contract for "^(string_of_sPL e))
                end
            | "\\" ->
                begin
                    match arg with
                    | BoolConst v -> BoolConst (not v)
                    | _ -> failwith ("unable to contract for "^(string_of_sPL e))
                end
            | _ -> failwith ("illegal unary op "^op)
        end
    | BinaryPrimApp (op,arg1,arg2) ->
        begin
            match op with
            | "+" ->
                begin
                    match arg1,arg2 with
                    | IntConst v1,IntConst v2 -> IntConst (v1+v2)
                    | _,_ -> failwith ("unable to contract "^(string_of_sPL e))
                end
            | "-" ->
                begin
                    match arg1,arg2 with
                    | IntConst v1,IntConst v2 -> IntConst (v1-v2)
                    | _,_ -> failwith ("unable to contract"^(string_of_sPL e))
                end
            | "*" ->
                begin
                    match arg1,arg2 with
                    | IntConst v1,IntConst v2 -> IntConst (v1*v2)
                    | _,_ -> failwith ("unable to contract"^(string_of_sPL e))
                end
            | "/" ->
                begin
                    match arg1,arg2 with
                    | IntConst v1,IntConst v2 -> IntConst (v1/v2)
                    | _,_ -> failwith ("unable to contract"^(string_of_sPL e))
                end
            | "|" ->
                begin
                    match arg1,arg2 with
                    | BoolConst v1,BoolConst v2 -> BoolConst (v1||v2)
                    | _,_ -> failwith ("unable to contract"^(string_of_sPL e))
                end
            | "&" ->
                begin
                    match arg1,arg2 with
                    | BoolConst v1,BoolConst v2 -> BoolConst (v1&v2)
                    | _,_ -> failwith ("unable to contract"^(string_of_sPL e))
                end
            | "<" ->
                begin
                    match arg1,arg2 with
                    | IntConst v1,IntConst v2 -> BoolConst (v1<v2)
                    | _,_ -> failwith ("unable to contract"^(string_of_sPL e))
                end
            | ">" ->
                begin
                    match arg1,arg2 with
                    | IntConst v1,IntConst v2 -> BoolConst (v1>v2)
                    | _,_ -> failwith ("unable to contract"^(string_of_sPL e))
                end
            | "=" ->
                begin
                    match arg1,arg2 with
                    | IntConst v1,IntConst v2 -> BoolConst (v1=v2)
                    | _,_ -> failwith ("unable to contract"^(string_of_sPL e))
                end
            | _ -> failwith ("illegal binary op "^op)
        end
    | _ -> e (* not a primitive for reduction *)


(* returns true if not(i in vs) *)
let notin (i:'a) (vs:'a list) : bool =
    not(List.exists (fun v -> v=i) vs)

(* remove [v->e] from subs that are captured by vs *)
(* filter_capture [(x,e1);(z,e2)] [x;y] ==> [(z,e2)] *)
let filter_clash (subs:('a*'b) list) (vs:'a list) : ('a*'b) list=
    List.filter (fun (v,_) -> notin v vs) subs

(* replace i by e if [i->e] in ss *)
let subs_var (i:string) (ss:(string*sPL_expr)list) : sPL_expr =
    try 
        snd(List.find (fun (v,_) -> v=i) ss)
    with _ -> Var i

(* rename i by v if [i->v] in ss *)
let ren_var (i:id) (ss:(id*id)list) : id =
    try 
        snd(List.find (fun (v,_) -> v=i) ss)
    with _ -> i

(* find name clashes and replace those that clash with fresh names *)
(* find_name_capture [x,y] [x] ==> ([_fresh_0,y],[(x,_fresh_0)] *)
let find_name_capture (xs:id list) (vv:id list) : ((id list) * (id * id) list) =
    let rec aux xs =
        match xs with
        | [] -> ([],[])
        | (x::xs) -> 
            let (r1,r2)=aux xs in
            if List.exists (fun v1 -> x=v1) vv then 
                let v = names # fresh_id in
                (v::r1,(x,v)::r2)
            else (x::r1,r2)
    in aux xs

let find_name_capture xs vv =
  (* let pr_exp = string_of_sPL in *)
    let pr1 = pr_list pr_id in
    let pr2 = pr_pair pr1 (pr_list (pr_pair pr_id pr_id)) in
    Debug.no_2 "find_name_capture" pr1 pr1 pr2 find_name_capture xs vv 

(* 
   given renaming [v->w], this method will rename 
   each free occurrence of v by w in e 
   no need to worry about capture here
   as we expect w to be fresh
*)
let rename_expr (vs:(id*id) list) (exp:sPL_expr) =
    let rec aux ss e =
        match e with
        | BoolConst _ | IntConst _ -> e
        | Var i -> Var (ren_var i ss)
        | UnaryPrimApp (op,arg) 
            -> UnaryPrimApp (op,aux ss arg)
        | BinaryPrimApp (op,arg1,arg2) 
            -> BinaryPrimApp (op,aux ss arg1,aux ss arg2)
        | Cond (e1,e2,e3) 
            -> Cond (aux ss e1,aux ss e2,aux ss e3)
        | Func (t,vs,body) -> 
            let nss = filter_clash ss vs in
            Func (t,vs,aux nss body)
      (* Func (t,vs,aux nss e) *)
        | RecFunc (t,f,vs,body) ->
            let nss = filter_clash ss (f::vs) in
            RecFunc (t,f,vs,aux nss body)
        | Appln (e1,t,es) -> Appln (aux ss e1,t,List.map (aux ss) es)
    in 
    if vs=[] then exp
    else aux vs exp


let rename_expr (vs:(id*id) list) (exp:sPL_expr) =
    let pr1 = pr_list (pr_pair pr_id pr_id) in
    let pr2 = string_of_sPL in
    Debug.no_2 "rename_expr" pr1 pr2 pr2 rename_expr vs exp


let filter_clash subs vs =
    let pr1 = pr_list (pr_pair pr_id string_of_sPL) in
    let pr2 = pr_list pr_id in
    Debug.no_2 "filter_clash" pr1 pr2 pr1 filter_clash subs vs 

(* apply substitution ss into expr e *)
(*   must avoid name_clashes *)
(*   must rename to avoid name_capture *)
let apply_subs 
        (ss:(id*sPL_expr)list) 
        (e:sPL_expr) : sPL_expr =
    let rec aux ss e =
        match e with
        | BoolConst _ | IntConst _ -> e
        | Var i -> subs_var i ss
        | UnaryPrimApp (op,arg) 
            -> UnaryPrimApp (op,aux ss arg)
        | BinaryPrimApp (op,arg1,arg2) 
            -> BinaryPrimApp (op,aux ss arg1,aux ss arg2)
        | Cond (e1,e2,e3) 
            -> Cond (aux ss e1,aux ss e2,aux ss e3)
        | Func (t,vs,body) -> 
        (* must avoid name clash and name capture *)
        (* get list of substitutions that can be made (filter_clash) *)
            let possible_subs = filter_clash ss vs in
        (* handle name capture *)
            let free_variables = List.concat (List.map (fun (_, expr) -> fv expr) possible_subs) in
            let (new_args, new_names) = find_name_capture vs free_variables in
            let new_body = rename_expr new_names body in
            Func (t, new_args, aux possible_subs new_body)
        | RecFunc (t,f,vs,body) ->
        (* must avoid name clash and name capture *)
            let possible_subs = filter_clash ss (f::vs) in
        (* handle name capture *)
            let free_variables = List.concat (List.map (fun (_, expr) -> fv expr) possible_subs) in
            let (new_args, new_names) = find_name_capture (f::vs) free_variables in
            let new_body = rename_expr new_names body in
            RecFunc (t, List.hd new_args, List.tl new_args, aux possible_subs new_body)
      (* begin *)
      (*   match List.filter (fun (x, y) -> x = f) new_names with *)
      (*     | [] -> RecFunc (t, f, new_args, aux possible_subs new_body) *)
      (*     | [(f, new_f)] -> RecFunc (t, new_f, new_args, aux possible_subs new_body) *)
      (* end         *)
                
        | Appln (e1,t,es) -> Appln (aux ss e1,t,List.map (aux ss) es)
    in aux ss e

let apply_subs (ss:(string*sPL_expr)list) (e:sPL_expr) : sPL_expr =
    let pr = string_of_sPL in
    let pr1 = pr_list (pr_pair pr_id pr) in
    Debug.ho_2 "apply_subs" pr1 pr pr apply_subs ss e


(* pre: len vs <= length args *)
(* returns zipped list and remainder *)
(* pair_up [1;2] [`a;`b;`c] ==> ([(1,`a);(2,`b)],[`c;`d]) *)
let pair_fn_args (vs:'a list) (args:'b list) : ('a*'b) list * 'b list =
    let rec aux vs args =
        match vs,args with
        | [],args -> ([],args)
        | v::vs,a::args ->
            let (subs,rem)=aux vs args in
            ((v,a)::subs,rem)
        | _,_ -> failwith "partial application should have been transformed"
    in aux vs args


module S = SPL

(* Custom shit placed in after this mark *)

let e1 = Cond (Var "a", Var "b", Var "c")
let t1 = S.Arrow(S.IntType,S.IntType)
let e2 = Func (t1, ["b"], e1)
let e3 = RecFunc (t1, "f",["b"],
                  Cond (Var "a", Var "b",Appln(Var "f",t1,[Var "c"])))
let s1 = [("b",IntConst 1);("c",BinaryPrimApp("+",IntConst 2,IntConst 3))]
let s2 = [("b",IntConst 1);("c",BinaryPrimApp("+",IntConst 2,Var "b"))]
let s3 = [("b",IntConst 1);("c",BinaryPrimApp("+",IntConst 2,Var "f"))]

let test_s1 =
    apply_subs s1 e1;
    apply_subs s1 e2;
    apply_subs s1 e3

let test_s2 =
    apply_subs s2 e1;
    apply_subs s2 e2;
    apply_subs s2 e3

let test_s3 =
    apply_subs s3 e1;
    apply_subs s3 e2;
    apply_subs s3 e3
