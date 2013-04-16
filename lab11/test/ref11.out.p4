LOADING dPL program ..
  type list 'a =   | Nil  | Cons 'a (list 'a);fun x ->  match x with   Cons _ y ->     match y with      Cons a _ -> a    end  endend
 AS ==> 
	 Type Declarations: [(list,list ['a] =[Nil [],Cons ['a,(list 'a)]])]
	 Expression: fun  x -> 
(match Var(x) with 
(Cons{0} _ y) -> 
(match Var(y) with 
(Cons{0} a _) -> Var(a) end) 
 end) 
 end
PRE-PROCESSING ..
 ==> pre-proc : fun  x -> 
(match Var(x) with 
(Nil{1} ) -> throw(Int(1));
(Cons{2} _ y) -> 
(match Var(y) with 
(Nil{1} ) -> throw(Int(1));
(Cons{2} a _) -> Var(a) end) 
 end) 
 end
