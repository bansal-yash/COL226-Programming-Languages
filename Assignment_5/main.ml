open List;;

type symbol = string * int;;
type signature = symbol list;;

type tree = 
  | Var of string
  | Num of int
  | C of { node : symbol ; children : tree list}
;;

let rec check_sig_helper given_signature symbols_till_now = match given_signature with
  | [] -> true
  | head :: tail ->
    let (a, b) = head in
    if (b < 0 || mem a symbols_till_now) then false
    else check_sig_helper tail (a :: symbols_till_now)
;;

let check_sig given_signature = check_sig_helper given_signature [];;

let rec wftree valid_signature t = match t with
  | Var v -> true
  | Num n -> true
  | C sym -> 
    let (s, n) = sym.node in
    if (mem sym.node valid_signature) && (n = length sym.children)
    then fold_left (&&) true (map (wftree valid_signature ) sym.children)
    else false
;;

let rec height t = match t with
  | Var v -> 0
  | Num n -> 0
  | C sym -> 
    let (s, n) = sym.node in (
      if n = 0 then 0 
      else 1 + fold_left max 0 (map height sym.children)
    )
;;

let rec size t = match t with
  | Var v -> 1
  | Num n -> 1
  | C sym -> 1 + (fold_left (+) 0 (map size sym.children))
;;

let rec vars t = match t with
  | Var v -> [v]
  | Num n -> []
  | C sym -> fold_left (@) [] (map vars sym.children)
;;


let rec mirror t = match t with 
  | Var v -> Var v
  | Num n -> Num n
  | C sym -> C { node = sym.node; children = rev (map mirror sym.children) }
;;

let rec find_list_subs element ls = match ls with 
  | [] -> Var element
  | (var, tree) :: tail -> 
    if var = element then tree else find_list_subs element tail
;; 

let rec substitute given_substitutions t = match t with
  | Var x -> find_list_subs x given_substitutions
  | Num n -> Num n
  | C r -> C { node = r.node; children = map (substitute given_substitutions) r.children }
;;

let rec composite_substitute given_substitutions t = match t with 
  | Var x -> 
    let a = find_list_subs x given_substitutions in
    if a = Var x then Var x
    else composite_substitute given_substitutions a
  | Num n -> Num n
  | C r -> C { node = r.node; children = map (composite_substitute given_substitutions ) r.children }
;;

let rec mem_subs element ls = match ls with 
  | [] -> false
  | (var, tree) :: tail -> 
    if var = element then true else mem_subs element tail
;; 

let rec not_common s1 s2 = match s2 with
  | [] -> []
  | head :: tail ->
    if mem_subs (fst head) s1 then not_common s1 tail else head :: (not_common s1 tail)

let rec comp_subs_helper s s1 s2 = match s1 with
  | [] -> not_common s s2
  | (a,b) :: tail -> (a, substitute s2 b) :: comp_subs_helper s tail s2
;;

let rec comp_subs s1 s2 = comp_subs_helper s1 s1 s2;;

let rec mgu t u = match t with
  | Var v1 -> (
      match u with
      | Var v2 -> 
        if v1 = v2 then [(v1, Var v1)]
        else [(v1, Var v2)]
      | Num n -> [(v1, Num n)]
      | C sym2 -> 
        let variables_in_u = vars u in
        if mem v1 variables_in_u then failwith "mgu not exists"
        else [(v1, C sym2)]
    )

  | Num n1 -> (
      match u with
      | Var v -> [(v, Num n1)]
      | Num n2 -> if n1 == n2 then [] else failwith "mgu not exist"
      | C sym -> failwith "mgu not exist"
    )

  | C sym1 -> (
      match u with 
      | Var v2 -> 
        let variables_in_t = vars t in
        if mem v2 variables_in_t then failwith "mgu not exists" 
        else [(v2, C sym1)]
      | Num n -> failwith "mgu not exists"
      | C sym2 -> 
        let (s1, n1) = sym1.node in
        let (s2, n2) = sym2.node in
        if s1 <> s2 || n1 <> n2 then failwith "mgu does not exist"
        else
          fold_left (comp_subs) [] (map2 mgu sym1.children sym2.children)
    )
;;





let rec print_tree t = match t with
  | Var v -> Printf.printf " (Variable:- %s) " v
  | Num n -> Printf.printf " (Number:- %d) " n
  | C sym -> 
    let (s,n) = sym.node in
    Printf.printf " (Symbol:- %s " s;
    Printf.printf " Arity:- %d )\n" n;
    Printf.printf " Childrens :- (\n";
    fold_left (fun _ child -> print_tree child ) () sym.children;
    Printf.printf " )\n"
;;

let rec print_list l = match l with 
  | [] -> Printf.printf "\n"
  | head :: tail ->
    Printf.printf "%s " head;
    print_list tail
;;

let rec print_substitution s = match s with
  | [] -> Printf.printf "\n"
  | (a,b) :: tail ->
    Printf.printf "Variable :- %s\n" a;
    print_tree b;
    Printf.printf "\n";
    print_substitution tail;
;;

let my_valid_signature = [("plus", 2); ("times", 2); ("mul", 2); ("div", 2); ("mod", 2); ("and", 2); ("or", 2);("not", 1); 
                          ("xor", 2); ("equal", 2); ("greater_than", 2); ("less_than", 2);("true", 0); ("false", 0); 
                          ("if_then_else", 3); ("pair", 2); ("first", 1); ("second", 1)];;






(* 
let tree1 = C {node = ("+", 2); children = [Var "x"; Var "y"] };;
let tree2 = C {node = ("+", 2); children = [ C {node = ("+", 8); children = [Num 9; Var "y"]} ; Var "x"] };;

let mgutree = mgu tree1 tree2;;

Printf.printf "The most general unifier is :- \n";;
print_substitution mgutree;;
Printf.printf "\n";;

let tree3 = substitute mgutree tree1;;
let tree4 = substitute mgutree tree2;;

Printf.printf "Tree 1 after substituting mgu :- \n";;
print_tree tree3;;
Printf.printf "\n";;
Printf.printf "Tree 2 after substituting mgu :- \n";;
print_tree tree4;;
Printf.printf "\n";;
 *)


(* 
Test case 1:- 

Different variables

let tree1 = Var "x";;
let tree2 = Var "y";;

The most general unifier is :- 
Variable :- x
 (Variable:- y) 


Tree 1 after substituting mgu :- 
 (Variable:- y) 
Tree 2 after substituting mgu :- 
 (Variable:- y) 

*)

(* 
Test case 2:- 

Same variables 

let tree1 = Var "a";;
let tree2 = Var "a";;

The most general unifier is :- 
Variable :- a
 (Variable:- a) 


Tree 1 after substituting mgu :- 
 (Variable:- a) 
Tree 2 after substituting mgu :- 
 (Variable:- a) 

*)

(* 
Test case 3:- 

One varible other not a variable and same variable is not occuring in other expression

let tree1 = Var "x";;
let tree2 = C {node = ("+", 2); children = [Num 1; Num 6] };;

The most general unifier is :- 
Variable :- x
 (Symbol:- +  Arity:- 2 )
 Childrens :- (
 (Number:- 1)  (Number:- 6)  )



Tree 1 after substituting mgu :- 
 (Symbol:- +  Arity:- 2 )
 Childrens :- (
 (Number:- 1)  (Number:- 6)  )

Tree 2 after substituting mgu :- 
 (Symbol:- +  Arity:- 2 )
 Childrens :- (
 (Number:- 1)  (Number:- 6)  )

*)

(* 
Test case 4:- 

One varible other not a variable and same variable is occuring in other expression

let tree1 = Var "x";;
let tree2 = C {node = ("+", 2); children = [Var "x"; Num 6] };;

Fatal error: exception Failure("mgu not exists")

*)

(* 
Test case 5:- 

When both expressions are not variables and with different nodes

let tree1 = C {node = ("*", 2); children = [Num 3; Num 6] };;
let tree2 = C {node = ("+", 2); children = [Num 3; Num 6] };;

Fatal error: exception Failure("mgu does not exist")

*)

(* 
Test case 6:- 

When both the trees are same

let tree1 = C {node = ("+", 2); children = [Num 3; Num 6] };;
let tree2 = C {node = ("+", 2); children = [Num 3; Num 6] };;

The most general unifier is :- 


Tree 1 after substituting mgu :- 
 (Symbol:- +  Arity:- 2 )
 Childrens :- (
 (Number:- 3)  (Number:- 6)  )

Tree 2 after substituting mgu :- 
 (Symbol:- +  Arity:- 2 )
 Childrens :- (
 (Number:- 3)  (Number:- 6)  )

*)

(* 
Test case 7:- 

When both expressions are not variables but mgu should exist

let tree1 = C {node = ("+", 2); children = [Var "x"; Num 6] };;
let tree2 = C {node = ("+", 2); children = [ C {node = ("+", 8); children = [Num 9; Var "y"]} ; Num 6] };;

The most general unifier is :- 
Variable :- x
 (Symbol:- +  Arity:- 8 )
 Childrens :- (
 (Number:- 9)  (Variable:- y)  )



Tree 1 after substituting mgu :- 
 (Symbol:- +  Arity:- 2 )
 Childrens :- (
 (Symbol:- +  Arity:- 8 )
 Childrens :- (
 (Number:- 9)  (Variable:- y)  )
 (Number:- 6)  )

Tree 2 after substituting mgu :- 
 (Symbol:- +  Arity:- 2 )
 Childrens :- (
 (Symbol:- +  Arity:- 8 )
 Childrens :- (
 (Number:- 9)  (Variable:- y)  )
 (Number:- 6)  )

*)

(* 
Test case 8:- 

let tree1 = C {node = ("+", 2); children = [Var "x"; Var "y"] };;
let tree2 = C {node = ("+", 2); children = [ C {node = ("+", 8); children = [Num 9; Var "y"]} ; Var "x"] };;

The most general unifier is :- 
Variable :- x
 (Symbol:- +  Arity:- 8 )
 Childrens :- (
 (Number:- 9)  (Variable:- x)  )

Variable :- y
 (Variable:- x) 


Tree 1 after substituting mgu :- 
 (Symbol:- +  Arity:- 2 )
 Childrens :- (
 (Symbol:- +  Arity:- 8 )
 Childrens :- (
 (Number:- 9)  (Variable:- x)  )
 (Variable:- x)  )

Tree 2 after substituting mgu :- 
 (Symbol:- +  Arity:- 2 )
 Childrens :- (
 (Symbol:- +  Arity:- 8 )
 Childrens :- (
 (Number:- 9)  (Variable:- x)  )
 (Symbol:- +  Arity:- 8 )
 Childrens :- (
 (Number:- 9)  (Variable:- x)  )
 )

*)