open Printf

type variables = string;;

type expr = 
  | Num of int
  | Bool of bool
  | Var of variables
  | Plus of expr * expr
  | Times of expr * expr
  | Sub of expr * expr
  | Div of expr * expr
  | And of expr * expr
  | Or of expr * expr
  | Not of expr
  | Equal of expr * expr
  | Greater_than of expr * expr
  | If_then_else of expr * expr * expr
  | Abstraction of variables * expr
  | Application of expr * expr
;;

type gamma_table = (variables * expr) list;;

type closure = Closure_type of expr * env_closure

and env_closure = (expr * closure) list;;

exception Stuck;;
exception Stuck_new;;

let rec height e = match e with
  | Num n -> 0
  | Bool b -> 0
  | Var v -> 0
  | Plus (e1, e2) -> 1 + (max (height e1) (height e2))
  | Times (e1, e2) -> 1 + (max (height e1) (height e2))
  | Sub (e1, e2) -> 1 + (max (height e1) (height e2))
  | Div (e1, e2) -> 1 + (max (height e1) (height e2))
  | And (e1, e2) -> 1 + (max (height e1) (height e2))
  | Or (e1, e2) -> 1 + (max (height e1) (height e2))
  | Not e1 -> 1 + (height e1)
  | Equal (e1, e2) -> 1 + (max (height e1) (height e2))
  | Greater_than (e1, e2) -> 1 + (max (height e1) (height e2))
  | If_then_else (e0, e1, e2) -> 1 + (max (max (height e0) (height e1)) (height e2))
  | Abstraction (_, e1) -> 1 + (height e1)
  | Application (e1, e2) -> 1 + (max (height e1) (height e2))
;;

let rec size e = match e with
  | Num n -> 1
  | Bool b -> 1
  | Var v -> 1
  | Plus (e1, e2) -> 1 + (size e1) + (size e2)
  | Times (e1, e2) -> 1 + (size e1) + (size e2)
  | Sub (e1, e2) -> 1 + (size e1) + (size e2)
  | Div (e1, e2) -> 1 + (size e1) + (size e2)
  | And (e1, e2) -> 1 + (size e1) + (size e2)
  | Or (e1, e2) -> 1 + (size e1) + (size e2)
  | Not e1 -> 1 + size(e1)
  | Equal (e1, e2) -> 1 + (size e1) + (size e2)
  | Greater_than (e1, e2) -> 1 + (size e1) + (size e2)
  | If_then_else (e0, e1, e2) -> 1 + (size e0) + (size e1) + (size e2)
  | Abstraction (_, e1) -> 2 + (size e1)
  | Application (e1, e2) -> 1 + (size e1) + (size e2)
;;

let rec free_vars e = match e with
  | Num n -> []
  | Bool b -> []
  | Var v -> [v]
  | Plus (e1, e2) -> (free_vars e1) @ (free_vars e2)
  | Times (e1, e2) -> (free_vars e1) @ (free_vars e2)
  | Sub (e1, e2) -> (free_vars e1) @ (free_vars e2)
  | Div (e1, e2) -> (free_vars e1) @ (free_vars e2)
  | And (e1, e2) -> (free_vars e1) @ (free_vars e2)
  | Or (e1, e2) -> (free_vars e1) @ (free_vars e2)
  | Not e1 -> free_vars e1
  | Equal (e1, e2) -> (free_vars e1) @ (free_vars e2)
  | Greater_than (e1, e2) -> (free_vars e1) @ (free_vars e2)
  | If_then_else (e0, e1, e2) -> (free_vars e0) @ (free_vars e1) @ (free_vars e2)
  | Abstraction (x, e1) -> []
  | Application (e1, e2) -> free_vars e2
;;

let rec search_environment (env : env_closure) v = match env with
  | (env1,clos)::tail -> if v<>env1 then search_environment tail v else
      (
        match clos with
        | Closure_type (Abstraction (variable,expression), env) -> Closure_type (Abstraction (variable, expression), (env1,clos)::env)
        | _ -> clos
      )
  | [] -> raise Stuck
;;

let rec krivine expression_closure (stk : closure list) = match expression_closure with
  | Closure_type (Num n , env) -> Closure_type (Num n, env)
  | Closure_type (Bool b, env) -> Closure_type (Bool b, env)
  | Closure_type (Var v, env) -> krivine  (search_environment env (Var v)) stk
  | Closure_type (Plus (e1, e2), env) -> 
    let c1 = krivine (Closure_type (e1, env)) [] in
    let c2 = krivine (Closure_type (e2, env)) [] in
    (
      match (c1, c2) with
      | (Closure_type (Num n1, _), Closure_type(Num n2, _)) -> Closure_type(Num (n1 + n2), [])
      | _ -> raise Stuck_new
    )
  | Closure_type (Times (e1, e2), env) -> 
    let c1 = krivine (Closure_type (e1, env)) [] in
    let c2 = krivine (Closure_type (e2, env)) [] in
    (
      match (c1, c2) with
      | ( Closure_type (Num n1, _), Closure_type(Num n2, _)) -> Closure_type(Num (n1 * n2), [])
      | _ -> raise Stuck_new
    )
  | Closure_type (Sub (e1, e2), env) -> 
    let c1 = krivine (Closure_type (e1, env)) [] in
    let c2 = krivine (Closure_type (e2, env)) [] in
    (
      match (c1, c2) with
      | ( Closure_type (Num n1, _), Closure_type(Num n2, _)) -> Closure_type(Num (n1 - n2), [])
      | _ -> raise Stuck_new
    )
  | Closure_type (Div (e1, e2), env) -> 
    let c1 = krivine (Closure_type (e1, env)) [] in
    let c2 = krivine (Closure_type (e2, env)) [] in
    (
      match (c1, c2) with
      | ( Closure_type (Num n1, _), Closure_type(Num n2, _)) -> Closure_type(Num (n1 / n2), [])
      | _ -> raise Stuck_new
    )
  | Closure_type (And (e1, e2), env) -> 
    let c1 = krivine (Closure_type (e1, env)) [] in
    let c2 = krivine (Closure_type (e2, env)) [] in
    (
      match (c1, c2) with
      | ( Closure_type (Bool b1, _), Closure_type(Bool b2, _)) -> Closure_type(Bool (b1 && b2), [])
      | _ -> raise Stuck_new
    )
  | Closure_type (Or (e1, e2), env) -> 
    let c1 = krivine (Closure_type (e1, env)) [] in
    let c2 = krivine (Closure_type (e2, env)) [] in
    (
      match (c1, c2) with
      | ( Closure_type (Bool b1, _), Closure_type(Bool b2, _)) -> Closure_type(Bool (b1 || b2), [])
      | _ -> raise Stuck_new
    )
  | Closure_type (Not e1, env) -> 
    let c1 = krivine (Closure_type (e1, env)) [] in
    (
      match c1 with
      | ( Closure_type (Bool b1, _)) -> Closure_type(Bool (not b1), [])
      | _ -> raise Stuck_new
    )
  | Closure_type (Equal (e1, e2), env) -> 
    let c1 = krivine (Closure_type (e1, env)) [] in
    let c2 = krivine (Closure_type (e2, env)) [] in
    (
      match (c1, c2) with
      | ( Closure_type (Num n1, _), Closure_type(Num n2, _)) -> Closure_type(Bool (n1 = n2), [])
      | ( Closure_type (Bool b1, _), Closure_type(Bool b2, _)) -> Closure_type(Bool (b1 = b2), [])
      | _ -> raise Stuck_new
    )
  | Closure_type (Greater_than (e1, e2), env) -> 
    let c1 = krivine (Closure_type (e1, env)) [] in
    let c2 = krivine (Closure_type (e2, env)) [] in
    (
      match (c1, c2) with
      | ( Closure_type (Num n1, _), Closure_type(Num n2, _)) -> Closure_type(Bool (n1 > n2), [])
      | _ -> raise Stuck_new
    )
  | Closure_type (If_then_else (e0, e1, e2), env) ->
    let c0 = krivine(Closure_type (e0, env)) [] in
    (
      match c0 with
      | Closure_type (Bool true, _) -> krivine (Closure_type (e1, env)) []
      | Closure_type (Bool false, _) -> krivine (Closure_type (e2, env)) []
      | _ -> raise Stuck_new
    )
  | Closure_type (Abstraction (x, expression_inside), env) -> 
    (
      match stk with 
      | head :: tail -> krivine ( Closure_type(expression_inside, (Var x, head) :: env) ) tail
      | _ -> raise Stuck_new
    )
  | Closure_type (Application (e1, e2), env) -> krivine (Closure_type(e1, env)) ( Closure_type(e2, env) :: stk)
;;

let rec print_expression_closure clos = match clos with
  | Closure_type( Num n, env) -> printf "Answer is a number :- %d\n\n" n
  | Closure_type( Bool b, env) -> printf "Answer is a boolean :- %B\n\n" b
  | _ -> printf "\n\n\n\n"
;;

let rec generate_env_clos_for_gamma (gamma : gamma_table) = match gamma with
  | [] -> []
  | (v, value) :: tail -> (Var v, Closure_type(value, [])) :: (generate_env_clos_for_gamma tail)




let test_case = If_then_else(Greater_than(Num(8),Num(2)),Plus(Num(1), Num(2)), Div(Num(9), Num(0)));;
let test_env_closure = [];;

let test_case_expression_closure e = Closure_type(test_case, test_env_closure);; 
let answer_closure = krivine (test_case_expression_closure test_case) [];;

print_expression_closure answer_closure;;



(* Test cases *)

(* Test Case 1

   let gamma : gamma_table = [];;
   let test_case = Num 54;;

   Answer is a number :- 54 
*)

(* Test Case 2

   let gamma : gamma_table = [];;
   let test_case = Bool true;;

   Answer is a boolean :- true
*)

(* Test Case 3

   let gamma : gamma_table = [ ("a1", Num 3); ("a2", Bool false)];;
   let test_case = Var "a1";;

   Answer is a number :- 3
*)

(* Test Case 4

   let gamma : gamma_table = [ ("a1", Num 3); ("a2", Bool false)];;
   let test_case = Times (Var "a1", Times( Num 43, Plus( Var "a1", Var "a2")));;

   Fatal error: exception Main.Stuck_new
*)

(* Test Case 5

   let gamma : gamma_table = [ ("a1", Num 3); ("a2", Bool false)];;
   let test_case = Times (Var "a1", Times( Num 43, Plus( Var "a1", Num 2)));;

   Answer is a number :- 645
*)

(* Test Case 6

   let gamma : gamma_table = [ ("a1", Num 3); ("a2", Bool false)];;
   let test_case = Sub( Num 43, Div( Num 6, Num 3));;

   Answer is a number :- 41
*)

(* Test Case 7

   let gamma : gamma_table = [ ("a1", Bool true); ("a2", Bool false)];;
   let test_case = Or(Not(Var "a1"), And(Var "a1", Var "a2"));;

   Answer is a boolean :- false
*)

(* Test case 8

   let gamma : gamma_table = [ ("a1", Num 25); ("a2", Num 5)];;
   let test_case = Equal( Plus(Num 10, Var "a1"), Times(Var "a2", Num 7));;

   Answer is a boolean :- true
*)

(* Test Case 9

   let gamma : gamma_table = [ ("a1", Num 25); ("a2", Num 5)];;
   let test_case = Not ( Greater_than( Var "a1", Var "a2"));;

   Answer is a boolean :- false
*)

(* Test case 10 

   let gamma : gamma_table = [ ("a1", Num 25); ("a2", Num 5)];;
   let test_case = If_then_else( Equal( Num 5, Num 2), Plus(Var "a1", Num 30), Times(Var "a2", Num 30));;

   Answer is a number :- 150
*)

(* Test Case 11

   let gamma : gamma_table = [ ("a1", Num 25); ("a2", Num 5)];;
   let test_case = If_then_else( Not(Equal( Num 5, Num 2)), Plus(Var "a1", Num 30), Times(Var "a2", Num 30));;

   Answer is a number :- 55
*)

(* Test case 12

   let gamma : gamma_table = [ ("a1", Num 25); ("a2", Num 5)];;
   let test_case = Application( Abstraction( "x", Times( Var "x", Num 3)) , Plus( Var "a1", Num 5));;

   Answer is a number :- 90
*)

(* Test case 13

   let gamma : gamma_table = [ ("a1", Num 2); ("a2", Num 5)];;

   let function1 = Abstraction ( "x", Plus( Var "x", Var "a1"));;
   let function2 = Abstraction( "x", Times( Var "x", Num 5));;
   let test_case = Sub (Application( function1, Num 3), Application( function2, Num 10));;

   Answer is a number :- -45
*)

(* Test case 14

   let gamma : gamma_table = [ ("a1", Num 10); ("a2", Num 5)];;

   let function1 = Abstraction ( "x", Plus( Var "x", Var "a1"));;
   let function2 = Abstraction( "x", Times( Var "x", Num 5));;
   let test_case = Application( function1, Application( function2, Num 10));;

   Answer is a number :- 60
*)

(* Test case 15

   let gamma : gamma_table = [ ("a1", Num 25); ("a2", Num 0)];;
   let test_case = Application( Abstraction( "x", Times( Var "x", Num 3)) , Div( Var "a1", Var "a2"));;

   Fatal error: exception Division_by_zero
*)

(* Test case 16

   let gamma : gamma_table = [ ("a1", Num 25); ("a2", Num 0)];;
   let test_case = Application( Abstraction( "x", Times( Var "a1", Num 3)) , Div( Var "a1", Var "a2"));;

   Answer is a number :- 75
*)

(* Test case 17

   let gamma : gamma_table = [ ("a1", Num 2); ("a2", Bool true)];;
   let test_case = Application( Abstraction( "x", Times( Var "a1", Num 4)) , Plus( Var "a1", Var "a2"));;

   Answer is a number :- 8
*)

(* Test case 18
   
   let gamma : gamma_table = [ ("a1", Num 6); ("a2", Bool true)];;
   let test_case = Application( Abstraction( "x", Times( Var "a1", Num 7)) , Plus( Var "a1", Var "a3"));;

   Answer is a number :- 42
*)