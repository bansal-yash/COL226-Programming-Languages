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
  | Pair of expr * expr
  | First of expr
  | Second of expr
  | Definition of variables * expr * expr
  | Abstraction of variables * expr
  | Application of expr * expr
;;

type opcode = 
  | Load_int of int
  | Load_bool of bool
  | Lookup of variables
  | Store of variables
  | Remove
  | Plus_op
  | Times_op
  | Sub_op
  | Div_op
  | And_op
  | Or_op
  | Not_op
  | Equal_op
  | Greater_than_op
  | If_then_else_op of compiled_code * compiled_code
  | Pair_op
  | First_op
  | Second_op
  | App
  | Make_closure of variables * compiled_code
  | Return

and compiled_code = opcode list
;;

type values =
  | N of int
  | B of bool
  | P of values * values
  | Clos of variables * compiled_code * gamma_table

and gamma_table = (variables * values) list;;

type stack = values list;;

type dump = (stack * gamma_table * compiled_code) list;;

exception Stuck;;

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
  | Pair (e1, e2) -> 1 + (max (height e1) (height e2))
  | First e1 -> 1 + height e1
  | Second e1 -> 1 + height e1
  | Definition (_, e1, e2) -> 1 + (max (height e1) (height e2))
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
  | Pair (e1, e2) -> 1 + (size e1) + (size e2)
  | First e1 -> 1 + (size e1)
  | Second e1 -> 1 + (size e1)
  | Definition (_, e1, e2) -> 2 + (size e1) + (size e2)
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
  | Pair (e1, e2) -> (free_vars e1) @ (free_vars e2)
  | First e1 -> free_vars e1
  | Second e1 -> free_vars e1
  | Definition (v, e1, e2) -> []
  | Abstraction (x, e1) -> []
  | Application (e1, e2) -> free_vars e2
;;

let rec compile e = match e with
  | Num n -> ([Load_int n] : compiled_code)
  | Bool b -> [Load_bool b]
  | Var v -> [Lookup v]
  | Plus (e1, e2) -> (compile e1) @ (compile e2) @ [Plus_op]
  | Times (e1, e2) -> (compile e1) @ (compile e2) @ [Times_op]
  | Sub (e1, e2) -> (compile e1) @ (compile e2) @ [Sub_op]
  | Div (e1, e2) -> (compile e1) @ (compile e2) @ [Div_op]
  | And (e1, e2) -> (compile e1) @ (compile e2) @ [And_op]
  | Or (e1, e2) -> (compile e1) @ (compile e2) @ [Or_op]
  | Not e1 -> (compile e1) @ [Not_op]
  | Equal (e1, e2) -> (compile e1) @ (compile e2) @ [Equal_op]
  | Greater_than (e1, e2) -> (compile e1) @ (compile e2) @ [Greater_than_op]
  | If_then_else (e0, e1, e2) -> (compile e0) @ [ If_then_else_op (compile e1 , compile e2) ]
  | Pair (e1, e2) -> (compile e1) @ (compile e2) @ [Pair_op]
  | First e1 -> (compile e1) @ [First_op]
  | Second e1 -> (compile e1) @ [Second_op]
  | Definition (v, e1, e2) -> (compile e1) @ [Store v] @ (compile e2) @ [Remove]
  | Abstraction (v, e1) -> [ Make_closure(v, compile(e1) @ [Return]) ]
  | Application (e1, e2) -> compile(e1) @ (compile e2) @ [App]
;;

let rec print_compiled_code (c : compiled_code) = match c with
  | [] -> printf "\n"
  | head :: tail ->
    (
      match head with
      | Load_int n -> printf "Load_int %d\n" n; print_compiled_code tail
      | Load_bool b -> printf "Load_bool %B\n" b; print_compiled_code tail
      | Lookup v -> printf "Lookup %s\n" v; print_compiled_code tail
      | Store v -> printf "Store %s\n" v; print_compiled_code tail
      | Remove -> printf "Remove\n"; print_compiled_code tail
      | Plus_op -> printf "Plus_op\n"; print_compiled_code tail
      | Times_op -> printf "Times_op\n"; print_compiled_code tail
      | Sub_op -> printf "Sub_op\n"; print_compiled_code tail
      | Div_op -> printf "Div_op\n"; print_compiled_code tail
      | And_op -> printf "And_op\n"; print_compiled_code tail
      | Or_op -> printf "Or_op\n"; print_compiled_code tail
      | Not_op -> printf "Not_op\n"; print_compiled_code tail
      | Equal_op -> printf "Equal_op\n"; print_compiled_code tail
      | Greater_than_op -> printf "Greater_than_op\n"; print_compiled_code tail
      | If_then_else_op (e1, e2) -> 
        printf "If_then_else_op\n";
        printf "First case\n";
        print_compiled_code e1; 
        printf "Second case\n";
        print_compiled_code e2; 
        printf "if else ends\n";
        print_compiled_code tail
      | Pair_op -> printf "Pair_op\n"; print_compiled_code tail 
      | First_op -> printf "First_op\n"; print_compiled_code tail
      | Second_op -> printf "Second_op\n"; print_compiled_code tail
      | App -> printf "App\n"; print_compiled_code tail
      | Make_closure (x, c) -> 
        printf "Make closure starts\n";
        printf "variable :- %s\n" x;
        printf "function compiled code starts\n";
        print_compiled_code c;
        printf "function code end\n";
        print_compiled_code tail
      | Return -> printf "Return\n" 
    )
;;

let rec search_gamma_table (gamma : gamma_table) v = match gamma with
  | (a, b) :: tail ->
    (
      if ( a = v) then b else (search_gamma_table tail v)
    )
  | [] -> raise Stuck
;;

let rec stkmc gamma (stk : stack) (compiled_opcodes : compiled_code) (dmp : dump) = match stk, compiled_opcodes, dmp with 
  | [v], [], _ -> v
  | s, (Load_int n) :: tail, _-> stkmc gamma ( N n :: s) tail dmp
  | s, (Load_bool b) :: tail, _ -> stkmc gamma (B b :: s) tail dmp
  | s, (Lookup v) :: tail, _ -> stkmc gamma ( (search_gamma_table gamma v) :: s) tail dmp
  | n :: res, (Store v) :: tail, _ -> stkmc ((v, n) :: gamma) res tail dmp 
  | s, (Remove) :: tail , _ -> 
    (match gamma with
     | h :: t -> stkmc t stk tail dmp
     | [] -> raise Stuck)
  | (N n1) :: (N n2) :: res, Plus_op :: tail, _ -> stkmc gamma ( N (n1 + n2) :: res) tail dmp
  | (N n1) :: (N n2) :: res, Times_op :: tail, _ -> stkmc gamma ( N (n1 * n2) :: res) tail dmp
  | (N n1) :: (N n2) :: res, Sub_op :: tail, _ -> stkmc gamma ( N (n2 - n1) :: res) tail dmp
  | (N n1) :: (N n2) :: res, Div_op :: tail, _ -> stkmc gamma ( N (n2 / n1) :: res) tail dmp
  | (B b1) :: (B b2) :: res, And_op :: tail, _ -> stkmc gamma ( B (b1 && b2) :: res) tail dmp
  | (B b1) :: (B b2) :: res, Or_op :: tail, _ -> stkmc gamma ( B (b1 || b2) :: res) tail dmp
  | (B b1) :: res, Not_op :: tail, _ -> stkmc gamma ( B (not b1) :: res) tail dmp
  | (N b1) :: (N b2) :: res, Equal_op :: tail, _ -> stkmc gamma ( B (b1 = b2) :: res) tail dmp
  | (B b1) :: (B b2) :: res, Equal_op :: tail, _ -> stkmc gamma ( B (b1 = b2) :: res) tail dmp
  | (N b1) :: (N b2) :: res, Greater_than_op :: tail, _ -> stkmc gamma ( B (b2 > b1) :: res) tail dmp
  | (B true) :: res, If_then_else_op (c1, c2) :: tail, _ -> stkmc gamma res (c1 @ tail) dmp
  | (B false) :: res, If_then_else_op (c1, c2) :: tail, _ -> stkmc gamma res (c2 @ tail) dmp
  | v1 :: v2 ::s, Pair_op :: tail, _ -> stkmc gamma (P (v2, v1) :: s) tail dmp
  | (P (v1, v2)) :: res, First_op :: tail, _ -> stkmc gamma (v1 :: res) tail dmp
  | (P (v1, v2)) :: res, Second_op :: tail, _ -> stkmc gamma (v2 :: res) tail dmp
  | s, (Make_closure (x, c')) :: c'', d -> stkmc gamma ((Clos (x, c', gamma)) :: s) c'' d
  | a :: (Clos (x, c', y')) :: s, App :: c'', d -> stkmc ( [(x, a)] @ gamma) [] c' ( [s, gamma, c''] @ d)
  | a :: s', Return :: c', ((s, gamma, c'') :: d) -> stkmc gamma ( a :: s) c'' d 

  | _, _, _-> raise Stuck
;;

let rec print_value a = match a with
  | N n -> printf "Answer is a number :- %d\n\n" n
  | B b -> printf "Answer is a boolean :- %B\n\n" b
  | P (v1, v2) -> 
    printf "Answer is a pair :- \n";
    printf "(First element is :- ";
    print_value v1;
    printf "second element is :- ";
    print_value v2;
    printf ")\n"
  | Clos (v, c, env) -> 
    printf "variable %s\n" v;
    print_compiled_code c;
    printf "\n";
    print_gamma_table env

and print_gamma_table g = match g with
  | [] -> ()
  | (var, value) :: tail ->
    printf "Variable %s\n" var;
    print_value value;
    print_gamma_table tail
;;


let gamma : gamma_table = [ ("x", N 1); ("y", N 2) ];;

let test_case = Application(Abstraction("x", Application(Abstraction("y", Var "y"), Var "x")), Var "x");;

let compiled_code = compile test_case;;

printf "\nCompiled code is :- \n";;
print_compiled_code (compiled_code);;

let value = stkmc gamma [] compiled_code [];;
print_value value;;



(* Test cases *)

(* Test Case 1

   let gamma : gamma_table = [];;
   let test_case = Num 54;;

   Compiled code is :- 
   Load_int 54


   Answer is a number :- 54 
*)

(* Test Case 2

   let gamma : gamma_table = [];;
   let test_case = Bool true;;

   Compiled code is :- 
   Load_bool true


   Answer is a boolean :- true
*)

(* Test Case 3

   let gamma : gamma_table = [ ("a1", N 3); ("a2", B false)];;
   let test_case = Var "a1";;

   Compiled code is :- 
   Lookup a1


   Answer is a number :- 3
*)

(* Test Case 4

   let gamma : gamma_table = [ ("a1", N 3); ("a2", B false)];;
   let test_case = Times (Var "a1", Times( Num 43, Plus( Var "a1", Var "a2")));;

   Compiled code is :- 
   Lookup a1
   Load_int 43
   Lookup a1
   Lookup a2
   Plus_op
   Times_op
   Times_op


   Fatal error: exception Main.Stuck
*)

(* Test Case 5

   let gamma : gamma_table = [ ("a1", N 3); ("a2", B false)];;
   let test_case = Times (Var "a1", Times( Num 43, Plus( Var "a1", Num 2)));;

   Compiled code is :- 
   Lookup a1
   Load_int 43
   Lookup a1
   Load_int 2
   Plus_op
   Times_op
   Times_op


   Answer is a number :- 645
*)

(* Test Case 6

   let gamma : gamma_table = [ ("a1", N 3); ("a2", B false)];;
   let test_case = Sub( Num 43, Div( Num 6, Num 3));;

   Compiled code is :- 
   Load_int 43
   Load_int 6
   Load_int 3
   Div_op
   Sub_op


   Answer is a number :- 41
*)

(* Test Case 7

   let gamma : gamma_table = [ ("a1", B true); ("a2", B false)];;
   let test_case = Or(Not(Var "a1"), And(Var "a1", Var "a2"));;

   Compiled code is :- 
   Lookup a1
   Not_op
   Lookup a1
   Lookup a2
   And_op
   Or_op


   Answer is a boolean :- false
*)

(* Test case 8

   let gamma : gamma_table = [ ("a1", N 25); ("a2", N 5)];;
   let test_case = Equal( Plus(Num 10, Var "a1"), Times(Var "a2", Num 7));;

   Compiled code is :- 
   Load_int 10
   Lookup a1
   Plus_op
   Lookup a2
   Load_int 7
   Times_op
   Equal_op


   Answer is a boolean :- true
*)

(* Test Case 9

   let gamma : gamma_table = [ ("a1", N 25); ("a2", N 5)];;
   let test_case = Not ( Greater_than( Var "a1", Var "a2"));;

   Compiled code is :- 
   Lookup a1
   Lookup a2
   Greater_than_op
   Not_op


   Answer is a boolean :- false
*)

(* Test case 10 

   let gamma : gamma_table = [ ("a1", N 25); ("a2", N 5)];;
   let test_case = If_then_else( Equal( Num 5, Num 2), Plus(Var "a1", Num 30), Times(Var "a2", Num 30));;

   Compiled code is :- 
   Load_int 5
   Load_int 2
   Equal_op
   If_then_else_op
   First case
   Lookup a1
   Load_int 30
   Plus_op

   Second case
   Lookup a2
   Load_int 30
   Times_op

   if else ends

   Answer is a number :- 150
*)

(* Test Case 10 

   let gamma : gamma_table = [ ("a1", N 25); ("a2", N 5)];;
   let test_case = If_then_else( Not(Equal( Num 5, Num 2)), Plus(Var "a1", Num 30), Times(Var "a2", Num 30));;

   Compiled code is :- 
   Load_int 5
   Load_int 2
   Equal_op
   Not_op
   If_then_else_op
   First case
   Lookup a1
   Load_int 30
   Plus_op

   Second case
   Lookup a2
   Load_int 30
   Times_op

   if else ends

   Answer is a number :- 55
*)

(* Test Case 11

   let gamma : gamma_table = [ ("a1", N 25); ("a2", N 5)];;
   let test_case = Pair( Plus(Var "a1", Var "a2"), Equal( Var "a1", Var "a2"));;

   Compiled code is :- 
   Lookup a1
   Lookup a2
   Plus_op
   Lookup a1
   Lookup a2
   Equal_op
   Pair_op

   Answer is a pair :- 
   (First element is :- Answer is a number :- 30

   second element is :- Answer is a boolean :- false

   )
*)

(* Test case 12

   let gamma : gamma_table = [ ("a1", N 25); ("a2", N 5)];;
   let test_case = First(Pair( Plus(Var "a1", Var "a2"), Equal( Var "a1", Var "a2")));;

   Compiled code is :- 
   Lookup a1
   Lookup a2
   Plus_op
   Lookup a1
   Lookup a2
   Equal_op
   Pair_op
   First_op

   Answer is a number :- 30
*)

(* Test case 13

   let gamma : gamma_table = [ ("a1", N 25); ("a2", N 5)];;
   let test_case = Second(Pair( Plus(Var "a1", Var "a2"), Equal( Var "a1", Var "a2")));;

   Compiled code is :- 
   Lookup a1
   Lookup a2
   Plus_op
   Lookup a1
   Lookup a2
   Equal_op
   Pair_op
   Second_op

   Answer is a boolean :- false
*)

(* Test case 14

   let gamma : gamma_table = [ ("a1", N 25); ("a2", N 5)];;
   let test_case = Plus( Num 10, Definition("x", Sub(Num 12, Num 9), Times(Var "x", Num 2)));;

   Compiled code is :- 
   Load_int 10
   Load_int 12
   Load_int 9
   Sub_op
   Store x
   Lookup x
   Load_int 2
   Times_op
   Remove
   Plus_op

   Answer is a number :- 16
*)

(* Test case 15

   let gamma : gamma_table = [ ("a1", N 25); ("a2", N 5)];;
   let test_case = Times( Plus( Num 10, Definition("a1", Sub(Num 12, Num 9), Times(Var "a1", Num 2))), Var "a1");;

   Compiled code is :- 
   Load_int 10
   Load_int 12
   Load_int 9
   Sub_op
   Store a1
   Lookup a1
   Load_int 2
   Times_op
   Remove
   Plus_op
   Lookup a1
   Times_op

   Answer is a number :- 400
*)

(* Test case 16

   let gamma : gamma_table = [ ("a1", N 25); ("a2", N 5)];;
   let test_case = Application( Abstraction( "x", Times( Var "x", Num 3)) , Plus( Var "a1", Num 5));;

   Compiled code is :- 
   Make closure starts
   variable :- x
   function compiled code starts
   Lookup x
   Load_int 3
   Times_op
   Return
   function code end
   Lookup a1
   Load_int 5
   Plus_op
   App

   Answer is a number :- 90
*)

(* Test Case 17

   let gamma : gamma_table = [ ("a1", N 25); ("a2", N 5)];;
   let test_case = Abstraction( "x", Times( Var "x", Var "a1"));;

   Compiled code is :- 
   Make closure starts
   variable :- x
   function compiled code starts
   Lookup x
   Lookup a1
   Times_op
   Return
   function code end

   variable x
   Lookup x
   Lookup a1
   Times_op
   Return

   Variable a1
   Answer is a number :- 25

   Variable a2
   Answer is a number :- 5
*)

(* Test case 18

   let gamma : gamma_table = [ ("a1", N 2); ("a2", N 5)];;

   let function1 = Abstraction ( "x", Plus( Var "x", Var "a1"));;
   let function2 = Abstraction( "x", Times( Var "x", Num 5));;
   let test_case = Sub (Application( function1, Num 3), Application( function2, Num 10));;

   Compiled code is :- 
   Make closure starts
   variable :- x
   function compiled code starts
   Lookup x
   Lookup a1
   Plus_op
   Return
   function code end
   Load_int 3
   App
   Make closure starts
   variable :- x
   function compiled code starts
   Lookup x
   Load_int 5
   Times_op
   Return
   function code end
   Load_int 10
   App
   Sub_op

   Answer is a number :- -45
*)

(* Test case 19

   let gamma : gamma_table = [ ("a1", N 2); ("a2", N 5)];;

   let function1 = Abstraction ( "x", Plus( Var "x", Var "a1"));;
   let function2 = Abstraction( "x", Times( Var "x", Num 5));;
   let test_case = Pair (Application( function1, Num 3), Application( function2, Num 10));;\

   Compiled code is :- 
   Make closure starts
   variable :- x
   function compiled code starts
   Lookup x
   Lookup a1
   Plus_op
   Return
   function code end
   Load_int 3
   App
   Make closure starts
   variable :- x
   function compiled code starts
   Lookup x
   Load_int 5
   Times_op
   Return
   function code end
   Load_int 10
   App
   Pair_op

   Answer is a pair :- 
   (First element is :- Answer is a number :- 5

   second element is :- Answer is a number :- 50

   )
*)

(* Test case 20

   let gamma : gamma_table = [ ("a1", N 10); ("a2", N 5)];;

   let function1 = Abstraction ( "x", Plus( Var "x", Var "a1"));;
   let function2 = Abstraction( "x", Times( Var "x", Num 5));;
   let test_case = Application( function1, Application( function2, Num 10));;

   Compiled code is :- 
   Make closure starts
   variable :- x
   function compiled code starts
   Lookup x
   Lookup a1
   Plus_op
   Return
   function code end
   Make closure starts
   variable :- x
   function compiled code starts
   Lookup x
   Load_int 5
   Times_op
   Return
   function code end
   Load_int 10
   App
   App

   Answer is a number :- 60
*)