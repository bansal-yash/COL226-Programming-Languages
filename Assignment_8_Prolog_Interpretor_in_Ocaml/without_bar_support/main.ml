open Types
open Printf

exception Incorrect_program_specification
exception List_variable_not_supported
exception MGU_not_exist
exception Not_printable

(* let rec print_tree t to_print = match t with
  | Variable v ->  if (List.mem v to_print) then printf " (Variable:- %s) " v else ()
  | Constant c -> printf " (Constant :- %s) \n" c 
  | _ -> ()
;;

let rec print_substitution s to_print= match s with
  | [] -> printf "\n"
  | (a,b) :: tail ->
    printf "Variable :- %s\n" a;
    print_tree b to_print;
    printf "\n";
    print_substitution tail to_print;
;;

let rec print_tree_comp t = match t with
  | Variable v ->  printf " (Variable:- %s) " v
  | Constant c -> printf " (Constant :- %s) \n" c
  | _ -> ()
;;

let rec print_substitution_comp s= match s with
  | [] -> printf "\n"
  | (a,b) :: tail ->
    printf "Variable :- %s\n" a;
    print_tree_comp b;
    printf "\n";
    print_substitution_comp tail;
;; *)

let rec vars t = match t with
  | Variable v -> [v]
  | List_variable v -> raise List_variable_not_supported
  | Anonymous_variable -> []
  | Constant s -> []
  | Function (_, tl) -> List.fold_left (@) [] (List.map vars tl)
  | List tl -> List.fold_left (@) [] (List.map vars tl)
  | Tuple tl -> List.fold_left (@) [] (List.map vars tl)
;;

let rec vars_af af = match af with
  | Function (p, tl) -> List.fold_left (@) [] (List.map vars tl)
  | Not af1 -> vars_af af1
  | Cut | Fail -> []
;;

let var_cl cl = match cl with
  | Fact hd -> vars_af hd
  | Rule (hd, bd) -> (vars_af hd) @ ( List.fold_left (@) [] (List.map vars_af bd))
;;

let rec find_list_subs element ls = match ls with 
  | [] -> Variable element
  | (var, tree) :: tail -> 
    if var = element then tree else find_list_subs element tail
;;

let rec substitute given_substitutions t = match t with
  | Variable x -> find_list_subs x given_substitutions
  | List_variable v -> raise List_variable_not_supported
  | Anonymous_variable -> Anonymous_variable
  | Constant s -> Constant s
  | Function (p, tl) -> Function (p, List.map (substitute given_substitutions) tl)
  | List tl -> List (List.map (substitute given_substitutions) tl)
  | Tuple tl -> Tuple (List.map (substitute given_substitutions) tl)
;;

let rec mem_subs (element : string) (ls : (string * term) list) = match ls with 
  | [] -> false
  | (var, tree) :: tail -> 
    if var = element then true else mem_subs element tail
;; 

let rec not_common ( s1 : (predicate * term) list) s2 = match s2 with
  | [] -> []
  | head :: tail ->
    if mem_subs (fst head) s1 then not_common s1 tail else head :: (not_common s1 tail)

let rec comp_subs_helper s s1 s2 = match s1 with
  | [] -> not_common s s2
  | (a,b) :: tail -> (a, substitute s2 b) :: comp_subs_helper s tail s2
;;

let rec comp_subs s1 s2 = comp_subs_helper s1 s1 s2;;

let rec mgu_term (term1 : Types.term) (term2 : Types.term) initial_sub = match term1 with
  | Variable v1 -> (
      match term2 with
      | Variable v2  -> if v1 = v2 then [] else [ (v1, Variable v2)]
      | List_variable v2 -> raise List_variable_not_supported
      | Anonymous_variable -> initial_sub
      | Constant c -> [(v1, Constant c)]
      | Function (p, tl) -> if (List.mem v1 (vars term2)) then raise MGU_not_exist else [(v1, term2)]
      | List tl -> if (List.mem v1 (vars term2)) then raise MGU_not_exist else [(v1, term2)]
      | Tuple tl -> if (List.mem v1 (vars term2)) then raise MGU_not_exist else [(v1, term2)]
    )

  | List_variable v1 -> raise List_variable_not_supported
  | Anonymous_variable -> initial_sub
  | Constant c1 -> (
      match term2 with
      | Variable v2 -> [ (v2, term1)]
      | Anonymous_variable -> initial_sub
      | Constant c2 -> if (c1 = c2) then [] else raise MGU_not_exist
      | _ -> raise MGU_not_exist 
    )
  | Function (p1, t1) -> (
      match term2 with
      | Variable v2  -> if (List.mem v2 (vars term1)) then raise MGU_not_exist else [(v2, term1)]
      | List_variable v2 -> raise List_variable_not_supported
      | Anonymous_variable -> initial_sub
      | Constant c -> raise MGU_not_exist
      | Function (p2, t2) -> (
          if ( (p1 = p2) && ((List.length t1) = (List.length t2))) then (
            let rec mgu_term_helper c1 c2 curr_sub = match (c1, c2) with
              | ([], []) -> curr_sub
              | (head1 :: tail1, head2 :: tail2) ->(
                  try
                    let curr_mgu = (mgu_term (substitute curr_sub head1) (substitute curr_sub head2) initial_sub) in
                    let new_subs = comp_subs curr_sub curr_mgu in
                    mgu_term_helper tail1 tail2 new_subs
                  with
                    MGU_not_exist -> raise MGU_not_exist
                )
              | (_, _) -> raise MGU_not_exist
            in (
              try
                let x = mgu_term_helper t1 t2 initial_sub in x
              with 
                MGU_not_exist -> raise MGU_not_exist
            )
          )
          else (
            raise MGU_not_exist
          )
        )
      | List tl -> raise MGU_not_exist
      | Tuple tl -> raise MGU_not_exist
    )
  | List tl1 -> (
      match term2 with
      | Variable v2  -> raise MGU_not_exist
      | List_variable v2 -> raise List_variable_not_supported
      | Anonymous_variable -> initial_sub
      | Constant c -> raise MGU_not_exist
      | Function (p, tl) -> raise MGU_not_exist
      | List tl2 -> (
          if ((List.length tl1) = (List.length tl2)) then (
            let rec mgu_term_helper c1 c2 curr_sub = match (c1, c2) with
              | ([], []) -> curr_sub
              | (head1 :: tail1, head2 :: tail2) ->(
                  try
                    let curr_mgu = (mgu_term (substitute curr_sub head1) (substitute curr_sub head2) initial_sub) in
                    let new_subs = comp_subs curr_sub curr_mgu in
                    mgu_term_helper tail1 tail2 new_subs
                  with
                    MGU_not_exist -> raise MGU_not_exist
                )
              | (_, _) -> raise MGU_not_exist
            in (
              try
                let x = mgu_term_helper tl1 tl2 initial_sub in x
              with 
                MGU_not_exist -> raise MGU_not_exist
            )
          )
          else (
            raise MGU_not_exist
          )
        )
      | Tuple tl -> raise MGU_not_exist
    )
  | Tuple tl1 -> (
      match term2 with
      | Variable v2  -> raise MGU_not_exist
      | List_variable v2 -> raise List_variable_not_supported
      | Anonymous_variable -> initial_sub
      | Constant c -> raise MGU_not_exist
      | Function (p, tl) -> raise MGU_not_exist
      | List tl -> raise MGU_not_exist
      | Tuple tl2 -> (
          if ((List.length tl1) = (List.length tl2)) then (
            let rec mgu_term_helper c1 c2 curr_sub = match (c1, c2) with
              | ([], []) -> curr_sub
              | (head1 :: tail1, head2 :: tail2) ->(
                  try
                    let curr_mgu = (mgu_term (substitute curr_sub head1) (substitute curr_sub head2) initial_sub) in
                    let new_subs = comp_subs curr_sub curr_mgu in
                    mgu_term_helper tail1 tail2 new_subs
                  with
                    MGU_not_exist -> raise MGU_not_exist
                )
              | (_, _) -> raise MGU_not_exist
            in (
              try
                let x = mgu_term_helper tl1 tl2 initial_sub in x
              with 
                MGU_not_exist -> raise MGU_not_exist
            )
          )
          else (
            raise MGU_not_exist
          )
        )

    )
;;

let rec mgu_atomic_formula (atfm1 : Types.atomic_formula) (atfm2 : Types.atomic_formula) initial_sub = match (atfm1, atfm2) with
  | ( Function(p1, t1), Function(p2, t2) ) ->(
      if ( (p1 = p2) && ((List.length t1) = (List.length t2))) then (
        let rec mgu_atomic_helper c1 c2 curr_sub = match (c1, c2) with
          | ([], []) -> curr_sub
          | (head1 :: tail1, head2 :: tail2) ->(
              try
                let curr_mgu = (mgu_term (substitute curr_sub head1) (substitute curr_sub head2) curr_sub) in
                let new_subs = comp_subs curr_sub curr_mgu in
                mgu_atomic_helper tail1 tail2 new_subs
              with
                MGU_not_exist -> raise MGU_not_exist
            )
          | (_, _) -> raise MGU_not_exist
        in (
          try
            let x = mgu_atomic_helper t1 t2 initial_sub in (true, x)
          with 
            MGU_not_exist -> (false, [])
        )
      )
      else (
        (false, [])
      )
    )
  | ( Not(r1), _) -> (
      let (a, b) = mgu_atomic_formula r1 atfm2 initial_sub in
      if (a = true) then ( false, []) else (true, b)
    )
  | (Cut, _) -> (true, initial_sub)
  | (Fail, _) -> (false, [])
  | (_, _) -> raise Incorrect_program_specification
;;    

let rec solve_subgoal (program : Types.program) (curr_program : Types.program) (subgoal : Types.atomic_formula) curr_solution = match curr_program with
  | [] -> (false, [])
  | Fact(f) :: rest ->
    let (x, y) = mgu_atomic_formula subgoal f curr_solution in
    if x = false then solve_subgoal program rest subgoal curr_solution else (true, y)
  | Rule(f, b) :: rest -> 
    let (x, y) = mgu_atomic_formula subgoal f curr_solution in
    if x = false then solve_subgoal program rest subgoal curr_solution
    else solve_main program program b y

and solve_main (program : Types.program) (curr_program : Types.program) (goal : Types.goal) curr_solution = match goal with
  | [] -> (true, curr_solution)
  | subgoal1 :: rest -> 
    let (x , new_ans) = solve_subgoal program curr_program subgoal1 curr_solution in
    if x = false then (false, []) 
    else (
      solve_main program curr_program rest new_ans
    )
;;



let input_prolog_program = open_in Sys.argv.(1);;
let input_goal = open_in Sys.argv.(2);;
let parsed_prolog_program = Parser.program Lexer.token (Lexing.from_channel input_prolog_program);;
let parsed_goal = Parser.goal Lexer.token (Lexing.from_channel input_goal);;

printf "\nProgram and goal parsed successfully\n";;

let var_to_print = List.fold_left (@) [] (List.map vars_af parsed_goal);;

let rec print_var_to_print v = match v with 
| [] -> printf "\n"
| hd :: tl -> printf "%s " hd; print_var_to_print tl
;;

print_var_to_print var_to_print;;

let rec print_ans (answer : (string * term) list) to_print= match answer with
  | [] -> ()
  | (v, s) :: rest -> if (List.mem v to_print) then 
      ( match s with
          Variable v2 -> ()
        | List_variable v2 -> raise List_variable_not_supported
        | Anonymous_variable -> ()
        | Constant c -> (
            printf "%s = " v;
            printf "%s\n" c;
            print_ans rest var_to_print
          )
        | Function (p, tl) ->  (* aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa to implement *) ()
        | List tl -> (
            printf "%s = " v;
            let rec print_list l = match l with
              | [] -> ()
              | (Constant c) :: [] -> printf "%s " c
              | (Constant c) :: rst -> printf "%s ," c; print_list rst
              | _ :: rst -> raise Not_printable
            in
            printf "[ "; print_list tl; printf " ]\n";
            print_ans rest var_to_print
          )
        | Tuple tl -> (
            printf "%s = " v;
            let rec print_tuple l = match l with
              | [] -> ()
              | (Constant c) :: [] -> printf "%s " c
              | (Constant c) :: rst -> printf "%s ," c; print_tuple rst
              | _ :: rst -> raise Not_printable
            in
            printf "( "; print_tuple tl; printf " )\n";
            print_ans rest var_to_print
          )
      )
    else print_ans rest var_to_print
;;

let (x, y) = solve_main parsed_prolog_program parsed_prolog_program parsed_goal [];;

printf "\nsolved, now printing\n";;

if x = true then(
  printf "\ntrue\n";
  print_ans y var_to_print;
  printf "\n"
)
else printf "\nfalse\n\n";;
