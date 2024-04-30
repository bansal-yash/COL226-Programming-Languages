open Lexer
open Types
open Printf

let no_of_clause = ref 1 ;;
let out = open_out "output.txt";;

let rec print_terms term_list = 
  match term_list with
    | [] -> ()
    | Variable var :: rest -> 
      Printf.fprintf out "Variable:- %s\n" var;
      print_terms rest
    | Cons constant :: rest -> 
      Printf.fprintf out "Constant:- %s\n" constant;
      print_terms rest
    | Func (predi, terms_list1) :: rest->
      Printf.fprintf out "Predicate:- %s\n" predi;
      print_terms terms_list1;
      print_terms rest

let rec print_atomic_form atomic_form =
  match atomic_form with
    | Normal (predi, term_list1) ->
        Printf.fprintf out "Predicate:- %s\n" predi;
        print_terms term_list1
    | Not (predi, term_list1) ->
        Printf.fprintf out "Not predicate:- %s\n" predi;
        print_terms term_list1

let rec print_body body = 
  match body with 
    | [] -> ()
    | atomic_form :: rest ->
      print_atomic_form atomic_form;
      print_body rest

let rec print_clause clause =
  match clause with
  | Fact atomic_form -> 
    Printf.fprintf out "Fact:- \n";
    print_atomic_form atomic_form;
    Printf.fprintf out "\n"
  | Rule (head, body) -> 
    Printf.fprintf out "Rule:- \n";
    Printf.fprintf out "Head:- \n";
    print_atomic_form head;
    Printf.fprintf out "Body:- \n";
    print_body body;
    Printf.fprintf out "\n"
    
let rec print_ast ast =
  match ast with
  | [] -> ()
  | clause :: rest ->
    Printf.fprintf out "Clause number:- %d\n" !no_of_clause;
    no_of_clause := !no_of_clause + 1;
    print_clause clause;
    print_ast rest

let () =
  let file_name = Sys.argv.(1) in
  let input_file = open_in file_name in
  let lexbuf = Lexing.from_channel input_file in
  let result = Parser.main Lexer.token lexbuf in
  let _ = print_ast result in
  print_string "\ndone\n"
