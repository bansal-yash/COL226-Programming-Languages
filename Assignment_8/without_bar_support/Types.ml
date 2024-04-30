type predicate = string ;;

type term = 
  | Variable of string
  | List_variable of string
  | Anonymous_variable
  | Constant of string
  | Function of predicate * (term list)
  | List of term list
  | Tuple of term list
;;

type atomic_formula = 
  | Function of predicate * (term list)
  | Not of atomic_formula
  | Cut
  | Fail
;;

type head = atomic_formula ;;

type body = atomic_formula list ;;

type clause = 
  | Fact of head
  | Rule of head * body
;;

type program = clause list ;;

type goal = atomic_formula list ;;