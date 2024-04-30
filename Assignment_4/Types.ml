type pred = string ;;

type term = 
  | Variable of string
  | Cons of string
  | Func of pred * term list ;;

type atomic_formula = 
  | Normal of pred * term list 
  | Not of pred * term list ;;

type clauses = 
  | Fact of atomic_formula
  | Rule of atomic_formula * atomic_formula list ;;

type program = clauses list ;;