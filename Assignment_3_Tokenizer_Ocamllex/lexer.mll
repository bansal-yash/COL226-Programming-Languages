{
  let no_of_tokens = ref 0
let no_of_lines = ref 1
let no_of_errors = ref 0
let no_of_char = ref 1

type token = 
  | Integer of int
  | Float of float
  | Character_constant of char
  | String_constant of string
  | Arithmetic_operator of string
  | Assignment_operator of string
  | Comparison_operator of string
  | Logical_operator of string
  | Bitwise_operator of string
  | Boolean_constant of string
  | String_operator of string
  | Identifier of string
  | Comment of string
  | Bracket of string
  | Comma of string
  | Keyword of string

exception Eof
exception Lexical_error of char
exception Character_error of string
exception Identifier_error of string
}

rule token = parse
| [' ' '\t']                            {incr no_of_char; token lexbuf}
| ['\n']                                {incr no_of_lines; no_of_char := 1; token lexbuf}

| "if" | "then" | "else" | "func" | "while" | "do" | "int" | "long" | "float" | "double" | "char" 
| "bool" | "string" | "break" | "pass" | "continue" | "for" | "return" | "define" | "void" 
| "case" | "switch" | "const" | "typedef" | "printf" | "scanf" | ";" as lxm       
{incr no_of_tokens; no_of_char := !no_of_char + String.length lxm; Keyword(lxm)}

| ['0'-'9']+ as lxm                     {incr no_of_tokens; no_of_char := !no_of_char + String.length lxm; Integer(int_of_string lxm)}

| ['0'-'9']+ '.' ['0'-'9']+ as lxm      {incr no_of_tokens; no_of_char := !no_of_char + String.length lxm; Float(float_of_string lxm)}

| ['\''] ([^ '"' '\\'] | '\\' ['"']) * ['\''] as lxm {
    if String.length lxm > 3 then (raise (Character_error lxm))
    else begin
      incr no_of_tokens; no_of_char := !no_of_char + 3; Character_constant(String.get lxm 1)
    end
  }

| ['"'] ([^ '"' '\\'] | '\\' ['"']) * ['"'] as lxm {incr no_of_tokens; no_of_char := !no_of_char + String.length lxm; String_constant(String.sub lxm 1 (String.length lxm - 2))}

| '+' | '-' | '*' | '/' | '%' as lxm    {incr no_of_tokens; no_of_char := !no_of_char + 2; Arithmetic_operator(String.make 1 lxm)}
| "**" | "//" | "++" | "--" as lxm      {incr no_of_tokens; incr no_of_char ; Arithmetic_operator(lxm) }

| '=' as lxm                            {incr no_of_tokens; incr no_of_char; Assignment_operator(String.make 1 lxm)}
| "+=" | "-=" | "*=" | "/=" as lxm      {incr no_of_tokens; no_of_char := !no_of_char + 2; Assignment_operator(lxm)}

| '>' | '<' as lxm                      {incr no_of_tokens; incr no_of_char; Comparison_operator(String.make 1 lxm)}
| "==" | ">=" | "<=" | "!=" as lxm      {incr no_of_tokens; no_of_char := !no_of_char + 2; Comparison_operator(lxm)}

| '!' as lxm                            {incr no_of_tokens; incr no_of_char; Logical_operator(String.make 1 lxm)}
| "&&" | "||" | "<=" | "!=" as lxm      {incr no_of_tokens; no_of_char := !no_of_char + 2; Logical_operator(lxm)}

| '&' | '|' | '^' | '~' as lxm          {incr no_of_tokens; incr no_of_char; Bitwise_operator(String.make 1 lxm)}
| ">>" | "<<" as lxm                    {incr no_of_tokens; no_of_char := !no_of_char + 2; Bitwise_operator(lxm)}

| "True" as lxm                         {incr no_of_tokens; no_of_char := !no_of_char + 4; Boolean_constant(lxm)}
| "False" as lxm                        {incr no_of_tokens; no_of_char := !no_of_char + 5; Boolean_constant(lxm)}

| "^^" as lxm                           {incr no_of_tokens; no_of_char := !no_of_char + 3; String_operator(lxm)}

| ['a'-'z' '_'] ['a'-'z' 'A' - 'Z' '0'-'9' '_' '\'']* as lxm    { incr no_of_tokens; no_of_char := !no_of_char + String.length lxm; Identifier(lxm) }
| ['0' - '9' 'A' - 'Z']+ ['a'-'z' 'A' - 'Z' '0'-'9' '_' ]* as lxm    { raise (Identifier_error lxm) }

| ['#'] ([^ '#' '\\'] | '\\' ['#']) * ['#']  as lxm {incr no_of_tokens; no_of_char := !no_of_char + String.length lxm; Comment(String.sub lxm 1 (String.length lxm - 2))}

| '(' | ')' | '[' | ']' | '{' | '}' as lxm                      {incr no_of_tokens; incr no_of_char; Bracket(String.make 1 lxm)}

| ',' as lxm                            {incr no_of_tokens; incr no_of_char; Comma(String.make 1 lxm)}

| eof                                   {raise Eof}
| _    as itr                           {raise (Lexical_error itr)}

  {
    let main () =
      let out = open_out "output.txt" in
      try 
        let file_name = Sys.argv.(1) in
        let input_file = open_in file_name in 
        let lexbuf = Lexing.from_channel input_file in
        while true do
          try 
            let result = token lexbuf in 
            match result with 

            | Integer(i) -> 
              Printf.fprintf out "%d : Integer Constant\n" i;

            | Float(i) -> 
              Printf.fprintf out "%f : Float Constant\n" i;

            | String_constant(i) -> 
              Printf.fprintf out "%s : String Constant\n" i;

            | Character_constant(i) -> 
              Printf.fprintf out "%c : Character Constant\n" i;

            | Arithmetic_operator(i) -> 
              Printf.fprintf out "%s : Arithmetic Operator\n" i;

            | Assignment_operator(i) -> 
              Printf.fprintf out "%s : Assignment Operator\n" i;

            | Comparison_operator(i) ->
              Printf.fprintf out "%s : Comparison Operator\n" i;

            | Logical_operator(i) ->
              Printf.fprintf out "%s : Logical Operator\n" i;

            | Bitwise_operator(i) ->
              Printf.fprintf out "%s : Bitwise Operator\n" i;

            | Boolean_constant(i) ->
              Printf.fprintf out "%s : Boolean Constant\n" i;

            | String_operator(i) ->
              Printf.fprintf out "%s : String Operator\n" i;

            | Identifier(i) ->
              Printf.fprintf out "%s : Identifier\n" i;

            | Comment(i) ->
              Printf.fprintf out "%s : Comment\n" i;

            | Bracket(i) -> 
              Printf.fprintf out "%s : Bracket\n" i;

            | Comma(i) -> 
              Printf.fprintf out "%s : Comma\n" i;

            | Keyword(i) ->
              Printf.fprintf out "%s : Keyword\n" i;

          with 
          | Lexical_error(i) ->
            Printf.fprintf out "%c : error" i;
            Printf.fprintf out " in line number :- %d" !no_of_lines;
            Printf.fprintf out " Character number :- %d\n" !no_of_char;
            incr no_of_char;
            incr no_of_errors;

          | Character_error(i) ->
            Printf.fprintf out "%s : error" i;
            Printf.fprintf out " in line number :- %d" !no_of_lines;
            Printf.fprintf out " Character number :- %d\n" !no_of_char;
            no_of_char := !no_of_char + 3;
            incr no_of_errors;

          | Identifier_error(i) ->
            Printf.fprintf out "%s : error" i;
            Printf.fprintf out " in line number :- %d" !no_of_lines;
            Printf.fprintf out " Character number :- %d\n" !no_of_char;
            no_of_char := !no_of_char + String.length i;
            incr no_of_errors;

        done 
      with 
      | Eof -> 
        Printf.fprintf out "\nNumber of lines: %d\n" !no_of_lines;
        Printf.fprintf out "Number of tokens: %d\n" !no_of_tokens;
        Printf.fprintf out "Number of errors: %d" !no_of_errors;
        close_out out;
        exit 0
;;
main();;
}

(* Test Case 1

int main() {
    int a = 5;
    float b = 3.14;
    if (a > 0) {
        printf("Hello");
    }
    else {
        printf("World");
    }
    return 0;
}

 *)

(*  Test Case 2

string s = "Hello, world!";
a = b + c * d / 5 - 10 % 3;
a += 5;
b -= 3.5;
if (x == 5 && y >= 10) then
    printf("Hello");

 *)

(* Test Case 3

if (!flag || (x < 0 && y > 0)) then
    printf("World");
int result = x & y | ~z;
bool isTrue = True;
bool isFalse = False;
int myVariable = 42;
func myFunction() {
    return;
}

 *)

(* Test Case 4

for (int i = 0; i < 10; i++) {
    array[i] = i * 2;
}
$%^&@
int x = 123abc;

 *)