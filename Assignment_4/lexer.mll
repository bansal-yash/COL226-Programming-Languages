{
open Parser
exception Lexical_error of char
exception Identifier_error of string
}

rule token = parse
| [' ' '\t' '\n']                                           { token lexbuf }

| ['%'] ([^ '\n']) * ['\n'] 
| "/*" ( [ ^ '*'] | "*" + [ ^ '/'])* "*/"                   { token lexbuf }

| "write" | "append" | "read" | "number" | "integer" 
| "abs" 
| "float" | "atomic" | "length" | "member" | "not"  as lxm  { Built_in_predicate(lxm) }

| ['0'-'9']+ as lxm                                         { Integer(lxm) }

| ['0'-'9']+ '.' ['0'-'9']+ as lxm                          { Float(lxm) }

| ['"'] ([^ '"']) * ['"']            
| ['''] ([^ ''']) * ['''] as lxm                            { String_constant(String.sub lxm 1 (String.length lxm - 2)) }

| '+' | '-' | '*' | '/' | '%' | "//" | "^" | "mod" as lxm   { Arithmetic_operator(lxm) }

| '>' | '<' | "=:=" | ">=" | "=<" | "=\\=" 
| "==" | "\\==" as lxm                                      { Comparison_operator(lxm) }

| "\\/" | "/\\" | "xor" | "<<" | ">>" as lxm                { Bitwise_operator(lxm) }

| "true" | "false" as lxm                                   { Boolean_constant(lxm) }

| ['a'-'z'] ['a'-'z' 'A' - 'Z' '0'-'9' '_']* as lxm         { Predicate(lxm) }

| ['A'-'Z' '_'] ['a'-'z' 'A' - 'Z' '0'-'9' '_']* as lxm     { Variable(lxm) }

| "is" | "=" as lxm                                         { Assignment_operator(lxm) }

| '('                                                       { Left_paren }
| ')'                                                       { Right_paren }

| '['                                                       { Left_square_bracket }
| ']'                                                       { Right_square_bracket }

| '.'                                                       { End_of_clause }
| ":-"                                                      { Turnstile }
| "fail"                                                    { Fail }
| '!'                                                       { Cut }
| '|'                                                       { Bar }
| ','                                                       { Comma }
| "\\+"                                                     { Not }
| '_'                                                       { Anonymous_variable }
| eof                                                       { EOF }

| _    as itr                                               { raise (Lexical_error itr) }
| ['0' - '9']+ ['a'-'z' 'A' - 'Z' '0'-'9' '_' ]* as lxm     { raise (Identifier_error lxm) }