{
open Parser
exception Lexical_error of char
exception Identifier_error of string
}

rule token = parse

| [' ' '\t' '\n']
| ['%'] ([^ '\n']) * ['\n'] 
| "/*" ( [ ^ '*'] | "*" + [ ^ '/'])* "*/"                       { token lexbuf }

| "fail"                                                        { Fail }

| "true" | "false" as lxm                                       { Constant(lxm) }

| ['0'-'9']+ as lxm                                             { Constant(string_of_int (int_of_string lxm)) }

| ['"'] ([^ '"']) * ['"']            
| ['''] ([^ ''']) * ['''] as lxm                                { Constant(String.sub lxm 1 (String.length lxm - 2)) }

| ['a'-'z'] ['a'-'z' 'A' - 'Z' '0'-'9' '_' '-']* as lxm         { Predicate_or_constant(lxm) }

| ['A'-'Z' '_'] ['a'-'z' 'A' - 'Z' '0'-'9' '_' '-']* as lxm     { Variable(lxm) }

| '('                                                           { Left_paren }
| ')'                                                           { Right_paren }

| '['                                                           { Left_square_bracket }
| ']'                                                           { Right_square_bracket }

| '.'                                                           { End_of_clause }
| ":-"                                                          { Turnstile }
| '!'                                                           { Cut }
| '|'                                                           { Bar }
| ','                                                           { Comma }
| "\\+"                                                         { Not }
| '_'                                                           { Anonymous_variable }
| eof                                                           { EOF }

| _ as rest                                                     { raise (Lexical_error rest) }
| ['0' - '9']+ ['a'-'z' 'A' - 'Z' '0'-'9' '_' ]* as lxm         { raise (Identifier_error lxm) }
