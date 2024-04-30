%{
    open Types
%}

%token <string> Built_in_predicate
%token <string> Integer
%token <string> Float
%token <string> String_constant
%token <string> Arithmetic_operator
%token <string> Comparison_operator
%token <string> Logical_operator
%token <string> Bitwise_operator
%token <string> Boolean_constant
%token <string> Assignment_operator
%token <string> Predicate
%token <string> Variable
%token Left_paren
%token Right_paren
%token Left_square_bracket
%token Right_square_bracket
%token End_of_clause
%token Turnstile
%token Fail
%token Cut
%token Bar
%token Comma
%token Not
%token Anonymous_variable
%token EOF

%nonassoc Comparison_operator
%nonassoc Assignment_operator

%start main
%type <Types.program> main

%%

main:
|   clause main     { [($1)] @ ($2) }
|   EOF             { [] }
                        
clause:
|   head End_of_clause                      { Fact($1) }
|   head Turnstile body End_of_clause       { Rule($1, $3) }

head:
|   atomic_formula                          { ($1) }

body:
|   atomic_formula Comma body               { [Normal]}
|   atomic_formula                          { [Normal($1)] }
|   Not atomic_formula Comma body           { [Not($2)] @ ($4)}
|   Not atomic_formula                      { [Not($2)] }

atomic_formula:
|   Predicate Left_paren terms Right_paren  { ($1, $3) }

terms:
|   Variable Comma terms                    { [Variable($1)] @ ($3)}
|   String_constant Comma terms             { [Cons($1)] @ ($3)}
|   Predicate Left_paren terms Right_paren Comma terms { [Func($1, $3)] @ ($6)}
|   Variable                                { [Variable($1)]}
|   String_constant                         { [Cons($1)]}
|   Predicate Left_paren terms Right_paren  { [Func($1, $3)]}