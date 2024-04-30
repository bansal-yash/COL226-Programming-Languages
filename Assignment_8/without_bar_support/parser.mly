%{
    open Types
%}

%token <string> Constant
%token <string> Predicate_or_constant
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


%start program
%start goal

%type <Types.program> program
%type <Types.goal> goal

%%

program:
|   clause program                          { ($1) :: ($2) }
|   EOF                                     { ([] : program) }

clause:
|   head End_of_clause                      { Fact($1) }
|   head Turnstile body End_of_clause       { Rule($1, $3) }

head:
|   atomic_formula                          { ($1) : atomic_formula }

body:
|   atomic_formula Comma body               { ($1) :: ($3) }
|   atomic_formula                          { [($1)] : atomic_formula list }
|   Not atomic_formula Comma body           { Not($2) :: ($4) }
|   Not atomic_formula                      { [Not($2)] : atomic_formula list }

atomic_formula:
|   Fail                                                                        { Fail }
|   Predicate_or_constant Left_paren terms_list Right_paren                     { Function($1, $3) }
|   Predicate_or_constant Left_paren Right_paren                                { Function($1, []) }
|   Cut                                                                         { Cut }

terms_list:
|   term Comma terms_list                                                       { ($1) :: ($3) }
|   term                                                                        { [($1)] : term list }

term:
|   Variable                                                                    { Variable($1) }
|   Anonymous_variable                                                          { Anonymous_variable }
|   Constant                                                                    { Constant($1) }
|   Predicate_or_constant                                                       { Constant($1) }
|   Predicate_or_constant Left_paren terms_list Right_paren                     { Function($1, $3) }
|   Predicate_or_constant Left_paren Right_paren                                { Function($1, []) }
|   Left_paren terms_list Right_paren                                           { Tuple($2) }
|   list                                                                        { List($1) }

list:
|   Left_square_bracket terms_list Right_square_bracket                         { ($2) }
|   Left_square_bracket terms_list Bar Variable Right_square_bracket            { ($2) @ [List_variable($4)]}
|   Left_square_bracket Right_square_bracket                                    { ([] : term list) }


goal:
|   subgoal_list End_of_clause              { ($1) }   

subgoal_list:
|   subgoal Comma subgoal_list              { ($1) :: ($3) }
|   subgoal                                 { [$1] : goal }
|   Not subgoal Comma subgoal_list           { Not($2) :: ($4) }
|   Not subgoal                      { [Not($2)] : goal }

subgoal:
|   atomic_formula                          { ($1) : atomic_formula }

%%