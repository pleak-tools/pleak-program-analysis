%{
open Syntax
%}
%token <string> IDENT
%token <int> INT
%token <float> FLOAT
%token LPAREN RPAREN LBRACK RBRACK
%token ASSIGN
%token PLUS TIMES LE EQ
%token QUESTION COLON
%token LAPLACE INPUT
%token SUM
%token REPEAT END
%token EOL EOF
%token ADDVARINTERVAL ADDSCALARDIST ADDVECDIST PRINTDIFFPRIVDIST PRINTVECDIST
%nonassoc LE EQ
%left PLUS
%left TIMES
%nonassoc SUM
%start prog
%type <Syntax.fullProg> prog
%%
prog: header subprog footer EOF { ($1,$2,$3) }
subprog: rev_prog { List.rev $1 }
rev_prog:
    | { [] }
    | rev_prog EOL { $1 }
    | rev_prog stmt EOL { $2 :: $1 }
    ;
stmt:
    | IDENT ASSIGN expr { Let ($1,$3) }
    | IDENT LBRACK INT COLON INT RBRACK ASSIGN expr { LetSlice ($1,$3,$5,$8) }
    | REPEAT expr EOL subprog END { Repeat ($2,$4) }
    ;
floatorint:
    | INT { float_of_int $1 }
    | FLOAT { $1 }
    ;
expr:
    | IDENT { V $1 }
    | IDENT LBRACK INT COLON INT RBRACK { Slice ($1,$3,$5) }
    | floatorint { C $1 }
    | LPAREN expr RPAREN { $2 }
    | expr PLUS expr { Add ($1,$3) }
    | expr TIMES expr { Mul ($1,$3) }
    | expr LE expr { Le ($1,$3) }
    | expr EQ expr { Eq ($1,$3) }
    | expr QUESTION expr COLON expr { IfThenElse ($1,$3,$5) }
    | SUM expr { Sum $2 }
    | LAPLACE LPAREN RPAREN { Laplace }
    | INPUT LPAREN RPAREN { Input }
    ;
ident_list: rev_ident_list { List.rev $1 }
rev_ident_list:
    | { [] }
    | rev_ident_list IDENT { $2 :: $1 }
    ;
header_decl:
    | ADDVARINTERVAL IDENT floatorint floatorint { AddVarInterval ($2,$3,$4) }
    | ADDSCALARDIST IDENT floatorint { AddScalarDist ($2,$3) }
    | ADDVECDIST ident_list floatorint { AddVecDist ($2,$3) }
    ;
footer_decl:
    | PRINTDIFFPRIVDIST ident_list { PrintDiffPrivDist $2 }
    | PRINTVECDIST ident_list { PrintVecDist $2 }
    ;
header: rev_header { List.rev $1 }
rev_header:
    | { [] }
    | rev_header EOL { $1 }
    | rev_header header_decl EOL { $2 :: $1 }
    ;
footer: rev_footer { List.rev $1 }
rev_footer:
    | { [] }
    | rev_footer EOL { $1 }
    | rev_footer footer_decl EOL { $2 :: $1 }
    ;
