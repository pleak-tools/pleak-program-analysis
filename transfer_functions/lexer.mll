{
open Myparser
}
let digit = ['0'-'9']
let newline = '\n' | '\r' | "\r\n"
let nonnewline = [^ '\n' '\r']
rule token = parse
    | [' ' '\t'] { token lexbuf }
    | newline { EOL }
    | '#' nonnewline* newline { EOL }
    | digit+ '.' digit* as lxm { FLOAT(float_of_string lxm) }
    | digit+ as lxm { INT(int_of_string lxm) }
    | "AddVarInterval" { ADDVARINTERVAL }
    | "AddScalarDist" { ADDSCALARDIST }
    | "AddVecDist" { ADDVECDIST }
    | "PrintDiffPrivDist" { PRINTDIFFPRIVDIST }
    | "PrintVecDist" { PRINTVECDIST }
    | "Laplace" { LAPLACE }
    | "Input" { INPUT }
    | "Sum" { SUM }
    | "Repeat" { REPEAT }
    | "End" { END }
    | ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']* as ident { IDENT(ident) }
    | '(' { LPAREN }
    | ')' { RPAREN }
    | '[' { LBRACK }
    | ']' { RBRACK }
    | '+' { PLUS }
    | '*' { TIMES }
    | "<=" { LE }
    | "=" { EQ }
    | ":=" { ASSIGN }
    | '?' { QUESTION }
    | ':' { COLON }
    | eof { EOF }
