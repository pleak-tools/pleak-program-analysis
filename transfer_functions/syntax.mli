open Apron

type expr
    = V of string
    | Slice of string * int * int
    | C of float
    | Add of expr * expr
    | Mul of expr * expr
    | Laplace
    | Le of expr * expr
    | Eq of expr * expr
    | IfThenElse of expr * expr * expr
    | Sum of expr
    (*
    | And of expr * expr
    | Not of expr
    *)
    | Input
    (* the following are used only internally *)
    | Sub of expr * expr
    | Div of expr * expr
    | Interval of float * float
    | ScalarInterval of Scalar.t * Scalar.t

type statement
    = Let of string * expr
    | LetSlice of string * int * int * expr
    | Repeat of expr * program
and program = statement list

type headerDecl
    = AddVarInterval of string * float * float
    | AddScalarDist of string * float
    | AddVecDist of string list * float

type header = headerDecl list

type footerDecl
    = PrintDiffPrivDist of string list
    | PrintVecDist of string list

type footer = footerDecl list

type fullProg = header * program * footer
