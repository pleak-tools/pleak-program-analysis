open Apron
open Format

type expr
  = V of string
  | C of float
  | Add of expr * expr
  | Mul of expr * expr
  | Laplace
  | Le of expr * expr
  | Eq of expr * expr
  | And of expr * expr
  | Not of expr
  | Input
  (* the following are used only internally *)
  | Sub of expr * expr
  | Interval of float * float

type statement
  = Let of string * expr

type program = statement list


let rec print_expr expr =
    match expr with
    | V x -> print_string x
    | C r -> print_float r
    | Add (e1,e2) -> print_char '('; print_expr e1; print_string " + "; print_expr e2; print_char ')'
    | Sub (e1,e2) -> print_char '('; print_expr e1; print_string " - "; print_expr e2; print_char ')'
    | Mul (e1,e2) -> print_char '('; print_expr e1; print_string " * "; print_expr e2; print_char ')'
    | Laplace -> print_string "Laplace()"
    | Le (e1,e2) -> print_char '('; print_expr e1; print_string " <= "; print_expr e2; print_char ')'
    | Eq (e1,e2) -> print_char '('; print_expr e1; print_string " == "; print_expr e2; print_char ')'
    | And (e1,e2) -> print_char '('; print_expr e1; print_string " && "; print_expr e2; print_char ')'
    | Not e1 -> print_char '!'; print_expr e1
    | Input -> print_string "Input()"
    | Interval (r1,r2) -> print_char '['; print_float r1; print_char ','; print_float r2; print_char ']'


let print_statement st =
    match st with
    | Let (x,expr) -> print_string x; print_string " := "; print_expr expr; print_newline ()



let example = [
    Let ("i", Input);
    Let ("j", Input);
    Let ("z", Laplace);
    Let ("x", Mul (C 2.0,V "z"));
    Let ("y", Add (V "z",C 3.0));
    Let ("w", V "x");
    Let ("a", C 2.0);
    Let ("b", Mul (V "a", V "a"));
    Let ("a", C 3.0);
    Let ("c", Le (Add (V "x", C 4.0), Add (V "w", C 3.0)));
    Let ("q", Mul (V "z", V "b"));
    Let ("r", Add (V "q", V "a"));
    Let ("d", Eq (V "i", V "j"))
    (*Let ("b", Mul (V "a", V "x"))*)
]

let vExp x = String.concat "" ["E";x]
let vVar x = String.concat "" ["V";x]

let example_vars = List.(sort_uniq compare (map (fun (Let (x, _)) -> x) example))
let example_vars2 = example_vars @ List.map vExp example_vars @ List.map vVar example_vars
let _ = List.iter print_string example_vars2; print_newline ()

(*let vararr = [|"x";"y";"w";"z";"a";"b";"c"|]*)
let vararr = Array.of_list example_vars2
let env = Environment.make [||] (Array.map Var.of_string vararr)
(*let mgr = Polka.manager_alloc_equalities ()*)
(*let mgr = Polka.manager_alloc_loose ()*)
let mgr = Ppl.manager_alloc_loose ()

module StringSet = Set.Make(String)

let astateRef = ref (Abstract1.top mgr env)
let isLaplaceRef = ref StringSet.empty

let expr2texpr expr =
    Texpr1.of_expr env (
	let rec f expr =
	    match expr with
	    | V y -> Texpr1.Var (Var.of_string y)
	    | C r -> Texpr1.Cst (Coeff.s_of_float r)
	    | Interval (r1,r2) -> Texpr1.Cst (Coeff.i_of_float r1 r2)
	    | Add (e1,e2) -> Texpr1.(Binop (Add, f e1, f e2, Real, Near))
	    | Sub (e1,e2) -> Texpr1.(Binop (Sub, f e1, f e2, Real, Near))
	    | Mul (e1,e2) -> Texpr1.(Binop (Mul, f e1, f e2, Real, Near))
	in f expr
    )


let isVarConst x =
    let tcons = Tcons1.(make (expr2texpr (V (vVar x))) EQ) in
    Abstract1.sat_tcons mgr !astateRef tcons

let isVarLaplace x =
    StringSet.mem x !isLaplaceRef


let assign_texpr x texpr = astateRef := Abstract1.assign_texpr mgr !astateRef (Var.of_string x) texpr None
let assign_expr x expr = assign_texpr x (expr2texpr expr)

let compare_exprs e1 e2 =
    let texpr = expr2texpr (Sub (e1,e2)) in
    let tcons = Tcons1.(make texpr EQ) in
    let iseq = Abstract1.sat_tcons mgr !astateRef tcons in
    let tcons = Tcons1.(make texpr SUP) in
    let isgt = Abstract1.sat_tcons mgr !astateRef tcons in
    let texpr = expr2texpr (Sub (e2,e1)) in
    let tcons = Tcons1.(make texpr SUP) in
    let islt = Abstract1.sat_tcons mgr !astateRef tcons in
    (*printf "%B %B %B\n" iseq isgt islt;*)
    if iseq then 0
    else if isgt then 1
    else if islt then -1
    else -2


let processStatement_gen1 st =
    printf "processStatement_gen1\n";
    (
    match st with
    | Let (x,expr) ->
	match expr with
	| V x ->
	    if isVarLaplace x then isLaplaceRef := StringSet.add x !isLaplaceRef
	| Laplace ->
	    isLaplaceRef := StringSet.add x !isLaplaceRef
	| Add (V y1,V y2)
	| Mul (V y1,V y2) ->
	    if isVarLaplace y1 && isVarConst y2 || isVarLaplace y2 && isVarConst y1 then
		isLaplaceRef := StringSet.add x !isLaplaceRef
	| _ -> ()
    );
    printf "isLaplaceRef = {%s}\n" (String.concat "," (StringSet.elements !isLaplaceRef))


let processStatement_gen2 st =
    printf "processStatement_gen2\n";
    (
    match st with
    | Let (x,expr) ->
	match expr with
	| V _
	| C _
	| Add (_,_)
	| Mul (_,_) ->
	    assign_expr x expr
	| Eq (e1,e2) ->
	    let cmp = compare_exprs e1 e2 in
	    if cmp == 0 then assign_expr x (C 1.0)
	    else if cmp == 1 || cmp == -1 then assign_expr x (C 0.0)
	| Le (e1,e2) ->
	    let cmp = compare_exprs e1 e2 in
	    if cmp == -1 || cmp == 0 then assign_expr x (C 1.0)
	    else if cmp == 1 then assign_expr x (C 0.0)
	| _ -> ()
    );
    printf "astate=%a\n" Abstract1.print !astateRef


(* expectations *)
let processStatement_gen3 st =
    printf "processStatement_gen3\n";
    (
    match st with
    | Let (x,expr) ->
	let ex = vExp x in
	match expr with
	| V y ->
	    assign_expr ex (V (vExp y))
	| C r ->
	    assign_expr ex (C r)
	| Add (V y,C r) ->
	    assign_expr ex (Add (V (vExp y), C r))
	| Add (V y1,V y2) ->
	    assign_expr ex (Add (V (vExp y1), V (vExp y2)))
	| Mul (C r,V y) ->
	    assign_expr ex (Mul (C r, V (vExp y)))
	| Mul (V y1,V y2) ->
	    if isVarConst y1 || isVarConst y2 then assign_expr ex (Mul (V (vExp y1), V (vExp y2)))
	| Eq (e1,e2) ->
	    let cmp = compare_exprs e1 e2 in
	    if cmp == 0 then assign_expr ex (C 1.0)
	    else if cmp == 1 || cmp == -1 then assign_expr ex (C 0.0)
	    else assign_expr ex (Interval (0.0,1.0))
	| Le (e1,e2) ->
	    let cmp = compare_exprs e1 e2 in
	    if cmp == -1 || cmp == 0 then assign_expr ex (C 1.0)
	    else if cmp == 1 then assign_expr ex (C 0.0)
	    else assign_expr ex (Interval (0.0,1.0))
	| Laplace ->
	    assign_expr ex (C 0.0)
	| _ -> ()
    );
    printf "astate=%a\n" Abstract1.print !astateRef

(* variances *)
let processStatement_gen4 st =
    printf "processStatement_gen4\n";
    (
    match st with
    | Let (x,expr) ->
	let vx = vVar x in
	match expr with
	| V y ->
	    assign_expr vx (V (vVar y))
	| C _ ->
	    assign_expr vx (C 0.0)
	| Add (V y,C r) ->
	    assign_expr vx (V (vVar y))
	| Add (V y1,V y2) ->
	    if isVarConst y1 || isVarConst y2 then assign_expr vx (Add (V (vVar y1), V (vVar y2)))
	| Mul (C r,V y) ->
	    assign_expr vx (Mul (C (r*.r), V (vVar y)))
	| Mul (V y1,V y2) ->
	    if isVarConst y1 then assign_expr vx (Mul (V (vVar y2), Mul (V (vExp y1), V (vExp y1))))
	    else if isVarConst y2 then assign_expr vx (Mul (V (vVar y1), Mul (V (vExp y2), V (vExp y2))))
	| Eq (e1,e2) ->
	    let cmp = compare_exprs e1 e2 in
	    if cmp == 0 then assign_expr vx (C 0.0)
	    else if cmp == 1 || cmp == -1 then assign_expr vx (C 0.0)
	| Le (e1,e2) ->
	    let cmp = compare_exprs e1 e2 in
	    if cmp == -1 || cmp == 0 then assign_expr vx (C 0.0)
	    else if cmp == 1 then assign_expr vx (C 0.0)
	| Laplace ->
	    assign_expr vx (C 1.0)
	| _ -> ()
    );
    printf "astate=%a\n" Abstract1.print !astateRef


let processStatement st =
    print_statement st;
    processStatement_gen1 st;
    processStatement_gen2 st;
    processStatement_gen3 st;
    processStatement_gen4 st


let main () =
    List.iter print_statement example;
    List.iter processStatement example
;;


main ()
