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
  | IfThenElse of expr * expr * expr
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

type program = statement list


let rec print_expr expr =
    match expr with
    | V x -> print_string x
    | C r -> print_float r
    | Add (e1,e2) -> print_char '('; print_expr e1; print_string " + "; print_expr e2; print_char ')'
    | Sub (e1,e2) -> print_char '('; print_expr e1; print_string " - "; print_expr e2; print_char ')'
    | Mul (e1,e2) -> print_char '('; print_expr e1; print_string " * "; print_expr e2; print_char ')'
    | Div (e1,e2) -> print_char '('; print_expr e1; print_string " / "; print_expr e2; print_char ')'
    | Laplace -> print_string "Laplace()"
    | Le (e1,e2) -> print_char '('; print_expr e1; print_string " <= "; print_expr e2; print_char ')'
    | Eq (e1,e2) -> print_char '('; print_expr e1; print_string " == "; print_expr e2; print_char ')'
    | IfThenElse (e1,e2,e3) -> print_char '('; print_expr e1; print_string " ? "; print_expr e2; print_string " : "; print_expr e3; print_char ')'
    (*
    | And (e1,e2) -> print_char '('; print_expr e1; print_string " && "; print_expr e2; print_char ')'
    | Not e1 -> print_char '!'; print_expr e1
    *)
    | Input -> print_string "Input()"
    | Interval (r1,r2) -> print_char '['; print_float r1; print_char ','; print_float r2; print_char ']'
    | ScalarInterval (s1,s2) -> print_char '['; printf "%a" Scalar.print s1; print_char ','; printf "%a" Scalar.print s2; print_char ']'


let print_statement st =
    match st with
    | Let (x,expr) -> print_string x; print_string " := "; print_expr expr; print_newline ()


let sum_floats xs = List.fold_left (+.) 0. xs
let string_of_string_list strs = String.concat "," strs
let string_of_float_list xs = string_of_string_list (List.map string_of_float xs)


let example = [
    Let ("i", Input);
    Let ("j", Input);
    Let ("k", Mul (C 2.0, V "i"));
    Let ("l", Mul (C 2.0, V "j"));
    Let ("v", Laplace);
    Let ("w", Laplace);
    Let ("c", Mul (C 3.0, V "v"));
    Let ("d", Mul (C 3.0, V "w"));
    Let ("a", Add (V "k", V "c"));
    Let ("b", Add (V "l", V "d"));
    Let ("e", Laplace);
    Let ("f", Laplace);
    Let ("g", Add (V "k", V "e"));
    Let ("h", Add (V "l", V "f"));
]

let vExp x = String.concat "" ["E";x]
let vVar x = String.concat "" ["V";x]

let example_vars = List.(sort_uniq compare (map (fun (Let (x, _)) -> x) example))
let example_vars2 = example_vars @ List.map vExp example_vars @ List.map vVar example_vars
let _ = printf "variables: %s\n" (string_of_string_list example_vars2)

let vararr = Array.of_list example_vars2
let env = Environment.make [||] (Array.map Var.of_string vararr)
(*let mgr = Polka.manager_alloc_loose ()*)
let mgr = Ppl.manager_alloc_loose ()

module StringSet = Set.Make(String)
module StringMap = Map.Make(String)

let astateRef = ref (Abstract1.top mgr env)
let isLaplaceRef = ref StringSet.empty
let dependsetMapRef = ref StringMap.empty

let getDependset x = StringMap.find x !dependsetMapRef

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
            | Div (e1,e2) -> Texpr1.(Binop (Div, f e1, f e2, Real, Near))
        in f expr
    )

let expr2tconsEQ expr = Tcons1.(make (expr2texpr expr) EQ)
let expr2tconsSUP expr = Tcons1.(make (expr2texpr expr) SUP)

let isVarConst x =
    let tcons = expr2tconsEQ (V (vVar x)) in
    Abstract1.sat_tcons mgr !astateRef tcons

let isVarLaplace x =
    StringSet.mem x !isLaplaceRef

let areVarsIndep x y = StringSet.(is_empty (inter (getDependset x) (getDependset y)))

let areAllVarsIndep xs =
    let rec f xs depset =
	match xs with
	| [] -> true
	| y :: ys ->
	    let dsy = getDependset y in
	    if StringSet.(is_empty (inter dsy depset)) then
		f ys (StringSet.union dsy depset)
	    else
		false
    in f xs StringSet.empty

let areVarsEqual x y =
    let tcons = Tcons1.(make (expr2texpr (Sub (V x, V y))) EQ) in
    Abstract1.sat_tcons mgr !astateRef tcons

let scalar2float s =
    Scalar.(
        match s with
        | Float r -> r
        | Mpfrf r -> Mpfrf.to_float r
        | Mpqf q -> Mpqf.to_float q
    )

let scalar_min s1 s2 = if Scalar.cmp s1 s2 < 0 then s1 else s2
let scalar_max s1 s2 = if Scalar.cmp s1 s2 > 0 then s1 else s2

let getVarBoundsScalar x = Abstract1.bound_variable mgr !astateRef (Var.of_string x)

let getVarBounds x =
    let bounds0 = getVarBoundsScalar x in
    (scalar2float bounds0.inf, scalar2float bounds0.sup)

let getExprBounds expr =
    let bounds0 = Abstract1.bound_texpr mgr !astateRef (expr2texpr expr) in
    (scalar2float bounds0.inf, scalar2float bounds0.sup)

let printVarBounds x =
    let (inf,sup) = getVarBounds x in
    printf "bounds of %s: [%f,%f]\n" x inf sup

let printExprBounds expr =
    let (inf,sup) = getExprBounds expr in
    print_string "bounds of "; print_expr expr;
    printf ": [%f,%f]\n" inf sup

let getVarLowerBound x = fst (getVarBounds x)
let getVarUpperBound x = snd (getVarBounds x)

(* upper bound on the differential-privacy distance *)
let diffPrivDist x y =
    if isVarLaplace x && isVarLaplace y && areVarsEqual (vVar x) (vVar y) then
        let (inf, sup) = getExprBounds (Sub (V (vExp x), V (vExp y))) in
        max sup (-. inf) /. sqrt (0.5 *. getVarLowerBound (vVar x))
    else
        infinity

let listDiffPrivDist xs ys =
    if List.(length xs == length ys) && areAllVarsIndep xs && areAllVarsIndep ys then
	sum_floats (List.map2 diffPrivDist xs ys)
    else
	infinity

let assign_texpr x texpr = astateRef := Abstract1.assign_texpr mgr !astateRef (Var.of_string x) texpr None
let assign_expr x expr = assign_texpr x (expr2texpr expr)

let add_tcons tcons = astateRef := Abstract1.meet_tcons_array mgr !astateRef Tcons1.(let arr = array_make env 1 in array_set arr 0 tcons; arr)

let tcons2abstract tcons = Abstract1.of_tcons_array mgr env Tcons1.(let arr = array_make env 1 in array_set arr 0 tcons; arr)

let compare_exprs e1 e2 =
    let texpr = expr2texpr (Sub (e1,e2)) in
    let tcons = Tcons1.(make texpr EQ) in
    let iseq = Abstract1.sat_tcons mgr !astateRef tcons in
    let tcons = Tcons1.(make texpr SUP) in
    let isgt = Abstract1.sat_tcons mgr !astateRef tcons in
    let texpr = expr2texpr (Sub (e2,e1)) in
    let tcons = Tcons1.(make texpr SUP) in
    let islt = Abstract1.sat_tcons mgr !astateRef tcons in
    if iseq then 0
    else if isgt then 1
    else if islt then -1
    else -2


let processStatement_gen1 st =
    (*printf "processStatement_gen1\n";*)
    (
    match st with
    | Let (x,expr) ->
        match expr with
        | V x ->
            if isVarLaplace x then isLaplaceRef := StringSet.add x !isLaplaceRef
        | Laplace ->
            isLaplaceRef := StringSet.add x !isLaplaceRef
        | Add (V y,C r)
        | Mul (C r,V y) ->
            if isVarLaplace y then
                isLaplaceRef := StringSet.add x !isLaplaceRef
        | Add (V y1,V y2)
        | Mul (V y1,V y2) ->
            if isVarLaplace y1 && isVarConst y2 || isVarLaplace y2 && isVarConst y1 then
                isLaplaceRef := StringSet.add x !isLaplaceRef
        | _ -> ()
    );
    printf "isLaplaceRef = {%s}\n" (string_of_string_list (StringSet.elements !isLaplaceRef))


let processStatement_gen2 st =
    (*printf "processStatement_gen2\n";*)
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
    )(*;
    printf "astate=%a\n" Abstract1.print !astateRef*)


(* expectations *)
let processStatement_gen3 st =
    (*printf "processStatement_gen3\n";*)
    (
    match st with
    | Let (x,expr) ->
        let ex = vExp x in
        match expr with
        | Input ->
            assign_expr ex (V x)
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
            if isVarConst y1 || isVarConst y2 || areVarsIndep y1 y2 then assign_expr ex (Mul (V (vExp y1), V (vExp y2)))
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
	| IfThenElse (_,V y2,V y3) ->
	    let ey2bounds = getVarBoundsScalar (vExp y2) in
	    let ey3bounds = getVarBoundsScalar (vExp y3) in
	    assign_expr ex (ScalarInterval (scalar_min ey2bounds.inf ey3bounds.inf, scalar_max ey2bounds.sup ey3bounds.sup))
        | Laplace ->
            assign_expr ex (C 0.0)
        | _ -> ()
    )(*;
    printf "astate=%a\n" Abstract1.print !astateRef*)

(* variances *)
let processStatement_gen4 st =
    (*printf "processStatement_gen4\n";*)
    (
    match st with
    | Let (x,expr) ->
        let vx = vVar x in
        match expr with
        | V y ->
            assign_expr vx (V (vVar y))
        | Input
        | C _ ->
            assign_expr vx (C 0.0)
        | Add (V y,C r) ->
            assign_expr vx (V (vVar y))
        | Add (V y1,V y2) ->
            if isVarConst y1 || isVarConst y2 || areVarsIndep y1 y2 then assign_expr vx (Add (V (vVar y1), V (vVar y2)))
        | Mul (C r,V y) ->
            assign_expr vx (Mul (C (r*.r), V (vVar y)))
        | Mul (V y1,V y2) ->
            if isVarConst y1 then assign_expr vx (Mul (V (vVar y2), Mul (V (vExp y1), V (vExp y1))))
            else if isVarConst y2 then assign_expr vx (Mul (V (vVar y1), Mul (V (vExp y2), V (vExp y2))))
            else if areVarsIndep y1 y2 then
                assign_expr vx
                    (Add ((Mul (V (vVar y2), Mul (V (vExp y1), V (vExp y1)))),
                     Add ((Mul (V (vVar y1), Mul (V (vExp y2), V (vExp y2)))),
                          (Mul (V (vVar y1), V (vVar y2))))))
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

(* independences *)
let processStatement_gen6 st =
    (*printf "processStatement_gen6\n";*)
    (* for each variable x, find the set dependset(x) of Laplace variables that it depends on *)
    (* then Indep(x,y) if dependset(x) and dependset(y) are disjoint *)
    let rec getvars expr =
        match expr with
        | V y ->
            [y]
        | Add (e1,e2)
        | Mul (e1,e2)
        | Eq (e1,e2)
        | Le (e1,e2) ->
            getvars e1 @ getvars e2
	| IfThenElse (e1,e2,e3) ->
            getvars e1 @ getvars e2 @ getvars e3
        | _ ->
            []
    in
    match st with
    | Let (x,expr) ->
        let dependset =
            match expr with
            | C _ -> StringSet.empty
            | Laplace -> StringSet.singleton x
            | _ -> List.fold_right StringSet.union (List.map getDependset (getvars expr)) StringSet.empty
        in
        dependsetMapRef := StringMap.add x dependset !dependsetMapRef;
        printVarBounds x;
        printVarBounds (vExp x);
        printVarBounds (vVar x);
        printf "dependset[%s] = {%s}\n" x (string_of_string_list (StringSet.elements dependset))

let processStatement st =
    print_statement st;
    processStatement_gen1 st;
    processStatement_gen2 st;
    processStatement_gen3 st;
    processStatement_gen4 st;
    processStatement_gen6 st

let printDiffPrivDist x y =
    printf "diffPrivDist(%s,%s) = %f\n" x y (diffPrivDist x y)

let printListDiffPrivDist xs ys =
    printf "diffPrivDist([%s],[%s]) = %f\n" (string_of_string_list xs) (string_of_string_list ys) (listDiffPrivDist xs ys)

let main () =
    List.iter print_statement example;
    add_tcons (expr2tconsEQ (Sub (Sub (V "i", V "j"), Interval (-2.0, 2.0))));
    List.iter processStatement example;
    printDiffPrivDist "a" "b";
    printDiffPrivDist "c" "d";
    printDiffPrivDist "g" "h";
    printListDiffPrivDist ["a";"c"] ["b";"d"];
    printListDiffPrivDist ["a";"g"] ["b";"h"];
    printExprBounds (Sub (V "i", V "j"));
    printExprBounds (Sub (V "Ea", V "Eb"));
    printExprBounds (Sub (Sub (V "Ea", V "Eb"), Mul (C 2.0, Sub (V "i", V "j"))));
;;


main ()
