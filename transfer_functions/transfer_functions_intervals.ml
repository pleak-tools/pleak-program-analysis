open Apron
open Format
open Syntax

let debug = ref false

let rec print_expr expr =
    match expr with
    | V x -> print_string x
    | Slice (x,i1,i2) -> printf "%s[%d:%d]" x i1 i2
    | C r -> print_float r
    | Add (e1,e2) -> print_char '('; print_expr e1; print_string " + "; print_expr e2; print_char ')'
    | Sub (e1,e2) -> print_char '('; print_expr e1; print_string " - "; print_expr e2; print_char ')'
    | Mul (e1,e2) -> print_char '('; print_expr e1; print_string " * "; print_expr e2; print_char ')'
    | Div (e1,e2) -> print_char '('; print_expr e1; print_string " / "; print_expr e2; print_char ')'
    | Laplace -> print_string "Laplace()"
    | Le (e1,e2) -> print_char '('; print_expr e1; print_string " <= "; print_expr e2; print_char ')'
    | Eq (e1,e2) -> print_char '('; print_expr e1; print_string " = "; print_expr e2; print_char ')'
    | IfThenElse (e1,e2,e3) -> print_char '('; print_expr e1; print_string " ? "; print_expr e2; print_string " : "; print_expr e3; print_char ')'
    | Sum e1 -> print_string "Sum "; print_expr e1
    (*
    | And (e1,e2) -> print_char '('; print_expr e1; print_string " && "; print_expr e2; print_char ')'
    | Not e1 -> print_char '!'; print_expr e1
    *)
    | Input -> print_string "Input()"
    | Interval (r1,r2) -> print_char '['; print_float r1; print_char ','; print_float r2; print_char ']'
    | ScalarInterval (s1,s2) -> print_char '['; printf "%a" Scalar.print s1; print_char ','; printf "%a" Scalar.print s2; print_char ']'

let rec print_statement st =
    match st with
    | Let (x,expr) -> print_string x; print_string " := "; print_expr expr; print_newline ()
    | LetSlice (x,i1,i2,expr) -> printf "%s[%d:%d]" x i1 i2; print_string " := "; print_expr expr; print_newline ()
    | Repeat (e1,prog) -> print_string "Repeat "; print_expr e1; print_newline (); print_program_indented prog; print_string "End"; print_newline ()
and print_program_indented prog = List.iter (fun st -> print_string "    "; print_statement st) prog

let print_program prog = List.iter print_statement prog


let println s = if !debug then (print_string s; print_newline ())

let sum_floats xs = List.fold_left (+.) 0. xs
let string_of_string_list strs = String.concat "," strs
let string_of_float_list xs = string_of_string_list (List.map string_of_float xs)

let rec uppercase_expr expr =
    match expr with
    | V x -> V (String.uppercase x)
    | C r -> C r
    | Sum e1 -> Sum (uppercase_expr e1)
    | Add (e1,e2) -> Add (uppercase_expr e1, uppercase_expr e2)
    | Mul (e1,e2) -> Mul (uppercase_expr e1, uppercase_expr e2)
    | Le (e1,e2) -> Le (uppercase_expr e1, uppercase_expr e2)
    | Eq (e1,e2) -> Eq (uppercase_expr e1, uppercase_expr e2)
    | IfThenElse (e1,e2,e3) -> IfThenElse (uppercase_expr e1, uppercase_expr e2, uppercase_expr e3)
    | _ -> expr


let rec intsFromTo a b = if a > b then [] else a :: intsFromTo (a+1) b

let largeExample n = List.map (fun i -> Let (String.concat "" ["x"; string_of_int i], C 2.0)) (intsFromTo 1 n)

let vExp x = String.concat "" ["E";x]
let vVar x = String.concat "" ["V";x]

let env = ref (Environment.make [||] [||])

let mgr = Box.manager_alloc ()
(*let mgr = Polka.manager_alloc_loose ()*)
(*let mgr = Ppl.manager_alloc_loose ()*)

module StringSet = Set.Make(String)
module StringMap = Map.Make(String)
module StringPairMap = Map.Make(struct type t = string * string let compare = compare end)

let astateRef = ref (Abstract1.top mgr !env)
let isLaplaceRef = ref StringSet.empty
let dependsetMapRef = ref StringMap.empty
let vecDependsetMapRef = ref StringMap.empty
let dpDependsetMapRef = ref StringMap.empty
let varExprRef = ref StringMap.empty
let isSyntacticallyConstRef = ref StringSet.empty
let vecDistMapRef = ref StringMap.empty
let numVecDists = ref 0
let scalarDistMapRef = ref StringMap.empty
let slicesMapRef = ref StringMap.empty

let scalar_max s1 s2 = if Scalar.cmp s1 s2 > 0 then s1 else s2
let scalar_min s1 s2 = if Scalar.cmp s1 s2 < 0 then s1 else s2
let interval_union t1 t2 = Interval.(if is_bottom t1 then t2 else if is_bottom t2 then t1 else of_scalar (scalar_min t1.inf t2.inf) (scalar_max t1.sup t2.sup))

let programVars program =
    let rec f st =
	match st with
	| Let (x,_) -> [x]
	| LetSlice (x,_,_,_) -> [x]
	| Repeat (i,prog) -> g prog
    and g prog = List.(concat (map f prog)) in
    List.(sort_uniq compare (g program))

let initEnvironment program =
    let program_vars = programVars program in
    let program_vars2 = program_vars @ List.map vExp program_vars @ List.map vVar program_vars in
    let _ = if !debug then printf "variables: %s\n" (string_of_string_list program_vars2) in
    let vararr = Array.of_list program_vars2 in
    env := Environment.make [||] (Array.map Var.of_string vararr);
    astateRef := Abstract1.top mgr !env

let getDependset x = StringMap.find x !dependsetMapRef
let getVecDependset x = StringMap.find x !vecDependsetMapRef
let getDpDependset x = StringMap.find x !dpDependsetMapRef
let getVarExpr x = StringMap.find x !varExprRef
let isSyntacticallyConst x = StringSet.mem x !isSyntacticallyConstRef

let addVecDist xs (d : float) =
    let vecDistNo = !numVecDists in
    numVecDists := !numVecDists + 1;
    List.iter (fun x -> vecDistMapRef := StringMap.add x (d,vecDistNo) !vecDistMapRef) xs

let getVecDist x = fst (StringMap.find x !vecDistMapRef)
let getVecDistNo x = snd (StringMap.find x !vecDistMapRef)
let hasVecDist x = StringMap.mem x !vecDistMapRef
let getVecDistOrInf x = if hasVecDist x then getVecDist x else infinity

let getScalarDist x = try StringMap.find x !scalarDistMapRef with Not_found -> infinity
let addScalarDist x d =
    (* if !debug then printf "addScalarDist %s %f\n" x d; *)
    scalarDistMapRef := StringMap.add x (min d (getScalarDist x)) !scalarDistMapRef

let expr2texpr expr =
    Texpr1.of_expr !env (
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

let assign_texpr x texpr = Abstract1.assign_texpr_with mgr !astateRef (Var.of_string x) texpr None
let assign_expr x expr = assign_texpr x (expr2texpr expr)

let add_tcons tcons = Abstract1.meet_tcons_array_with mgr !astateRef Tcons1.(let arr = array_make !env 1 in array_set arr 0 tcons; arr)

let tcons2abstract tcons = Abstract1.of_tcons_array mgr !env Tcons1.(let arr = array_make !env 1 in array_set arr 0 tcons; arr)

let killVar1 x = assign_texpr x Texpr1.(of_expr !env (Cst (Coeff.Interval Interval.top)))
let killVar x = killVar1 x; killVar1 (vExp x); killVar1 (vVar x)

let setVarBoundsScalar x t = assign_texpr x Texpr1.(of_expr !env (Cst (Coeff.Interval t)))

let isVarConst x =
    let tcons = expr2tconsEQ (V (vVar x)) in
    Abstract1.sat_tcons mgr !astateRef tcons

let isVarLaplace x =
    StringSet.mem x !isLaplaceRef

let areVarsIndep x y = StringSet.(is_empty (inter (getDependset x) (getDependset y)))

let all bs = List.fold_left (&&) true bs
let isVarIndepOfAll x xs = all (List.map (areVarsIndep x) xs)

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

let scalar2float s =
    Scalar.(
	let isinf = is_infty s in
	if isinf != 0 then
	   float_of_int isinf *. infinity
	else
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

let areVarBoundsEqual x =
    let bounds = getVarBoundsScalar x in
    Scalar.equal bounds.inf bounds.sup

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

let getSlices x =
    if StringMap.mem x !slicesMapRef then
	StringMap.find x !slicesMapRef
    else
	[(0,Interval.top)]

let setSlices x sls = slicesMapRef := StringMap.add x sls !slicesMapRef

let getSlice x ((i1,i2) : int * int) =
    let slices = getSlices x in
    let rec f sls bounds =
	match sls with
	| (j1,b1) :: (j2,b2) :: sls' ->
	    f ((j2,b2) :: sls') (
		if i2 <= j1 || i1 >= j2 then
		    bounds
		else
		    interval_union bounds b1)
	| [(j1,b1)] ->
	    if i2 <= j1 then
		bounds
	    else
		interval_union bounds b1
    in
    f slices Interval.bottom

let getTopSlice x = getSlice x (0,max_int)

let setSlice x (i1,i2) t =
    let slices = getSlices x in
    let rec f sls =
	match sls with
	| (j1,b1) :: (j2,b2) :: sls' ->
	    if i1 >= j2 then
		(j1,b1) :: f ((j2,b2) :: sls')
	    else if i2 <= j1 then
		sls
	    else if i1 > j1 then
		(j1,b1) :: f ((i1,b1) :: (j2,b2) :: sls')
	    else if i1 == j1 then
		(i1,t) :: (
		    if i2 < j2 then
			(i2,b1) :: (j2,b2) :: sls'
		    else
			f ((j2,b2) :: sls'))
	    else (*if i1 < j1 then*) (
		if i2 < j2 then
		    (i2,b1) :: (j2,b2) :: sls'
		else
		    f ((j2,b2) :: sls'))
	| [(j1,b1)] ->
	    if i2 <= j1 then
		sls
	    else if i1 > j1 then
		(j1,b1) :: f [(i1,b1)]
	    else if i1 == j1 then
		[(i1,t); (i2,b1)]
	    else (*if i1 < j1 then*)
		[(i2,b1)]
    in
    setSlices x (f slices)

(* write the current bounds of x in the abstract state to the slice (i1,i2) *)
let writeSlice x (i1,i2) =
    let t = getVarBoundsScalar x in
    setSlice x (i1,i2) t

let writeTopSlice x = writeSlice x (0,max_int)

(* read the new bounds of x in the abstract state from the slice (i1,i2) *)
let readSlice x (i1,i2) =
    let t = getSlice x (i1,i2) in
    setVarBoundsScalar x t

let readTopSlice x = readSlice x (0,max_int)

let printSlices x =
    printf "slices of %s:" x;
    let rec f sls =
	match sls with
	| (j1,b1) :: (j2,b2) :: sls' ->
	    printf " [%d:%d] -> %a;" j1 j2 Interval.print b1;
	    f ((j2,b2) :: sls')
	| [(j1,b1)] ->
	    printf " [%d:] -> %a\n" j1 Interval.print b1
    in
    f (getSlices x)

let isSyntConstOrLaplace x = isSyntacticallyConst x || isVarLaplace x

(* a Laplace variable which is not computed from other Laplace variables and constants *)
let isMaxLaplace x =
    isVarLaplace x && not (
	match getVarExpr x with
	| C _ ->
	    true
        | Add (V y,C _)
        | Mul (C _,V y)
	| V y ->
	    isSyntConstOrLaplace y
        | Add (V y1,V y2)
        | Mul (V y1,V y2)
        | Le (V y1,V y2)
        | Eq (V y1,V y2) ->
	    isSyntConstOrLaplace y1 && isSyntConstOrLaplace y2
        | IfThenElse (V y1,V y2,V y3) ->
	    isSyntConstOrLaplace y1 && isSyntConstOrLaplace y2 && isSyntConstOrLaplace y3
	| _ ->
	    false
    )

let scalarDist x =
    let (inf, sup) = getVarBounds (vExp x) in
    min (sup -. inf) (getScalarDist x)

let addVarInterval x a b =
    (*add_tcons (expr2tconsEQ (Sub (V (vExp x), Interval (a, b))))*)
    add_tcons (expr2tconsEQ (Sub (V x, Interval (a, b))))

let vecDist xs =
    let vecDistNos = ref [] in
    let dist = ref 0.0 in
    let addVdn x = vecDistNos := x :: !vecDistNos in
    let addDist r = dist := !dist +. r in
    let equal x xs = List.mem x xs in
    let rec f x =
	if hasVecDist x then
	    let vdn = getVecDistNo x in
	    let vdns = !vecDistNos in
	    if equal vdn vdns then
		()
	    else (
		addVdn vdn;
		addDist (getVecDist x)
	    )
	else
	    addDist infinity
    in
    List.iter (StringSet.iter f) (List.map getVecDependset xs);
    !dist

(* upper bound on the differential-privacy distance *)
let simpleDiffPrivDist x =
    if isVarLaplace x && areVarBoundsEqual (vVar x) then (
        scalarDist x /. sqrt (0.5 *. getVarLowerBound (vVar x))
    ) else
        infinity

let diffPrivDist xs =
    let eqvVars = ref [] in
    let dpDist = ref 0.0 in
    let addEqvVars x = eqvVars := x :: !eqvVars in
    let addDpDist r = dpDist := !dpDist +. r in
    let equal x xs = List.mem x xs in
    let indep x xs = isVarIndepOfAll x xs in
    let rec f x =
	if isMaxLaplace x then
	    let xs = !eqvVars in
	    if equal x xs then
		()
	    else if indep x xs then (
		addEqvVars x;
		addDpDist (simpleDiffPrivDist x)
	    ) else
		addDpDist infinity
	else
	    addDpDist infinity
    in
    List.iter (StringSet.iter f) (List.map getDpDependset xs);
    !dpDist

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
    (*println "processStatement_gen1";*)
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
    if !debug then printf "isLaplaceRef = {%s}\n" (string_of_string_list (StringSet.elements !isLaplaceRef))


let processStatement_gen2 st =
    (*println "processStatement_gen2";*)
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
    (*println "processStatement_gen3";*)
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
    (*println "processStatement_gen4";*)
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
	| Sum (V y) ->
	    if isVarConst y then
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
    if !debug then printf "astate=%a\n" Abstract1.print !astateRef

let processStatement_scalarDists st =
    (
    match st with
    | Let (x,expr) ->
	(
        match expr with
        | C _
        | Laplace ->
	    addScalarDist x 0.0
        | V y
        | Add (V y,C _) ->
	    addScalarDist x (scalarDist y)
        | Add (V y1,V y2) ->
            addScalarDist x (scalarDist y1 +. scalarDist y2)
        | Mul (C r,V y) ->
            addScalarDist x (r *. scalarDist y)
        | Mul (V y1,V y2) ->
	    if isVarConst y1 && scalarDist y1 <= 0.0 then
		addScalarDist x (abs_float (getVarUpperBound y1) *. scalarDist y2);
	    if isVarConst y2 && scalarDist y2 <= 0.0 then
		addScalarDist x (abs_float (getVarUpperBound y2) *. scalarDist y1)
        | Eq (e1,e2)
        | Le (e1,e2) ->
	    addScalarDist x 1.0
	| IfThenElse (V y1,V y2,V y3) ->
	    if isVarConst y1 && scalarDist y1 <= 0.0 then
		addScalarDist x (max (scalarDist y2) (scalarDist y3))
	| Sum (V y) ->
	    let vd = vecDist [y] in
	    let sd = scalarDist y in
	    if !debug then printf "processStatement_scalarDists: computeDists %s vd=%f sd=%f\n" x vd sd;
	    addScalarDist x (vd *. sd)
        | _ -> ()
	);
	if !debug then printf "scalarDist(%s) = %f\n" x (scalarDist x)
    )

let processStatement_isSyntacticallyConst st =
    match st with
    | Let (x,expr) ->
	match expr with
        | Add (V y,C _)
        | Mul (C _,V y)
	| V y ->
	    if isSyntacticallyConst y then isSyntacticallyConstRef := StringSet.add x !isSyntacticallyConstRef
	| C _ ->
	    isSyntacticallyConstRef := StringSet.add x !isSyntacticallyConstRef
        | Add (V y1,V y2)
        | Mul (V y1,V y2)
        | Le (V y1,V y2)
        | Eq (V y1,V y2) ->
	    if isSyntacticallyConst y1 && isSyntacticallyConst y2 then isSyntacticallyConstRef := StringSet.add x !isSyntacticallyConstRef
        | IfThenElse (V y1,V y2,V y3) ->
	    if isSyntacticallyConst y1 && isSyntacticallyConst y2 && isSyntacticallyConst y3 then isSyntacticallyConstRef := StringSet.add x !isSyntacticallyConstRef
	| _ -> ()

let processStatement_gen5 st =
    match st with
    | Let (x,expr) ->
	varExprRef := StringMap.add x expr !varExprRef 

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

let rec applySlices expr =
    match expr with
    | Slice (x,i1,i2) ->
	readSlice x (i1,i2); V x
    | Add (e1,e2) ->
	Add (applySlices e1, applySlices e2)
    | Mul (e1,e2) ->
	Mul (applySlices e1, applySlices e2)
    | Eq (e1,e2) ->
	Eq (applySlices e1, applySlices e2)
    | Le (e1,e2) ->
	Le (applySlices e1, applySlices e2)
    | IfThenElse (e1,e2,e3) ->
	IfThenElse (applySlices e1, applySlices e2, applySlices e3)
    | _ ->
	expr

let rec unapplySlices expr =
    match expr with
    | Slice (x,i1,i2) ->
	readTopSlice x
    | Add (e1,e2) ->
	unapplySlices e1; unapplySlices e2
    | Mul (e1,e2) ->
	unapplySlices e1; unapplySlices e2
    | Eq (e1,e2) ->
	unapplySlices e1; unapplySlices e2
    | Le (e1,e2) ->
	unapplySlices e1; unapplySlices e2
    | IfThenElse (e1,e2,e3) ->
	unapplySlices e1; unapplySlices e2; unapplySlices e3
    | _ ->
	()

(* independences *)
let processStatement_gen6 st =
    (*println "processStatement_gen6";*)
    (* for each variable x, find the set dependset(x) of Laplace variables that it depends on *)
    (* then Indep(x,y) if dependset(x) and dependset(y) are disjoint *)
    match st with
    | Let (x,expr) ->
        let dependset =
            match expr with
            | C _ -> StringSet.empty
            | Laplace -> StringSet.singleton x
            | _ -> List.fold_right StringSet.union (List.map getDependset (getvars expr)) StringSet.empty
        in
        dependsetMapRef := StringMap.add x dependset !dependsetMapRef;
	if !debug then (
	    printVarBounds x;
	    printVarBounds (vExp x);
	    printVarBounds (vVar x);
	    printf "dependset[%s] = {%s}" x (string_of_string_list (StringSet.elements dependset)); print_newline ()
	)

let processStatement_vecDependset st =
    (* for each variable x, find the set vecDependset(x) of input vector variables that it depends on, assuming that x is a vector variable *)
    (* vecDependset(x) is used to compute vecDist *)
    match st with
    | Let (x,expr) ->
        let dependset =
	    match expr with
	    | Input ->
		StringSet.singleton x
	    | _ ->
		List.fold_right StringSet.union (List.map getVecDependset (getvars expr)) StringSet.empty
        in
        vecDependsetMapRef := StringMap.add x dependset !vecDependsetMapRef;
	if !debug then printf "vecDependset[%s] = {%s}\n" x (string_of_string_list (StringSet.elements dependset))

let dpDependsetChanged = ref false

let processStatement_dpDependset1 certainlyExecuted st =
    (* for each variable x, find the set dpDependset(x) of maximal Laplace variables and input variables that it depends on *)
    (* dpDependset(x) is used to compute dpDist *)
    match st with
    | Let (x,expr) ->
        let dependset =
	    if isMaxLaplace x then
		StringSet.singleton x
	    else
		match expr with
		| Input ->
		    StringSet.singleton x
		| _ ->
		    List.fold_right StringSet.union (List.map getDpDependset (getvars expr)) StringSet.empty
        in
	let hasPrevDepset = StringMap.mem x !dpDependsetMapRef in
	let newDependset =
	    if certainlyExecuted || not hasPrevDepset then
		dependset
	    else
		StringSet.union (getDpDependset x) dependset
	in
	if not hasPrevDepset || not (StringSet.equal (getDpDependset x) newDependset) then (
	    dpDependsetMapRef := StringMap.add x newDependset !dpDependsetMapRef;
	    dpDependsetChanged := true
	);
	if !debug then printf "dpDependset[%s] = {%s}\n" x (string_of_string_list (StringSet.elements newDependset))

let processStatement_dpDependset st = processStatement_dpDependset1 true st

let rec processRepeatStatement_dpDependset m n prog =
    if !debug then printf "processRepeatStatement_dpDependset %d %d\n" m n;
    if n > 0 then (
	dpDependsetChanged := false;
	List.iter (processStatement_dpDependset1 (m>0)) prog;
	if !dpDependsetChanged then
	    processRepeatStatement_dpDependset (m-1) (n-1) prog
    )

let processStatement st =
    print_statement st;
    match st with
    | Let (x,_) ->
	processStatement_gen1 st;
	processStatement_gen2 st;
	processStatement_gen3 st;
	processStatement_gen4 st;
	processStatement_scalarDists st;
	processStatement_isSyntacticallyConst st;
	processStatement_gen5 st;
	processStatement_gen6 st;
	processStatement_vecDependset st;
	processStatement_dpDependset st;
	writeTopSlice x
    | LetSlice (x,i1,i2,e) ->
	let e' = applySlices e in
	processStatement_gen2 (Let (x,e'));
	writeSlice x (i1,i2);
	unapplySlices e;
	readTopSlice x;
	printSlices x
    | Repeat (e1,prog) ->
	List.iter killVar (programVars prog); (* remove the information that is not computed correctly for loops *)
	let (inf,sup) = getExprBounds e1 in
	let (m,n) = (int_of_float (floor inf), int_of_float (ceil sup)) in
	processRepeatStatement_dpDependset m n prog

let printDiffPrivDist x =
    printf "diffPrivDist(%s) = %f\n" x (diffPrivDist [x])

let printListDiffPrivDist xs =
    printf "diffPrivDist([%s]) = %f\n" (string_of_string_list xs) (diffPrivDist xs)

let printVecDist xs =
    printf "vecDist([%s]) = %f\n" (string_of_string_list xs) (vecDist xs)

let processHeaderDecl hdecl =
    match hdecl with
    | AddVarInterval (x,r1,r2) ->
	addVarInterval x r1 r2
    | AddScalarDist (x,sd) ->
	addScalarDist x sd
    | AddVecDist (xs,vd) ->
	addVecDist xs vd

let processHeader header = List.iter processHeaderDecl header

let processFooterDecl fdecl =
    match fdecl with
    | PrintDiffPrivDist xs ->
	printListDiffPrivDist xs
    | PrintVecDist xs ->
	printVecDist xs

let processFooter footer = List.iter processFooterDecl footer

let testLargeExample n =
    let example = largeExample n in
    initEnvironment example;
    List.iter processStatement example

let tmpUid = ref 0
let getTmpVar () =
    tmpUid := !tmpUid + 1;
    String.concat "" ["$"; string_of_int (!tmpUid)]

let simplifyAlways e =
    let t = getTmpVar () in
    ([Let (t,e)], V t)

let simplifyKeepingVars e =
    match e with
    | V _ ->
	([], e)
    | _ ->
	simplifyAlways e

let simplifyKeepingVarsAndConsts e =
    match e with
    | V _
    | C _ ->
	([], e)
    | _ ->
	simplifyAlways e

let rec simplifyExpr expr =
    match expr with
    | Add (e1,e2) ->
	let (st1a,e1a) = simplifyExpr e1 in
	let (st2a,e2a) = simplifyExpr e2 in
	let (st1b,e1b) = simplifyKeepingVars e1a in
	let (st2b,e2b) = simplifyKeepingVarsAndConsts e2a in
	(List.concat [st1a;st2a;st1b;st2b], Add (e1b,e2b))
    | Mul (e1,e2) ->
	let (st1a,e1a) = simplifyExpr e1 in
	let (st2a,e2a) = simplifyExpr e2 in
	let (st1b,e1b) = simplifyKeepingVarsAndConsts e1a in
	let (st2b,e2b) = simplifyKeepingVars e2a in
	(List.concat [st1a;st2a;st1b;st2b], Mul (e1b,e2b))
    | Eq (e1,e2) ->
	let (st1a,e1a) = simplifyExpr e1 in
	let (st2a,e2a) = simplifyExpr e2 in
	let (st1b,e1b) = simplifyKeepingVars e1a in
	let (st2b,e2b) = simplifyKeepingVars e2a in
	(List.concat [st1a;st2a;st1b;st2b], Eq (e1b,e2b))
    | Le (e1,e2) ->
	let (st1a,e1a) = simplifyExpr e1 in
	let (st2a,e2a) = simplifyExpr e2 in
	let (st1b,e1b) = simplifyKeepingVars e1a in
	let (st2b,e2b) = simplifyKeepingVars e2a in
	(List.concat [st1a;st2a;st1b;st2b], Le (e1b,e2b))
    | Sum e1 ->
	let (st1a,e1a) = simplifyExpr e1 in
	let (st1b,e1b) = simplifyKeepingVars e1a in
	(List.concat [st1a;st1b], Sum e1b)
    | IfThenElse (e1,e2,e3) ->
	let (st1a,e1a) = simplifyExpr e1 in
	let (st2a,e2a) = simplifyExpr e2 in
	let (st3a,e3a) = simplifyExpr e3 in
	let (st1b,e1b) = simplifyKeepingVars e1a in
	let (st2b,e2b) = simplifyKeepingVars e2a in
	let (st3b,e3b) = simplifyKeepingVars e3a in
	(List.concat [st1a;st2a;st3a;st1b;st2b;st3b], IfThenElse (e1b,e2b,e3b))
    | _ ->
	([], expr)

let rec simplifyStatement st =
    match st with
    | Let (x,expr) ->
	let (st1,e1) = simplifyExpr expr in
	st1 @ [Let (x,e1)]
    | LetSlice (x,i1,i2,expr) ->
	let (st1,e1) = simplifyExpr expr in
	st1 @ [LetSlice (x,i1,i2,e1)]
    | Repeat (e1,prog) ->
	let (st1a,e1a) = simplifyExpr e1 in
	let (st1b,e1b) = simplifyKeepingVarsAndConsts e1a in
	let prog' = simplifyProgram prog in
	st1a @ st1b @ [Repeat (e1b,prog')]

and simplifyProgram prog = List.concat (List.map simplifyStatement prog)

let main () =
    if Array.length Sys.argv = 1 then (
	printf "Usage: %s [-d] INPUTFILE\n" Sys.argv.(0);
	printf "Processes the file INPUTFILE\n";
	printf "-d        enables debugging output\n";
	printf "-l LINES  processes a simple example with LINES lines (for testing performance)\n"
    );

    let i = ref 1 in
    while !i < Array.length Sys.argv do
	if Sys.argv.(!i) = "-d" then
	    debug := true
	else if Sys.argv.(!i) = "-l" then (
	    let n = int_of_string(Sys.argv.(!i+1)) in
	    testLargeExample n;
	    i := !i+1
	) else (
	    let ic = open_in Sys.argv.(!i) in
	    let lexbuf = Lexing.from_channel ic in
	    let (header,prog0,footer) = Myparser.prog Lexer.token lexbuf in
	    let prog = simplifyProgram prog0 in
	    initEnvironment prog;
	    if !debug then (print_program prog; flush stdout);
	    processHeader header;
	    List.iter processStatement prog;
	    processFooter footer;
	    close_in ic;
	    i := Array.length Sys.argv - 1
	);
	i := !i+1
    done
;;


main ()
