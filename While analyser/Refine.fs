module Refine

open Parser
open Eval


let Intersect a b =
    match a,b with
    | Bottom, _ | _, Bottom -> Bottom
    | Interval(l1,u1), Interval(l2,u2) -> createVarBound(max l1 l2, min u1 u2)

let refineVar (state:State) (x:string) (target:VariableBound) =
    match state with
    | BottomState -> BottomState
    | Vars v ->
        let old = v |> Map.tryFind x |> Option.defaultValue Bottom
        let neu = Intersect old target
        match neu with
        | Bottom -> BottomState 
        | _ -> Vars(v |> Map.add x neu)

let boundOf (trace:Map<Expr,VariableBound>) (e:Expr) =
    trace |> Map.tryFind e |> Option.defaultValue (createVarBound(MinusInf, PlusInf))

let isFinite = function Finite _ -> true | _ -> false

let boundLe a b =
    match a,b with
    | MinusInf, _ -> true
    | _, PlusInf -> true
    | PlusInf, _ -> false
    | _, MinusInf -> false
    | Finite x, Finite y -> x <= y

let boundMin a b = if boundLe a b then a else b
let boundMax a b = if boundLe a b then b else a

let floorDivInt (a:int) (k:int) =
    // k > 0
    if a >= 0 then a / k
    else - ((-a + k - 1) / k)

let ceilDivInt (a:int) (k:int) =
    // k > 0
    if a >= 0 then (a + k - 1) / k
    else - ((-a) / k)

let floorDivBoundByPos (b:Bound) (k:int) =
    // k > 0
    match b with
    | MinusInf -> MinusInf
    | PlusInf -> PlusInf
    | Finite a -> Finite (floorDivInt a k)

let ceilDivBoundByPos (b:Bound) (k:int) =
    // k > 0
    match b with
    | MinusInf -> MinusInf
    | PlusInf -> PlusInf
    | Finite a -> Finite (ceilDivInt a k)

let preimageByPos (target:VariableBound) (a:int) (b:int) : VariableBound =
    // y in [a,b], a>=1
    match target with
    | Bottom -> Bottom
    | Interval(tL,tU) ->
        let l1 = ceilDivBoundByPos tL a
        let l2 = ceilDivBoundByPos tL b
        let u1 = floorDivBoundByPos tU a
        let u2 = floorDivBoundByPos tU b
        createVarBound (boundMin l1 l2, boundMax u1 u2)

let splitNegPos (vb:VariableBound) =
    // restituisce (negPart, posPart) senza lo zero
    match vb with
    | Bottom -> Bottom, Bottom
    | Interval(l,u) ->
        let neg =
            if boundLe l (Finite -1) then
                let uu = if boundLe u (Finite -1) then u else Finite -1
                createVarBound (l, uu)
            else Bottom
        let pos =
            if boundLe (Finite 1) u then
                let ll = if boundLe (Finite 1) l then l else Finite 1
                createVarBound (ll, u)
            else Bottom
        neg, pos

let refineMulLeft (target:VariableBound) (b2:VariableBound) : VariableBound =
    match target, b2 with
    | Bottom, _ | _, Bottom -> Bottom

    // Se posso scegliere y=0 e 0 è ammesso dal target -> qualunque x va bene
    | _, _ when containsZero b2 && containsZero target ->
        createVarBound (MinusInf, PlusInf)

    | _ ->
        // consideriamo i due pezzi senza zero
        let neg, pos = splitNegPos b2

        let fromPos =
            match pos with
            | Bottom -> Bottom
            | Interval(Finite a, Finite b) ->
                preimageByPos target a b
            | _ ->
                createVarBound (MinusInf, PlusInf)

        let fromNeg =
            match neg with
            | Bottom -> Bottom
            | Interval(Finite a, Finite b) ->
                // neg = [a,b] con a<=b<=-1
                // y = -z, z in [ -b, -a ] positivo
                let za = -b
                let zb = -a
                // (-x)*z in target  =>  x in - preimageByPosY(target, za, zb)
                preimageByPos target za zb |> minusInterval
            | _ ->
                createVarBound (MinusInf, PlusInf)

        joinIntervals fromNeg fromPos

let enforceNonZero (vb:VariableBound) : VariableBound =
    match vb with
    | Bottom -> Bottom
    | Interval(l,u) ->
        // se è esattamente 0 -> impossibile
        if l = Finite 0 && u = Finite 0 then Bottom
        // se parte da 0, alza a 1
        elif l = Finite 0 then createVarBound (Finite 1, u)
        // se finisce a 0, abbassa a -1
        elif u = Finite 0 then createVarBound (l, Finite -1)
        else vb

let refineDivNumerator (target:VariableBound) (den:VariableBound) : VariableBound =
    match den with
    | Bottom -> Bottom
    | _ ->
        let den' = enforceNonZero den
        match den' with
        | Bottom -> Bottom
        | _ ->
            let neg, pos = splitNegPos den'   // come nel codice di Mul
            let partMul d =
                if d = Bottom then Bottom else mulIntervals target d
            joinIntervals (partMul neg) (partMul pos)

let rec refineExpr (state:State) (expr:Expr) (target:VariableBound) (trace:Map<Expr,VariableBound>) : State =
    match expr with
    | Int _ -> state
    | InputInt _ -> state
    | Var x -> refineVar state x target

    | Minus e ->
        let negTarget =
            match target with
            | Bottom -> Bottom
            | Interval(l,u) -> createVarBound(negateBound u, negateBound l)
        refineExpr state e negTarget trace

    | Add(e1,e2) ->
        let b1 = boundOf trace e1
        let b2 = boundOf trace e2
        let t1 = subIntervals target b2
        let t2 = subIntervals target b1
        state
        |> fun s -> refineExpr s e1 t1 trace
        |> fun s -> refineExpr s e2 t2 trace

    | Sub(e1,e2) ->
        let b1 = boundOf trace e1
        let b2 = boundOf trace e2
        let t1 = addIntervals target b2
        let t2 = subIntervals b1 target
        state
        |> fun s -> refineExpr s e1 t1 trace
        |> fun s -> refineExpr s e2 t2 trace
    | Mul(e1,e2) ->
        let b2 = boundOf trace e2
        let t1 = refineMulLeft target b2
        // simmetrico per e2:
        let b1 = boundOf trace e1
        let t2 = refineMulLeft target b1
        state
        |> fun s -> refineExpr s e1 t1 trace
        |> fun s -> refineExpr s e2 t2 trace
    | Div(e1,e2) ->
        let b1 = boundOf trace e1
        let b2 = boundOf trace e2
        // t1 = vincolo per numeratore, t2 = vincolo per denominatore
        // Numeratore: e1 ∈ target * e2 (senza 0 quando possibile)
        let t1 = refineDivNumerator target b2
        // Denominatore: esiste q in target tale che q*e2 ∈ b1  => e2 ∈ preimageMul(b1, target)
        // cioè riuso refineMulLeft con product=b1 e multiplier=target
        let t2 = refineMulLeft b1 target |> enforceNonZero
        state
        |> fun s -> refineExpr s e1 t1 trace
        |> fun s -> refineExpr s e2 t2 trace

let lubState s1 s2 =
    match s1,s2 with
    | BottomState, s
    | s, BottomState -> s
    | Vars m1, Vars m2 ->
        let keys =
            Seq.append (m1 |> Map.toSeq |> Seq.map fst) (m2 |> Map.toSeq |> Seq.map fst)
            |> Set.ofSeq

        let merged =
            keys
            |> Seq.fold (fun acc k ->
                let v1 = m1 |> Map.tryFind k |> Option.defaultValue Bottom
                let v2 = m2 |> Map.tryFind k |> Option.defaultValue Bottom
                acc |> Map.add k (joinIntervals v1 v2)
            ) Map.empty

        Vars merged

let rec negateCond c =
    match c with
    | True -> False
    | False -> True
    | Neg x -> x
    | And(a,b) -> Or(negateCond a, negateCond b)
    | Or(a,b) -> And(negateCond a, negateCond b)

    | Equi(a,b) -> Diff(a,b)
    | Diff(a,b) -> Equi(a,b)
    | Min(a,b) -> MagEqui(a,b)
    | MinEqui(a,b) -> Mag(a,b)
    | Mag(a,b) -> MinEqui(a,b)
    | MagEqui(a,b) -> Min(a,b)

let getLU = function
  | Bottom -> (PlusInf, MinusInf) // inconsistente
  | Interval(l,u) -> (l,u)

let predBound (b:Bound) =
  match b with
  | Finite k -> Finite (k-1)
  | PlusInf -> PlusInf
  | MinusInf -> MinusInf

let succBound (b:Bound) =
  match b with
  | Finite k -> Finite (k+1)
  | PlusInf -> PlusInf
  | MinusInf -> MinusInf

let isSingleton = function
  | Interval(Finite a, Finite b) when a=b -> Some a
  | _ -> None

let rec assumeCond(state:State,cond:Cond) =
    match cond,state with
    | _, BottomState -> BottomState
    | True,_ -> state

    | False,_ -> BottomState

    | Neg c,_ ->
        assumeCond(state, negateCond c)

    | And(c1,c2),_ ->
        let s1 = assumeCond(state,c1)
        assumeCond(s1,c2)

    | Or(c1,c2),_ ->
        let s1 = assumeCond(state,c1)
        let s2 = assumeCond(state,c2)
        lubState s1 s2
    | Equi(e1,e2),_ ->
        let evalE1 = evaluateExpr state e1
        let evalE2 = evaluateExpr state e2
        let trace = mergeMaps evalE1.steps evalE2.steps
        let common = Intersect evalE1.bound evalE2.bound
        let s1 = refineExpr state e1 common trace
        let s2 = refineExpr s1 e2 common trace
        s2
    | MinEqui(e1,e2),_ ->
        let ev1 = evaluateExpr state e1
        let ev2 = evaluateExpr state e2
        let trace = mergeMaps ev1.steps ev2.steps
        let (l1,u1) = getLU ev1.bound
        let (l2,u2) = getLU ev2.bound
        // e1 ∈ (-inf, u2], e2 ∈ [l1, +inf)
        let t1 = createVarBound(MinusInf, u2)
        let t2 = createVarBound(l1, PlusInf)
        state |> fun s -> refineExpr s e1 t1 trace
            |> fun s -> refineExpr s e2 t2 trace
    | Min(e1,e2),_ ->
        let ev1 = evaluateExpr state e1
        let ev2 = evaluateExpr state e2
        let trace = mergeMaps ev1.steps ev2.steps
        let (l1,u1) = getLU ev1.bound
        let (l2,u2) = getLU ev2.bound
        let t1 = createVarBound(MinusInf, predBound u2)
        let t2 = createVarBound(succBound l1, PlusInf)
        state |> fun s -> refineExpr s e1 t1 trace
            |> fun s -> refineExpr s e2 t2 trace

      // e1 >= e2  (riuso <=)
    | MagEqui(e1,e2),_ ->
        assumeCond(state, MinEqui(e2,e1))

    // e1 > e2  (riuso <)
    | Mag(e1,e2),_ ->
        assumeCond(state, Min(e2,e1))

    // e1 != e2
    | Diff(e1,e2),_ ->
        let ev1 = evaluateExpr state e1
        let ev2 = evaluateExpr state e2
        match isSingleton ev1.bound, isSingleton ev2.bound with
        | Some a, Some b when a = b ->
            BottomState
        | _ ->
            state


