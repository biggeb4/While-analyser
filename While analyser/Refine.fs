module Refine

open Parser
open Eval


let Intersect a b =
    match a,b with
    | Bottom, _ | _, Bottom -> Bottom
    | Interval(l1,u1), Interval(l2,u2) -> createVarBound(max l1 l2, min u1 u2)

let refineVar (state:State) (x:string) (target:VariableBound) =
    let old = state |> Map.tryFind x |> Option.defaultValue Bottom
    let neu = Intersect old target
    state |> Map.add x neu

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

let zeroIn (vb:VariableBound) =
    match vb with
    | Bottom -> false
    | Interval(l,u) -> boundLe l (Finite 0) && boundLe (Finite 0) u

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

let preimageByPosY (target:VariableBound) (a:int) (b:int) : VariableBound =
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
    | _, _ when zeroIn b2 && zeroIn target ->
        createVarBound (MinusInf, PlusInf)

    | _ ->
        // consideriamo i due pezzi senza zero
        let neg, pos = splitNegPos b2

        let fromPos =
            match pos with
            | Bottom -> Bottom
            | Interval(Finite a, Finite b) ->
                preimageByPosY target a b
            | _ ->
                // pos ma non finito: fallback safe (puoi raffinare poco)
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
                preimageByPosY target za zb |> minusInterval
            | _ ->
                createVarBound (MinusInf, PlusInf)

        // union (approssimata) dei due insiemi: lub
        lub fromNeg fromPos

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
            lub (partMul neg) (partMul pos)

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

let rec assumeCond(state:State,cond:Cond) =
    match cond with
    | Equi(e1,e2) ->
        let evalE1 = evaluateExpr state e1
        let evalE2 = evaluateExpr state e2
        let trace = mergeMaps evalE1.steps evalE2.steps
        let common = Intersect evalE1.bound evalE2.bound
        let s1 = refineExpr state e1 common trace
        let s2 = refineExpr s1 e2 common trace
        s2
