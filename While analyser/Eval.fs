module Eval
open CFGBuilder
open Parser

type VariableBound = 
    |Interval of Bound * Bound
    |Bottom

type State = 
    |Vars of Map<string, VariableBound>
    |BottomState

let mutable states : Map<NodeId, State> = Map.empty
let mutable warnings :Set<string> = Set.empty
let mutable maxBound = Bound.PlusInf
let mutable minBound = Bound.MinusInf

let negateBound b =
    match b with
    | Finite v -> Finite (-v)
    | PlusInf -> MinusInf
    | MinusInf -> PlusInf

let createVarBound (lower: Bound, upper: Bound) : VariableBound =
    let l = max minBound lower
    let u = min maxBound upper
    if u < l then Bottom
    else Interval (l,u)

let containsZero (interval)=
    match interval with
    | Interval (lower, upper) ->
        match lower, upper with
        | Finite l, Finite u -> l <= 0 && u >= 0
        | MinusInf, _ | _, PlusInf -> true
        | PlusInf, _ | _, MinusInf -> false
    | Bottom -> false

let hasUnbounded (interval) =
    match interval with
    | Interval (lower, upper) ->
        match lower, upper with
        | Finite _, Finite _ -> false
        | _ -> true
    | Bottom -> false

let isPositive (interval) =
    match interval with
    | Interval (lower, upper) ->
        match lower, upper with
        | Finite l, Finite u -> l > 0 && u > 0
        | MinusInf, _ | _, PlusInf -> false
        | PlusInf, _ | _, MinusInf -> true
    | Bottom -> false

let isNegative (interval) =
    match interval with
    | Interval (lower, upper) ->
        match lower, upper with
        | Finite l, Finite u -> l < 0 && u < 0
        | MinusInf, _ | _, PlusInf -> false
        | PlusInf, _ | _, MinusInf -> true
    | Bottom -> false

//lub: least upper bound (join) tra due VariableBound
let joinIntervals a b =
    match a, b with
    | Bottom, x | x, Bottom -> x

    | Interval(l1,u1), Interval(l2,u2) ->
        Interval(min l1 l2, max u1 u2)

let unionOpt s1 s2 =
    match s1, s2 with
    | None, None -> None
    | Some s, None
    | None, Some s -> Some s
    | Some a, Some b -> Some (Set.union a b)

type EvalRes =
  { bound: VariableBound
    vars: Set<string>
    steps: Map<Expr, VariableBound> }

let mergeMaps m1 m2 =
    Map.fold (fun acc k v -> Map.add k v acc) m1 m2

let minusInterval i =
    match i with
    | Interval(l,u) -> Interval(negateBound u, negateBound l)
    | Bottom -> Bottom

let addIntervals i1 i2 =
    match i1, i2 with
    | Interval(l1,u1), Interval(l2,u2) ->
        let newLower =
            match l1, l2 with
            | MinusInf, _ | _, MinusInf -> MinusInf
            | PlusInf, _ | _, PlusInf -> PlusInf
            | Finite a, Finite b -> Finite (a + b)
        let newUpper =
            match u1, u2 with
            | PlusInf, _ | _, PlusInf -> PlusInf
            | MinusInf, _ | _, MinusInf -> MinusInf
            | Finite a, Finite b -> Finite (a + b)
        createVarBound(newLower, newUpper)
    | Bottom, _ | _, Bottom ->
        Bottom

let subIntervals i1 i2 =
    match i1, i2 with
    | Interval(l1,u1), Interval(l2,u2) ->
        let newLower =
            match l1, u2 with
            | MinusInf, _ | _, PlusInf -> MinusInf
            | PlusInf, _ | _, MinusInf -> PlusInf
            | Finite a, Finite b -> Finite (a - b)
        let newUpper =
            match u1, l2 with
            | PlusInf, _ | _, MinusInf -> PlusInf
            | MinusInf, _ | _, PlusInf -> MinusInf
            | Finite a, Finite b -> Finite (a - b)
        createVarBound(newLower, newUpper)
    | Bottom, _ | _, Bottom ->
        Bottom

let mulIntervals i1 i2 =
    match i1, i2 with
    | Bottom, _ | _, Bottom ->
        Bottom
    | i1, i2 ->
        if (hasUnbounded i1 && containsZero i2) || (hasUnbounded i2 && containsZero i1) then
            createVarBound(MinusInf, PlusInf)
        else
            let (Interval(l1,u1)) = i1
            let (Interval(l2,u2)) = i2
            let candidates = [ (l1,l2); (l1,u2); (u1,l2); (u1,u2) ]
            let prods =
                candidates
                |> List.map (fun (a,b) ->
                    match a,b with
                    | Finite x, Finite y -> Finite (x * y)

                    | PlusInf, Finite k | Finite k, PlusInf ->
                        if k > 0 then PlusInf
                        elif k < 0 then MinusInf
                        else failwith "impossibile: 0 * +inf (filtrato prima)"
                    | MinusInf, Finite k | Finite k, MinusInf ->
                        if k > 0 then MinusInf
                        elif k < 0 then PlusInf
                        else failwith "impossibile: 0 * -inf (filtrato prima)"
                    | PlusInf, PlusInf -> PlusInf
                    | MinusInf, MinusInf -> PlusInf
                    | PlusInf, MinusInf -> MinusInf
                    | MinusInf, PlusInf -> MinusInf
                )
            createVarBound(List.min prods, List.max prods)

let divIntervals i1 i2 =
    match i1, i2 with
    | Bottom, _ | _, Bottom ->
        Bottom

    | Interval(l1,u1), Interval(l2,u2) ->
        let divNoZero (dl,du) : VariableBound =
            let candidates = [ (l1,dl); (l1,du); (u1,dl); (u1,du) ]

            let vals =
                candidates
                |> List.choose (fun (a,b) ->
                    match a,b with
                    | Finite x, Finite y -> Some (Finite (x / y)) // y != 0

                    | PlusInf, Finite k ->
                        if k > 0 then Some PlusInf
                        elif k < 0 then Some MinusInf
                        else None

                    | MinusInf, Finite k ->
                        if k > 0 then Some MinusInf
                        elif k < 0 then Some PlusInf
                        else None

                    | Finite _, PlusInf
                    | Finite _, MinusInf ->
                        Some (Finite 0)

                    // ∞ / ∞ indeterminato
                    | PlusInf, PlusInf
                    | MinusInf, MinusInf
                    | PlusInf, MinusInf
                    | MinusInf, PlusInf ->
                        None
                )
            if List.isEmpty vals then
                createVarBound(MinusInf, PlusInf)
            else
                createVarBound(List.min vals, List.max vals)
        let res =
            if l2 = Finite 0 && u2 = Finite 0 then
                warnings <- warnings |> Set.add "divisione per zero"
                Bottom
            elif containsZero i2 then
                warnings <- warnings |> Set.add "potrebbe dividere per zero"
                let parts =
                    [ if l2 < Finite 0 then yield (l2, Finite -1)
                      if u2 > Finite 0 then yield (Finite 1, u2) ]
                parts
                |> List.map divNoZero
                |> List.reduce joinIntervals
            else
                divNoZero (l2,u2)
        res


let rec evaluateExpr (state:State)(expr:Expr)=
    let inline mk v vars steps = { bound=v; vars=vars; steps=steps }
    match expr with
    | Int v -> mk (Interval(Finite v, Finite v)) Set.empty (Map.empty |> Map.add expr (Interval(Finite v, Finite v)))
    | Var v -> 
        match state with
        | BottomState -> mk Bottom Set.empty (Map.empty |> Map.add expr Bottom)
        | Vars s ->
            let res = s |> Map.tryFind v |> Option.defaultValue Bottom
            mk res (Set.singleton v) (Map.empty |> Map.add expr res)

    | InputInt (lower, upper) -> 
        let res=createVarBound(lower, upper)
        mk res Set.empty (Map.empty |> Map.add expr res)
    | Minus e ->
        let r = evaluateExpr state e
        let res = minusInterval r.bound
        mk res r.vars (r.steps|> Map.add expr res)
    | Add (e1,e2) ->
        let r1 = evaluateExpr state e1
        let r2 = evaluateExpr state e2
        let res = addIntervals r1.bound r2.bound
        mk res (Set.union r1.vars r2.vars) (mergeMaps r1.steps r2.steps |> Map.add expr res )
    | Sub (e1,e2) ->
        let r1 = evaluateExpr state e1
        let r2 = evaluateExpr state e2
        let res = subIntervals r1.bound r2.bound
        mk res (Set.union r1.vars r2.vars) (mergeMaps r1.steps r2.steps |> Map.add expr res )
    | Mul (e1,e2) ->
        let r1 = evaluateExpr state e1
        let r2 = evaluateExpr state e2
        let res = mulIntervals r1.bound r2.bound
        mk res (Set.union r1.vars r2.vars) (mergeMaps r1.steps r2.steps |> Map.add expr res )
    | Div (e1,e2) ->
        let r1 = evaluateExpr state e1
        let r2 = evaluateExpr state e2
        let res = divIntervals r1.bound r2.bound
        mk res (Set.union r1.vars r2.vars) (mergeMaps r1.steps r2.steps |> Map.add expr res )
