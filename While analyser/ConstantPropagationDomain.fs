module ConstantPropagationDomain

open Parser
open Eval
open RefinerCommon

type ConstantValue =
    | Bottom
    | Const of int
    | Top

// ===================================
// Ordine di lattice
// Bottom <= Const k <= Top
// Const a e Const b incomparabili se a <> b
// ===================================

let leqConst a b =
    match a, b with
    | Bottom, _ -> true
    | _, Top -> true
    | Top, _ -> (b = Top)
    | Const x, Const y -> x = y
    | _, _ -> false

let joinConst a b =
    match a, b with
    | Bottom, x
    | x, Bottom -> x
    | Top, _
    | _, Top -> Top
    | Const x, Const y ->
        if x = y then Const x else Top

let meetConst a b =
    match a, b with
    | Bottom, _
    | _, Bottom -> Bottom
    | Top, x
    | x, Top -> x
    | Const x, Const y ->
        if x = y then Const x else Bottom

// ===================================
// Operazioni forward
// ===================================

let negConst = function
    | Bottom -> Bottom
    | Top -> Top
    | Const x -> Const (-x)

let addConst a b =
    match a, b with
    | Bottom, _
    | _, Bottom -> Bottom
    | Const x, Const y -> Const (x + y)
    | _ -> Top

let subConst a b =
    match a, b with
    | Bottom, _
    | _, Bottom -> Bottom
    | Const x, Const y -> Const (x - y)
    | _ -> Top

let mulConst a b =
    match a, b with
    | Bottom, _
    | _, Bottom -> Bottom

    | Const 0, _
    | _, Const 0 -> Const 0

    | Const x, Const y -> Const (x * y)

    | _ -> Top

let divConst a b =
    match a, b with
    | Bottom, _
    | _, Bottom -> Bottom
    | _, Const 0 -> Bottom
    | Const x, Const y -> Const (x / y)
    | _ -> Top

// ===================================
// Widening / Narrowing
// ===================================

let widenConst a b =
    joinConst a b

let narrowConst a b =
    meetConst a b

// ===================================
// Costruttori astratti
// ===================================

let constInt n = Const n

let inputInt (lower, upper) =
    match lower, upper with
    | Finite l, Finite u when l = u -> Const l
    | Finite l, Finite u when l > u -> Bottom
    | _ -> Top

// ===================================
// Refiner per constant propagation
// ===================================

let makeConstantPropagationRefiner (dom: Domain<ConstantValue>) : (State<ConstantValue> * Cond -> State<ConstantValue>) =

    let boundOf (trace: Map<Expr, ConstantValue>) (e: Expr) =
        trace |> Map.tryFind e |> Option.defaultValue dom.top

    let rec refineExprToConst
        (state: State<ConstantValue>)
        (expr: Expr)
        (target: ConstantValue)
        (trace: Map<Expr, ConstantValue>) : State<ConstantValue> =

        match state with
        | BottomState -> BottomState
        | _ ->
            match target with
            | Bottom -> BottomState
            | Top -> state
            | Const k ->
                match expr with
                | Int n ->
                    if n = k then state else BottomState

                | InputInt (Finite l, Finite u) ->
                    if l <= k && k <= u then state else BottomState

                | InputInt _ ->
                    state

                | Var x ->
                    refineVarMeet dom state x (Const k)

                | Minus e ->
                    refineExprToConst state e (Const (-k)) trace

                | Add (e1, e2) ->
                    let b1 = boundOf trace e1
                    let b2 = boundOf trace e2

                    match b1, b2 with
                    | Const c1, _ ->
                        refineExprToConst state e2 (Const (k - c1)) trace
                    | _, Const c2 ->
                        refineExprToConst state e1 (Const (k - c2)) trace
                    | _ ->
                        state

                | Sub (e1, e2) ->
                    let b1 = boundOf trace e1
                    let b2 = boundOf trace e2

                    match b1, b2 with
                    | Const c1, _ ->
                        refineExprToConst state e2 (Const (c1 - k)) trace
                    | _, Const c2 ->
                        refineExprToConst state e1 (Const (k + c2)) trace
                    | _ ->
                        state

                | Mul (e1, e2) ->
                    let b1 = boundOf trace e1
                    let b2 = boundOf trace e2

                    match b1, b2 with
                    | Const c1, _ ->
                        if c1 = 0 then
                            if k = 0 then state else BottomState
                        elif k % c1 = 0 then
                            refineExprToConst state e2 (Const (k / c1)) trace
                        else
                            BottomState

                    | _, Const c2 ->
                        if c2 = 0 then
                            if k = 0 then state else BottomState
                        elif k % c2 = 0 then
                            refineExprToConst state e1 (Const (k / c2)) trace
                        else
                            BottomState

                    | _ ->
                        state

                | Div (e1, e2) ->
                    let b2 = boundOf trace e2

                    match b2 with
                    | Const 0 ->
                        BottomState
                    | Const 1 ->
                        refineExprToConst state e1 (Const k) trace
                    | Const -1 ->
                        refineExprToConst state e1 (Const (-k)) trace
                    | _ ->
                        state

    let assumeAtomConst (state: State<ConstantValue>) (cond: Cond) =
        match cond with
        | Equi (e1, e2) ->
            let ev1 = evaluateExpr dom state e1
            let ev2 = evaluateExpr dom state e2
            let trace = mergeMaps ev1.steps ev2.steps

            match ev1.bound, ev2.bound with
            | Bottom, _
            | _, Bottom ->
                BottomState

            | Const c1, Const c2 ->
                if c1 = c2 then state else BottomState

            | Const c, _ ->
                refineExprToConst state e2 (Const c) trace

            | _, Const c ->
                refineExprToConst state e1 (Const c) trace

            | _ ->
                state

        | Diff (e1, e2) ->
            let ev1 = evaluateExpr dom state e1
            let ev2 = evaluateExpr dom state e2

            match ev1.bound, ev2.bound with
            | Bottom, _
            | _, Bottom ->
                BottomState

            | Const c1, Const c2 ->
                if c1 = c2 then BottomState else state

            | _ ->
                state

        | Min (e1, e2)
        | Mag (e2, e1) ->
            let ev1 = evaluateExpr dom state e1
            let ev2 = evaluateExpr dom state e2

            match ev1.bound, ev2.bound with
            | Bottom, _
            | _, Bottom ->
                BottomState

            | Const c1, Const c2 ->
                if c1 < c2 then state else BottomState

            | _ ->
                state

        | MinEqui (e1, e2)
        | MagEqui (e2, e1) ->
            let ev1 = evaluateExpr dom state e1
            let ev2 = evaluateExpr dom state e2

            match ev1.bound, ev2.bound with
            | Bottom, _
            | _, Bottom ->
                BottomState

            | Const c1, Const c2 ->
                if c1 <= c2 then state else BottomState

            | _ ->
                state

        | _ ->
            state

    fun (state, cond) ->
        assumeCondWith (joinStates dom) assumeAtomConst (state, cond)

// ===================================
// Dominio
// ===================================

let makeConstantPropagationDomain () : Domain<ConstantValue> =
    let dom =
        { bottom = Bottom
          top = Top

          leq = leqConst
          join = joinConst
          meet = meetConst

          widen = widenConst
          narrow = narrowConst

          neg = negConst
          add = addConst
          sub = subConst
          mul = mulConst
          div = divConst

          constInt = constInt
          inputInt = inputInt

          refine = None }

    let refiner = makeConstantPropagationRefiner dom
    { dom with refine = Some refiner }