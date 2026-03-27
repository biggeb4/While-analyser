module RefineIntervals

open Parser
open Eval
open IntervalDomain
open RefinerCommon

let makeIntervalAssume
    (dom: Domain<VariableBound>)
    (createVarBound: Bound * Bound -> VariableBound)
    : (State<VariableBound> * Cond -> State<VariableBound>) =

    let intersect a b =
        match a, b with
        | Bottom, _
        | _, Bottom -> Bottom
        | _ -> dom.meet a b

    let getLU = function
        | Bottom -> (PlusInf, MinusInf)
        | Interval (l, u) -> (l, u)

    let predBound = function
        | Finite k -> Finite (k - 1)
        | PlusInf -> PlusInf
        | MinusInf -> MinusInf

    let succBound = function
        | Finite k -> Finite (k + 1)
        | PlusInf -> PlusInf
        | MinusInf -> MinusInf

    let assumeAtomInterval (state: State<VariableBound>) (cond: Cond) =
        match state with
        | BottomState -> BottomState
        | _ ->
            match cond with
            | Equi (e1, e2) ->
                let b1 = (evaluateExpr dom state e1).bound
                let b2 = (evaluateExpr dom state e2).bound
                let common = intersect b1 b2
                match common with
                | Bottom -> BottomState
                | _ ->
                    match e1, e2 with
                    | Var x, _ ->
                        refineVarMeet dom state x common
                    | _, Var y ->
                        refineVarMeet dom state y common
                    | _ ->
                        state

            | MinEqui (e1, e2)
            | MagEqui (e2, e1) ->
                let b1 = (evaluateExpr dom state e1).bound
                let b2 = (evaluateExpr dom state e2).bound
                let (l1, _) = getLU b1
                let (_, u2) = getLU b2
                let t1 = createVarBound (MinusInf, u2)
                let t2 = createVarBound (l1, PlusInf)

                match e1, e2 with
                | Var x, Var y ->
                    state
                    |> fun s -> refineVarMeet dom s x t1
                    |> fun s -> refineVarMeet dom s y t2
                | Var x, _ ->
                    refineVarMeet dom state x t1
                | _, Var y ->
                    refineVarMeet dom state y t2
                | _ ->
                    state

            | Min (e1, e2)
            | Mag (e2, e1) ->
                let b1 = (evaluateExpr dom state e1).bound
                let b2 = (evaluateExpr dom state e2).bound
                let (l1, _) = getLU b1
                let (_, u2) = getLU b2
                let t1 = createVarBound (MinusInf, predBound u2)
                let t2 = createVarBound (succBound l1, PlusInf)

                match e1, e2 with
                | Var x, Var y ->
                    state
                    |> fun s -> refineVarMeet dom s x t1
                    |> fun s -> refineVarMeet dom s y t2
                | Var x, _ ->
                    refineVarMeet dom state x t1
                | _, Var y ->
                    refineVarMeet dom state y t2
                | _ ->
                    state

            | Diff (e1, e2) ->
                let b1 = (evaluateExpr dom state e1).bound
                let b2 = (evaluateExpr dom state e2).bound
                match b1, b2 with
                | Interval (Finite a, Finite b), Interval (Finite c, Finite d)
                    when a = b && c = d && a = c ->
                    BottomState
                | _ ->
                    state

            | _ ->
                state

    fun (state, cond) ->
        condWith (joinStates dom) assumeAtomInterval (state, cond)


let makeIntervalRefiner
    (dom: Domain<VariableBound>)
    (createVarBound: Bound * Bound -> VariableBound)
    : (State<VariableBound> * Cond -> State<VariableBound>) =

    let intersect a b =
        match a, b with
        | Bottom, _
        | _, Bottom -> Bottom
        | _ -> dom.meet a b

    let boundOf (trace: Map<Expr, VariableBound>) (e: Expr) =
        trace |> Map.tryFind e |> Option.defaultValue dom.top

    let floorDivInt (a: int) (k: int) =
        if a >= 0 then a / k
        else - ((-a + k - 1) / k)

    let ceilDivInt (a: int) (k: int) =
        if a >= 0 then (a + k - 1) / k
        else - ((-a) / k)

    let floorDivBoundByPos (b: Bound) (k: int) =
        match b with
        | MinusInf -> MinusInf
        | PlusInf -> PlusInf
        | Finite a -> Finite (floorDivInt a k)

    let ceilDivBoundByPos (b: Bound) (k: int) =
        match b with
        | MinusInf -> MinusInf
        | PlusInf -> PlusInf
        | Finite a -> Finite (ceilDivInt a k)

    let preimageByPos (target: VariableBound) (a: int) (b: int) : VariableBound =
        match target with
        | Bottom -> Bottom
        | Interval (tL, tU) ->
            let l1 = ceilDivBoundByPos tL a
            let l2 = ceilDivBoundByPos tL b
            let u1 = floorDivBoundByPos tU a
            let u2 = floorDivBoundByPos tU b
            createVarBound (boundMin l1 l2, boundMax u1 u2)

    let splitNegPos (vb: VariableBound) =
        match vb with
        | Bottom -> Bottom, Bottom
        | Interval (l, u) ->
            let neg =
                if boundLe l (Finite -1) then
                    let uu =
                        if boundLe u (Finite -1) then u
                        else Finite -1
                    createVarBound (l, uu)
                else
                    Bottom

            let pos =
                if boundLe (Finite 1) u then
                    let ll =
                        if boundLe (Finite 1) l then l
                        else Finite 1
                    createVarBound (ll, u)
                else
                    Bottom

            neg, pos

    let enforceNonZero (vb: VariableBound) : VariableBound =
        match vb with
        | Bottom -> Bottom
        | Interval (l, u) ->
            if l = Finite 0 && u = Finite 0 then Bottom
            elif l = Finite 0 then createVarBound (Finite 1, u)
            elif u = Finite 0 then createVarBound (l, Finite -1)
            else vb

    let negateInterval = function
        | Bottom -> Bottom
        | Interval (l, u) -> Interval (negateBound u, negateBound l)

    let refineMulLeft (target: VariableBound) (b2: VariableBound) : VariableBound =
        match target, b2 with
        | Bottom, _
        | _, Bottom -> Bottom

        | _, _ when containsZero b2 && containsZero target ->
            createVarBound (MinusInf, PlusInf)

        | _ ->
            let neg, pos = splitNegPos b2

            let fromPos =
                match pos with
                | Bottom -> Bottom
                | Interval (Finite a, Finite b) ->
                    preimageByPos target a b
                | _ ->
                    createVarBound (MinusInf, PlusInf)

            let fromNeg =
                match neg with
                | Bottom -> Bottom
                | Interval (Finite a, Finite b) ->
                    let za = -b
                    let zb = -a
                    preimageByPos target za zb |> negateInterval
                | _ ->
                    createVarBound (MinusInf, PlusInf)

            dom.join fromNeg fromPos

    let refineDivNumerator (target: VariableBound) (den: VariableBound) : VariableBound =
        match den with
        | Bottom -> Bottom
        | _ ->
            let den' = enforceNonZero den
            match den' with
            | Bottom -> Bottom
            | _ ->
                let neg, pos = splitNegPos den'
                let partMul d =
                    if d = Bottom then Bottom
                    else dom.mul target d
                dom.join (partMul neg) (partMul pos)

    let getLU = function
        | Bottom -> (PlusInf, MinusInf)
        | Interval (l, u) -> (l, u)

    let predBound = function
        | Finite k -> Finite (k - 1)
        | PlusInf -> PlusInf
        | MinusInf -> MinusInf

    let succBound = function
        | Finite k -> Finite (k + 1)
        | PlusInf -> PlusInf
        | MinusInf -> MinusInf

    let isSingleton = function
        | Interval (Finite a, Finite b) when a = b -> Some a
        | _ -> None

    let rec refineExpr
        (state: State<VariableBound>)
        (expr: Expr)
        (target: VariableBound)
        (trace: Map<Expr, VariableBound>) : State<VariableBound> =

        match expr with
        | Int _ -> state
        | InputInt _ -> state

        | Var x ->
            refineVarMeet dom state x target

        | Minus e ->
            let negTarget =
                match target with
                | Bottom -> Bottom
                | Interval (l, u) -> createVarBound (negateBound u, negateBound l)
            refineExpr state e negTarget trace

        | Add (e1, e2) ->
            let b1 = boundOf trace e1
            let b2 = boundOf trace e2
            let t1 = dom.sub target b2
            let t2 = dom.sub target b1
            state
            |> fun s -> refineExpr s e1 t1 trace
            |> fun s -> refineExpr s e2 t2 trace

        | Sub (e1, e2) ->
            let b1 = boundOf trace e1
            let b2 = boundOf trace e2
            let t1 = dom.add target b2
            let t2 = dom.sub b1 target
            state
            |> fun s -> refineExpr s e1 t1 trace
            |> fun s -> refineExpr s e2 t2 trace

        | Mul (e1, e2) ->
            let b2 = boundOf trace e2
            let b1 = boundOf trace e1
            let t1 = refineMulLeft target b2
            let t2 = refineMulLeft target b1
            state
            |> fun s -> refineExpr s e1 t1 trace
            |> fun s -> refineExpr s e2 t2 trace

        | Div (e1, e2) ->
            let b1 = boundOf trace e1
            let b2 = boundOf trace e2
            let t1 = refineDivNumerator target b2
            let t2 = refineMulLeft b1 target |> enforceNonZero
            state
            |> fun s -> refineExpr s e1 t1 trace
            |> fun s -> refineExpr s e2 t2 trace

    let refineAtomInterval (state: State<VariableBound>) (cond: Cond) =
        match cond with
        | Equi (e1, e2) ->
            let ev1 = evaluateExpr dom state e1
            let ev2 = evaluateExpr dom state e2
            let trace = mergeMaps ev1.steps ev2.steps
            let common = intersect ev1.bound ev2.bound
            let s1 = refineExpr state e1 common trace
            refineExpr s1 e2 common trace

        | MinEqui (e1, e2)
        | MagEqui (e2, e1) ->
            let ev1 = evaluateExpr dom state e1
            let ev2 = evaluateExpr dom state e2
            let trace = mergeMaps ev1.steps ev2.steps
            let (l1, _) = getLU ev1.bound
            let (_, u2) = getLU ev2.bound
            let t1 = createVarBound (MinusInf, u2)
            let t2 = createVarBound (l1, PlusInf)
            state
            |> fun s -> refineExpr s e1 t1 trace
            |> fun s -> refineExpr s e2 t2 trace

        | Min (e1, e2)
        | Mag (e2, e1) ->
            let ev1 = evaluateExpr dom state e1
            let ev2 = evaluateExpr dom state e2
            let trace = mergeMaps ev1.steps ev2.steps
            let (l1, _) = getLU ev1.bound
            let (_, u2) = getLU ev2.bound
            let t1 = createVarBound (MinusInf, predBound u2)
            let t2 = createVarBound (succBound l1, PlusInf)
            state
            |> fun s -> refineExpr s e1 t1 trace
            |> fun s -> refineExpr s e2 t2 trace

        | Diff (e1, e2) ->
            let ev1 = evaluateExpr dom state e1
            let ev2 = evaluateExpr dom state e2
            match isSingleton ev1.bound, isSingleton ev2.bound with
            | Some a, Some b when a = b -> BottomState
            | _ -> state

        | _ ->
            state

    fun (state, cond) ->
        condWith (joinStates dom) refineAtomInterval (state, cond)