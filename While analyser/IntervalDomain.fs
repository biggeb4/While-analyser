module IntervalDomain

open Parser
open Eval
open RefinerCommon

type VariableBound =
    | Interval of Bound * Bound
    | Bottom

// ===================================
// Utility sui bound
// ===================================

let boundLe a b =
    match a, b with
    | MinusInf, _ -> true
    | _, PlusInf -> true
    | PlusInf, _ -> false
    | _, MinusInf -> false
    | Finite x, Finite y -> x <= y

let boundLt a b = boundLe a b && a <> b

let boundMin a b = if boundLe a b then a else b
let boundMax a b = if boundLe a b then b else a

let negateBound = function
    | MinusInf -> PlusInf
    | PlusInf -> MinusInf
    | Finite v -> Finite (-v)


let containsZero = function
    | Bottom -> false
    | Interval (lower, upper) ->
        boundLe lower (Finite 0) && boundLe (Finite 0) upper
// ===================================
// Costruttore di intervalli parametrico su [minBound,maxBound]
// ===================================

let makeCreateVarBound (minBound: Bound) (maxBound: Bound) =
    fun (lower: Bound, upper: Bound) ->
        if boundLt upper lower then Bottom
        else
            match minBound, maxBound with
            | MinusInf, PlusInf ->
                Interval (lower, upper)
            | Finite m, Finite n ->
                match lower, upper with
                | Finite l, Finite u when m <= l && u <= n ->
                    Interval (Finite l, Finite u)
                | _, Finite u when m <= u && u <= n ->
                    Interval (MinusInf, Finite u)
                | Finite l, _ when m <= l && l <= n ->
                    Interval (Finite l, PlusInf)
                | _, _ when boundLe lower (Finite m) && boundLe (Finite n) upper ->
                    Interval (MinusInf, PlusInf)
                | _ ->
                    Interval (MinusInf, PlusInf)
            | _ ->
                Interval (lower, upper)

// ===================================
// Costruttore del dominio parametrico Int_{m,n}
// ===================================

let makeIntervalDomain (minBound: Bound) (maxBound: Bound) : Domain<VariableBound> =
    let createVarBound = makeCreateVarBound minBound maxBound
    // ===================================
    // Predicati sugli intervalli
    // ===================================

    let hasUnbounded = function
        | Bottom -> false
        | Interval (lower, upper) ->
            match lower, upper with
            | Finite _, Finite _ -> false
            | _ -> true

    // ===================================
    // Ordine / join / meet
    // ===================================

    let leqIntervals a b =
        match a, b with
        | Bottom, _ -> true
        | _, Bottom -> false
        | Interval (l1, u1), Interval (l2, u2) ->
            boundLe l2 l1 && boundLe u1 u2

    let joinIntervals a b =
        match a, b with
        | Bottom, x
        | x, Bottom -> x
        | Interval (l1, u1), Interval (l2, u2) ->
            Interval (boundMin l1 l2, boundMax u1 u2)

    let meetIntervals a b =
        match a, b with
        | Bottom, _
        | _, Bottom -> Bottom
        | Interval (l1, u1), Interval (l2, u2) ->
            createVarBound (boundMax l1 l2, boundMin u1 u2)

    // ===================================
    // Operazioni forward
    // ===================================

    let minusInterval = function
        | Bottom -> Bottom
        | Interval (l, u) -> Interval (negateBound u, negateBound l)

    let addIntervals a b =
        match a, b with
        | Bottom, _
        | _, Bottom -> Bottom
        | Interval (l1, u1), Interval (l2, u2) ->
            let newLower =
                match l1, l2 with
                | Finite v1, Finite v2 -> Finite (v1 + v2)
                | MinusInf, _ | _, MinusInf -> MinusInf
                | PlusInf, _ | _, PlusInf -> PlusInf

            let newUpper =
                match u1, u2 with
                | Finite v1, Finite v2 -> Finite (v1 + v2)
                | MinusInf, _ | _, MinusInf -> MinusInf
                | PlusInf, _ | _, PlusInf -> PlusInf

            createVarBound (newLower, newUpper)

    let subIntervals a b =
        match a, b with
        | Bottom, _
        | _, Bottom -> Bottom
        | Interval (l1, u1), Interval (l2, u2) ->
            let newLower =
                match l1, u2 with
                | Finite v1, Finite v2 -> Finite (v1 - v2)
                | MinusInf, _ | _, PlusInf -> MinusInf
                | PlusInf, _ | _, MinusInf -> PlusInf

            let newUpper =
                match u1, l2 with
                | Finite v1, Finite v2 -> Finite (v1 - v2)
                | MinusInf, _ | _, PlusInf -> MinusInf
                | PlusInf, _ | _, MinusInf -> PlusInf

            createVarBound (newLower, newUpper)

    let mulIntervals a b =
        match a, b with
        | Bottom, _
        | _, Bottom -> Bottom
        | i1, i2 ->
            if (hasUnbounded i1 && containsZero i2) || (hasUnbounded i2 && containsZero i1) then
                createVarBound (MinusInf, PlusInf)
            else
                let (Interval (l1, u1)) = i1
                let (Interval (l2, u2)) = i2

                let candidates = [ (l1, l2); (l1, u2); (u1, l2); (u1, u2) ]

                let prods =
                    candidates
                    |> List.map (fun (a, b) ->
                        match a, b with
                        | Finite 0, _ | _, Finite 0 -> Finite 0
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

                let newLower = prods |> List.reduce boundMin
                let newUpper = prods |> List.reduce boundMax
                createVarBound (newLower, newUpper)

    let divIntervals a b =
        match a, b with
        | Bottom, _
        | _, Bottom -> Bottom
        | Interval (l1, u1), Interval (l2, u2) ->

            let divNoZero (dl, du) =
                let candidates = [ (l1, dl); (l1, du); (u1, dl); (u1, du) ]

                let vals =
                    candidates
                    |> List.choose (fun (x, y) ->
                        match x, y with
                        | Finite vx, Finite vy -> Some (Finite (vx / vy))

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

                        // ∞ / ∞ → indeterminato: scarto
                        | PlusInf, PlusInf
                        | MinusInf, MinusInf
                        | PlusInf, MinusInf
                        | MinusInf, PlusInf ->
                            None
                    )

                if List.isEmpty vals then
                    createVarBound (MinusInf, PlusInf)
                else
                    createVarBound (List.reduce boundMin vals, List.reduce boundMax vals)

            // denominatore esattamente zero
            if l2 = Finite 0 && u2 = Finite 0 then
                warnings<-warnings.Add ("Divisione per zero")
                Bottom

            // denominatore contiene zero: split
            elif containsZero b then
                warnings<-warnings.Add ("Potrebbe dividere per zero")
                let parts =
                    [ if boundLt l2 (Finite 0) then yield (l2, Finite -1)
                      if boundLt (Finite 0) u2 then yield (Finite 1, u2) ]

                parts
                |> List.map divNoZero
                |> List.reduce joinIntervals

            else
                divNoZero (l2, u2)

    // ===================================
    // Widening / Narrowing
    // ===================================

    let widenIntervals minBound maxBound oldB newB =
        let createVarBound = makeCreateVarBound minBound maxBound
        match oldB, newB with
        | Bottom, b -> b
        | b, Bottom -> b
        | Interval (l1, u1), Interval (l2, u2) ->
            let wl =
                if boundLt l2 l1 then minBound else l1
            let wu =
                if boundLt u1 u2 then maxBound else u1
            createVarBound (wl, wu)

    let narrowIntervals oldB newB =
        meetIntervals oldB newB
    
    let dom=
        { bottom = Bottom
          top = createVarBound (MinusInf, PlusInf)

          leq = leqIntervals
          join = joinIntervals
          meet = meetIntervals

          widen = widenIntervals minBound maxBound
          narrow = narrowIntervals

          neg = minusInterval
          add = addIntervals
          sub = subIntervals
          mul = mulIntervals
          div = divIntervals

          constInt = fun n -> createVarBound (Finite n, Finite n)
          inputInt = fun (l, u) -> createVarBound (l, u)
          AssumeAndRefine = (fun _ -> failwith "interval AssumeAndRefine not initialized") }

    // ===================================
    // Refine
    // ===================================

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
                state

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

    let refine = makeIntervalRefiner dom createVarBound

    { dom with
        AssumeAndRefine = refine }