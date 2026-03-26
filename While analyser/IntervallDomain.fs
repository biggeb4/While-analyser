module IntervalDomain

open Parser
open Eval

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
        let l = boundMax minBound lower
        let u = boundMin maxBound upper
        if boundLt u l then Bottom
        else Interval (l, u)

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

    let isPositive = function
        | Bottom -> false
        | Interval (lower, upper) ->
            match lower, upper with
            | Finite l, Finite u -> l > 0 && u > 0
            | PlusInf, _ -> true
            | _, MinusInf -> true
            | _ -> false

    let isNegative = function
        | Bottom -> false
        | Interval (lower, upper) ->
            match lower, upper with
            | Finite l, Finite u -> l < 0 && u < 0
            | MinusInf, _ -> false
            | _, PlusInf -> false
            | _ -> false

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
                Bottom

            // denominatore contiene zero: split
            elif containsZero b then
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

      refine = None }