module CongruenceDomain

open Parser
open Eval
open RefinerCommon

// ======================================================
// DOMINIO DELLE CONGRUENZE
//
//convenzioni:
//
//   Cong (0, c) = costante esatta {c}
//   Cong (1, 0) = Top = Z
//   Cong (m, r) con m > 0 = { x in Z | x ≡ r (mod m) }
//
// La normalizzazione impone:
//   - m >= 0
//   - se m > 0 allora 0 <= r < m
// ======================================================

type CongruenceValue =
    | Bottom
    | Cong of int * int

// ======================================================
// Utility aritmetiche di base
// ======================================================

let rec gcd a b =
    let a = abs a
    let b = abs b
    if b = 0 then a else gcd b (a % b)

let private gcd3 a b c =
    gcd (gcd a b) c

let private lcm a b =
    let a = abs a
    let b = abs b
    if a = 0 || b = 0 then 0
    else (a / gcd a b) * b

let private modNorm a m =
    if m <= 0 then a
    else
        let r = a % m
        if r < 0 then r + m else r

let private divisibleBy a b =
    b <> 0 && a % b = 0

let private congruentMod a b m =
    if m = 0 then a = b
    else modNorm (a - b) m = 0

// ======================================================
// Normalizzazione dei valori astratti
// ======================================================

let normalizeCong = function
    | Bottom -> Bottom
    | Cong (m, r) ->
        if m < 0 then
            let mm = -m
            if mm = 0 then Cong (0, r)
            else Cong (mm, modNorm r mm)
        elif m = 0 then
            Cong (0, r)
        else
            let rr = modNorm r m
            Cong (m, rr)

let topCong = Cong (1, 0)

let constCong c = Cong (0, c)

// ======================================================
// Predicati concreti
// ======================================================

let isBottom = function
    | Bottom -> true
    | _ -> false

let isConst = function
    | Cong (0, c) -> Some c
    | _ -> None

let containsValue n = function
    | Bottom -> false
    | Cong (0, c) -> n = c
    | Cong (m, r) -> congruentMod n r m

let mayContainZero v =
    containsValue 0 v

let isTop = function
    | Cong (1, 0) -> true
    | _ -> false

// ======================================================
// Ordine di lattice
// ======================================================

let leqCong a b =
    let a = normalizeCong a
    let b = normalizeCong b

    match a, b with
    | Bottom, _ -> true
    | _, Bottom -> false

    | Cong (0, c1), Cong (0, c2) ->
        c1 = c2

    | Cong (0, c), Cong (m, r) ->
        congruentMod c r m

    | Cong (m, r), Cong (0, c) ->
        m = 0 && r = c

    | Cong (m1, r1), Cong (m2, r2) ->
        divisibleBy m1 m2 && congruentMod r1 r2 m2

// ======================================================
// Join
// Il join di due congruenze è la più piccola congruenza
// che contiene entrambe.
// ======================================================

let joinCong a b =
    let a = normalizeCong a
    let b = normalizeCong b

    match a, b with
    | Bottom, x
    | x, Bottom -> x

    | Cong (0, c1), Cong (0, c2) ->
        if c1 = c2 then
            Cong (0, c1)
        else
            let d = abs (c1 - c2)
            normalizeCong (Cong (d, c1))

    | Cong (m1, r1), Cong (m2, r2) ->
        let d = gcd3 m1 m2 (r1 - r2)
        if d = 0 then
            // succede solo se erano la stessa costante
            Cong (0, r1)
        else
            normalizeCong (Cong (d, r1))

// ======================================================
// Meet, teorema cinese del resto
// ======================================================

let private extendedgcd a b =
    let rec loop a b x0 y0 x1 y1 =
        if b = 0 then (a, x0, y0)
        else
            let q = a / b
            loop b (a - q * b) x1 y1 (x0 - q * x1) (y0 - q * y1)
    loop a b 1 0 0 1

let private meetGeneralCongruences m1 r1 m2 r2 =
    let g = gcd m1 m2

    if not (congruentMod r1 r2 g) then
        Bottom
    else
        let m1' = m1 / g
        let m2' = m2 / g
        let rhs = (r2 - r1) / g

        let (_, inv, _) = extendedgcd m1' m2'
        let t = modNorm (rhs * inv) m2'
        let modulus = lcm m1 m2
        let residue = r1 + m1 * t
        normalizeCong (Cong (modulus, residue))

let meetCong a b =
    let a = normalizeCong a
    let b = normalizeCong b

    match a, b with
    | Bottom, _
    | _, Bottom -> Bottom

    | Cong (0, c1), Cong (0, c2) ->
        if c1 = c2 then Cong (0, c1) else Bottom

    | Cong (0, c), Cong (m, r)
    | Cong (m, r), Cong (0, c) ->
        if congruentMod c r m then Cong (0, c) else Bottom

    | Cong (m1, r1), Cong (m2, r2) ->
        meetGeneralCongruences m1 r1 m2 r2

// ======================================================
// Operazioni forward
// ======================================================

let negCong = function
    | Bottom -> Bottom
    | Cong (0, c) -> Cong (0, -c)
    | Cong (m, r) -> normalizeCong (Cong (m, -r))

let addCong a b =
    let a = normalizeCong a
    let b = normalizeCong b

    match a, b with
    | Bottom, _
    | _, Bottom -> Bottom

    | Cong (0, c1), Cong (0, c2) ->
        Cong (0, c1 + c2)

    | Cong (m1, r1), Cong (m2, r2) ->
        let g = gcd m1 m2
        if g = 0 then
            Cong (0, r1 + r2)
        else
            normalizeCong (Cong (g, r1 + r2))

let subCong a b =
    addCong a (negCong b)

let mulCong a b =
    let a = normalizeCong a
    let b = normalizeCong b

    match a, b with
    | Bottom, _
    | _, Bottom -> Bottom

    | Cong (0, c1), Cong (0, c2) ->
        Cong (0, c1 * c2)

    | Cong (m1, r1), Cong (m2, r2) ->
        let g = gcd3 (m1 * m2) (m1 * r2) (m2 * r1)
        if g = 0 then
            Cong (0, r1 * r2)
        else
            normalizeCong (Cong (g, r1 * r2))

let divCong a b =
    let a = normalizeCong a
    let b = normalizeCong b

    match a, b with
    | Bottom, _
    | _, Bottom -> Bottom, None

    | _, Cong (0, 0) ->
        Bottom,Some { name = DivisionByZero; critical = true }

    | Cong (0, c1), Cong (0, c2) ->
        Cong (0, c1 / c2), None

    | _, Cong (0, 1) ->
        a, None

    | _, Cong (0, -1) ->
        negCong a, None

    | Cong (0, 0), den ->
        if mayContainZero den then 
            topCong, Some { name = MayDivideByZero; critical = false }
        else Cong (0, 0), None
    | _,den ->
        if mayContainZero den then
            topCong, Some { name = MayDivideByZero; critical = false }
        else
            topCong, None

// ======================================================
// Widening / Narrowing
// ======================================================

let widenCong a b = joinCong a b
let narrowCong a b = meetCong a b

// ======================================================
// Costruttori astratti
// ======================================================

let constInt n =
    Cong (0, n)

let inputInt (lower, upper) =
    match lower, upper with
    | Finite l, Finite u when l > u ->
        Bottom
    | Finite l, Finite u when l = u ->
        Cong (0, l)
    | _ ->
        topCong

// ======================================================
// Backward refinement su espressioni
// ======================================================

let makeCongruenceDomain () : Domain<CongruenceValue> =
    let dom =
        { bottom = Bottom
          top = topCong
          zero = constCong 0

          leq = leqCong
          join = joinCong
          meet = meetCong

          widen = widenCong
          narrow = narrowCong

          neg = negCong
          add = addCong
          sub = subCong
          mul = mulCong
          div = divCong

          constInt = constInt
          inputInt = inputInt

          AssumeAndRefine = (fun _ -> failwith "congruence AssumeAndRefine not initialized") }

    let boundOf (trace: Map<Expr, CongruenceValue>) (e: Expr) =
        trace |> Map.tryFind e |> Option.defaultValue dom.top

    let rec refineExprCong
        (state: State<CongruenceValue>)
        (expr: Expr)
        (target: CongruenceValue)
        (trace: Map<Expr, CongruenceValue>) : State<CongruenceValue> =

        match state with
        | BottomState ->
            BottomState
        | _ ->
            match target with
            | Bottom ->
                BottomState

            | _ ->
                match expr with
                | Int n ->
                    if dom.leq (Cong (0, n)) target then state else BottomState

                | InputInt (Finite l, Finite u) when l = u ->
                    if dom.leq (Cong (0, l)) target then state else BottomState

                | InputInt _ ->
                    state

                | Var x ->
                    refineVarMeet dom state x target

                | Minus e ->
                    let t = dom.neg target
                    refineExprCong state e t trace

                | Add (e1, e2) ->
                    let b1 = boundOf trace e1
                    let b2 = boundOf trace e2
                    let t1 = dom.sub target b2
                    let t2 = dom.sub target b1

                    state
                    |> fun s -> refineExprCong s e1 t1 trace
                    |> fun s -> refineExprCong s e2 t2 trace

                | Sub (e1, e2) ->
                    let b1 = boundOf trace e1
                    let b2 = boundOf trace e2
                    let t1 = dom.add target b2
                    let t2 = dom.sub b1 target

                    state
                    |> fun s -> refineExprCong s e1 t1 trace
                    |> fun s -> refineExprCong s e2 t2 trace

                | Mul _ -> state

                | Div (_, e2) ->
                    let den = boundOf trace e2
                    match den with
                    | Cong (0, 0) -> 
                        BottomState
                    | _ -> state

    let assumeAtomCong (state: State<CongruenceValue>) (cond: Cond) =
        match state with
        | BottomState ->
            BottomState
        | _ ->
            match cond with
            | Equi (e1, e2) ->
                let ev1 = evaluateExpr dom state e1
                let ev2 = evaluateExpr dom state e2
                let trace = mergeMaps ev1.steps ev2.steps
                let common = dom.meet ev1.bound ev2.bound
                if ev1.EvalError || ev2.EvalError then BottomState
                else
                    match common with
                    | Bottom ->
                        BottomState
                    | _ ->
                        state
                        |> fun s -> refineExprCong s e1 common trace
                        |> fun s -> refineExprCong s e2 common trace

            | Diff (e1, e2) ->
                let ev1 = evaluateExpr dom state e1
                let ev2 = evaluateExpr dom state e2
                
                if ev1.EvalError || ev2.EvalError then BottomState
                else
                    match ev1.bound, ev2.bound with
                    | Cong (0, c1), Cong (0, c2) when c1 = c2 ->
                        BottomState
                    | _ ->
                        state

            | Min (e1, e2) | Mag(e2,e1) ->
                let ev1 = (evaluateExpr dom state e1)
                let ev2 = (evaluateExpr dom state e2)
                
                if ev1.EvalError || ev2.EvalError then BottomState
                else
                    match ev1.bound, ev2.bound with
                    | Cong (0, c1), Cong (0, c2) ->
                        if c1 < c2 then state else BottomState
                    | _ ->
                        state

            | MinEqui (e1, e2) | MagEqui(e2,e1) ->
                let ev1 = (evaluateExpr dom state e1)
                let ev2 = (evaluateExpr dom state e2)
                
                if ev1.EvalError || ev2.EvalError then BottomState
                else
                    match ev1.bound, ev2.bound with
                    | Cong (0, c1), Cong (0, c2) ->
                        if c1 <= c2 then state else BottomState
                    | _ ->
                        state

            | _ ->
                state

    let assumeAndRefine (state, cond) =
        condWith (joinStates dom) assumeAtomCong (state, cond)

    { dom with
        AssumeAndRefine = assumeAndRefine }