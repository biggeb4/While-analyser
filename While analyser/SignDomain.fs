module SignDomain

open Parser
open Eval
open RefinerCommon

type SignValue =
    | Bottom
    | Neg
    | Zero
    | Pos
    | NonPos
    | NonZero
    | NonNeg
    | Top

type private AtomSign =
    | ANeg
    | AZero
    | APos

let private atomsOf = function
    | Bottom -> Set.empty
    | Neg -> Set.ofList [ ANeg ]
    | Zero -> Set.ofList [ AZero ]
    | Pos -> Set.ofList [ APos ]
    | NonPos -> Set.ofList [ ANeg; AZero ]
    | NonZero -> Set.ofList [ ANeg; APos ]
    | NonNeg -> Set.ofList [ AZero; APos ]
    | Top -> Set.ofList [ ANeg; AZero; APos ]

let private signOfAtoms atoms =
    match atoms with
    | s when Set.isEmpty s -> Bottom
    | s when s = Set.ofList [ ANeg ] -> Neg
    | s when s = Set.ofList [ AZero ] -> Zero
    | s when s = Set.ofList [ APos ] -> Pos
    | s when s = Set.ofList [ ANeg; AZero ] -> NonPos
    | s when s = Set.ofList [ ANeg; APos ] -> NonZero
    | s when s = Set.ofList [ AZero; APos ] -> NonNeg
    | _ -> Top

let leqSign a b =
    Set.isSubset (atomsOf a) (atomsOf b)

let joinSign a b =
    Set.union (atomsOf a) (atomsOf b) |> signOfAtoms

let meetSign a b =
    Set.intersect (atomsOf a) (atomsOf b) |> signOfAtoms

let private negAtom = function
    | ANeg -> APos
    | AZero -> AZero
    | APos -> ANeg

let negSign s =
    atomsOf s
    |> Set.map negAtom
    |> signOfAtoms

let private addAtom a b =
    match a, b with
    | AZero, x
    | x, AZero -> Set.singleton x
    | ANeg, ANeg -> Set.singleton ANeg
    | APos, APos -> Set.singleton APos
    | ANeg, APos
    | APos, ANeg -> Set.ofList [ ANeg; AZero; APos ]

let private subAtom a b =
    addAtom a (negAtom b)

let private mulAtom a b =
    match a, b with
    | AZero, _
    | _, AZero -> Set.singleton AZero
    | ANeg, ANeg
    | APos, APos -> Set.singleton APos
    | ANeg, APos
    | APos, ANeg -> Set.singleton ANeg

let private divAtom a b =
    match a, b with
    | _, AZero -> Set.empty
    | AZero, _ -> Set.singleton AZero
    | ANeg, ANeg
    | APos, APos -> Set.singleton APos
    | ANeg, APos
    | APos, ANeg -> Set.singleton ANeg

let private liftBinary atomOp x y =
    let xs = atomsOf x
    let ys = atomsOf y

    seq {
        for a in xs do
            for b in ys do
                yield! atomOp a b
    }
    |> Set.ofSeq
    |> signOfAtoms

let addSign x y = liftBinary addAtom x y
let subSign x y = liftBinary subAtom x y
let mulSign x y = liftBinary mulAtom x y

let divSign x y =
    if y = Bottom then Bottom
    elif y = Zero then 
        warnings<-warnings.Add ("Divisione per zero")
        Bottom
    else
        if (atomsOf y).Contains AZero then
            warnings<-warnings.Add ("Potrebbe dividere per zero")
        let ys = atomsOf y |> Set.remove AZero
        if Set.isEmpty ys then Bottom
        else
            let xs = atomsOf x
            seq {
                for a in xs do
                    for b in ys do
                        yield! divAtom a b
            }
            |> Set.ofSeq
            |> signOfAtoms

let widenSign a b = joinSign a b
let narrowSign a b = meetSign a b

let constInt n =
    if n < 0 then Neg
    elif n = 0 then Zero
    else Pos

let inputInt (l, u) =
    match l, u with
    | Finite a, Finite b when b < a -> Bottom
    | Finite a, Finite b when a = 0 && b = 0 -> Zero
    | Finite a, Finite b when b < 0 -> Neg
    | Finite a, Finite b when a > 0 -> Pos
    | Finite a, Finite b when a >= 0 -> NonNeg
    | Finite a, Finite b when b <= 0 -> NonPos
    | Finite a, Finite b when a < 0 && b > 0 -> Top
    | MinusInf, Finite b when b < 0 -> Neg
    | MinusInf, Finite 0 -> NonPos
    | Finite a, PlusInf when a > 0 -> Pos
    | Finite 0, PlusInf -> NonNeg
    | _ -> Top

let private meetVar dom state x s =
    refineVarMeet dom state x s

let private signOfInt n =
    if n < 0 then Neg
    elif n = 0 then Zero
    else Pos

let makeSignRefiner (dom: Domain<SignValue>) : (State<SignValue> * Cond -> State<SignValue>) =

    let rec assumeAtom (state: State<SignValue>) (cond: Cond) =
        match state with
        | BottomState -> BottomState
        | _ ->
            match cond with
            | Equi (Var x, Int c)
            | Equi (Int c, Var x) ->
                meetVar dom state x (signOfInt c)

            | Diff (Var x, Int 0)
            | Diff (Int 0, Var x) ->
                meetVar dom state x NonZero

            | Equi (Var x, Var y) ->
                let sx = (evaluateExpr dom state (Var x)).bound
                let sy = (evaluateExpr dom state (Var y)).bound
                match sx, sy with
                | Neg, _ -> meetVar dom state y Neg
                | Zero, _ -> meetVar dom state y Zero
                | Pos, _ -> meetVar dom state y Pos
                | _, Neg -> meetVar dom state x Neg
                | _, Zero -> meetVar dom state x Zero
                | _, Pos -> meetVar dom state x Pos
                | _ -> state

            | Min (Var x, Int 0)
            | Mag (Int 0, Var x) ->
                meetVar dom state x Neg

            | MinEqui (Var x, Int 0)
            | MagEqui (Int 0, Var x) ->
                meetVar dom state x NonPos

            | Mag (Var x, Int 0)
            | Min (Int 0, Var x) ->
                meetVar dom state x Pos

            | MagEqui (Var x, Int 0)
            | MinEqui (Int 0, Var x) ->
                meetVar dom state x NonNeg

            | Min (Var x, Int c) ->
                if c <= 0 then meetVar dom state x NonPos else state

            | MinEqui (Var x, Int c) ->
                if c < 0 then meetVar dom state x Neg
                elif c = 0 then meetVar dom state x NonPos
                else state

            | Mag (Var x, Int c) ->
                if c >= 0 then meetVar dom state x NonNeg else state

            | MagEqui (Var x, Int c) ->
                if c > 0 then meetVar dom state x Pos
                elif c = 0 then meetVar dom state x NonNeg
                else state

            | MinEqui (Var x, Var y) ->
                let sx = (evaluateExpr dom state (Var x)).bound
                let sy = (evaluateExpr dom state (Var y)).bound

                let s1 =
                    if sy = Neg || sy = Zero || sy = NonPos then
                        meetVar dom state x NonPos
                    else
                        state

                let s2 =
                    if sx = Pos || sx = Zero || sx = NonNeg then
                        meetVar dom s1 y NonNeg
                    else
                        s1

                s2

            | Min (Var x, Var y) ->
                let sx = (evaluateExpr dom state (Var x)).bound
                let sy = (evaluateExpr dom state (Var y)).bound

                let s1 =
                    if sy = Neg || sy = Zero || sy = NonPos then
                        meetVar dom state x Neg
                    else
                        state

                let s2 =
                    if sx = Pos || sx = Zero || sx = NonNeg then
                        meetVar dom s1 y Pos
                    else
                        s1

                s2

            | Diff (Var x, Var y) ->
                let sx = (evaluateExpr dom state (Var x)).bound
                let sy = (evaluateExpr dom state (Var y)).bound
                match sx, sy with
                | Zero, Zero
                | Neg, Neg
                | Pos, Pos -> BottomState
                | _ -> state

            | _ ->
                state

    fun (state, cond) ->
        condWith (joinStates dom) assumeAtom (state, cond)

let makeSignDomain () : Domain<SignValue> =
    let dom =
        { bottom = Bottom
          top = Top

          leq = leqSign
          join = joinSign
          meet = meetSign

          widen = widenSign
          narrow = narrowSign

          neg = negSign
          add = addSign
          sub = subSign
          mul = mulSign
          div = divSign

          constInt = constInt
          inputInt = inputInt

          AssumeAndRefine = (fun _ -> failwith "sign AssumeAndRefine not initialized") }

    let refine = makeSignRefiner dom

    { dom with
        AssumeAndRefine = refine }