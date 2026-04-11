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
    if y = Bottom then
        Bottom, None
    elif y = Zero then
        Bottom, Some { name = DivisionByZero; critical = true }
    else
        let w =
            if atomsOf y |> Set.contains AZero then
                Some { name = MayDivideByZero; critical = false }
            else
                None

        let ys = atomsOf y |> Set.remove AZero
        let xs = atomsOf x

        let res =
            seq {
                for a in xs do
                    for b in ys do
                        yield! divAtom a b
            }
            |> Set.ofSeq
            |> signOfAtoms

        res, w

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

let private containsZero = function
    | Zero
    | NonPos
    | NonNeg
    | Top -> true
    | _ -> false

let private refineMulLeft target other =
    match other with
    | Bottom -> Bottom
    | Pos -> target
    | Neg -> negSign target
    | Zero ->
        if containsZero target then Top else Bottom
    | NonNeg ->
        if target = Pos then NonNeg
        elif target = Neg then NonPos
        elif target = Zero then Top
        elif target = NonNeg then Top
        elif target = NonPos then Top
        elif target = NonZero then Top
        else Top
    | NonPos ->
        if target = Pos then NonPos
        elif target = Neg then NonNeg
        elif target = Zero then Top
        elif target = NonNeg then Top
        elif target = NonPos then Top
        elif target = NonZero then Top
        else Top
    | NonZero ->
        if target = Zero then Zero
        else Top
    | Top -> Top

let makeSignRefiner (dom: Domain<SignValue>) : (State<SignValue> * Cond -> State<SignValue>) =

    let boundOf (trace: Map<Expr, SignValue>) (e: Expr) =
        trace |> Map.tryFind e |> Option.defaultValue Top

    let rec refineExpr
        (state: State<SignValue>)
        (expr: Expr)
        (target: SignValue)
        (trace: Map<Expr, SignValue>) : State<SignValue> =

        if state = BottomState then BottomState
        else
            match expr with
            | Int c ->
                let csign = signOfInt c
                if leqSign csign target then state else BottomState

            | InputInt _ ->
                state

            | Var x ->
                meetVar dom state x target

            | Minus e ->
                refineExpr state e (negSign target) trace

            | Add (e1, e2) ->
                let b1 = boundOf trace e1
                let b2 = boundOf trace e2
                let t1 = subSign target b2
                let t2 = subSign target b1
                state
                |> fun s -> refineExpr s e1 t1 trace
                |> fun s -> refineExpr s e2 t2 trace

            | Sub (e1, e2) ->
                let b1 = boundOf trace e1
                let b2 = boundOf trace e2
                let t1 = addSign target b2
                let t2 = subSign b1 target
                state
                |> fun s -> refineExpr s e1 t1 trace
                |> fun s -> refineExpr s e2 t2 trace

            | Mul (e1, e2) ->
                let b1 = boundOf trace e1
                let b2 = boundOf trace e2
                let t1 = refineMulLeft target b2
                let t2 = refineMulLeft target b1
                state
                |> fun s -> refineExpr s e1 t1 trace
                |> fun s -> refineExpr s e2 t2 trace

            | Div (_, _) ->
                state

    let refineAtomSign (state: State<SignValue>) (cond: Cond) =
        match cond with
        | Equi (e1, e2) ->
            let ev1 = evaluateExpr dom state e1
            let ev2 = evaluateExpr dom state e2
            if ev1.EvalError || ev2.EvalError then BottomState
            else
                let trace = mergeMaps ev1.steps ev2.steps
                let common = meetSign ev1.bound ev2.bound
                let s1 = refineExpr state e1 common trace
                refineExpr s1 e2 common trace

        | Diff (e1, e2) ->
            let ev1 = evaluateExpr dom state e1
            let ev2 = evaluateExpr dom state e2
            if ev1.EvalError || ev2.EvalError then BottomState
            else
                let trace = mergeMaps ev1.steps ev2.steps
                match ev1.bound, ev2.bound with
                | Zero, Zero -> BottomState
                | Zero,_ ->
                    refineExpr state e2 NonZero trace
                |_, Zero -> 
                    refineExpr state e1 NonZero trace
                | _ ->
                    match e1, e2 with
                    | Var x, Var y when x = y ->
                        BottomState
                    | Int c, Int d when c = d ->
                        BottomState
                    | _ ->
                        state

        | MinEqui (e1, e2)
        | MagEqui (e2, e1) ->
            let ev1 = evaluateExpr dom state e1
            let ev2 = evaluateExpr dom state e2
            if ev1.EvalError || ev2.EvalError then BottomState
            else
                let trace = mergeMaps ev1.steps ev2.steps

                let t1 =
                    match ev2.bound,e2 with
                    |_, Int -1 -> Neg
                    | Neg,_ | Zero,_ | NonPos,_ -> NonPos
                    | _ -> Top

                let t2 =
                    match ev1.bound,e1 with
                    |_, Int 1 -> Pos
                    | Pos,_ | Zero,_ | NonNeg,_ -> NonNeg
                    | _ -> Top

                state
                |> fun s -> refineExpr s e1 t1 trace
                |> fun s -> refineExpr s e2 t2 trace

        | Min (e1, e2)
        | Mag (e2, e1) ->
            let ev1 = evaluateExpr dom state e1
            let ev2 = evaluateExpr dom state e2
            if ev1.EvalError || ev2.EvalError then BottomState
            else
                let trace = mergeMaps ev1.steps ev2.steps

                let t1 =
                    match ev2.bound,e2 with
                    |_, Int 1 -> NonPos
                    | Neg,_ | Zero,_ | NonPos,_ -> Neg
                    | _ -> Top

                let t2 =
                    match ev1.bound,e1 with
                    |_, Int -1 -> NonNeg
                    | Pos,_ | Zero,_ | NonNeg,_ -> Pos
                    | _ -> Top

                state
                |> fun s -> refineExpr s e1 t1 trace
                |> fun s -> refineExpr s e2 t2 trace

        | _ ->
            state

    fun (state, cond) ->
        condWith (joinStates dom) refineAtomSign (state, cond)

let makeSignDomain () : Domain<SignValue> =
    let dom =
        { bottom = Bottom
          top = Top
          zero = Zero

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