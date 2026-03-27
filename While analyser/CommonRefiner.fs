module RefinerCommon

open Parser
open Eval

// ===================================
// Utility comuni sugli stati
// ===================================

let lookupVar (dom: Domain<'A>) (state: State<'A>) (x: string) : 'A =
    match state with
    | BottomState -> dom.bottom
    | Vars m -> m |> Map.tryFind x |> Option.defaultValue dom.top

let updateVar (state: State<'A>) (x: string) (value: 'A) : State<'A> =
    match state with
    | BottomState -> BottomState
    | Vars m -> Vars (m |> Map.add x value)

let refineVarMeet (dom: Domain<'A>) (state: State<'A>) (x: string) (value: 'A) : State<'A> =
    match state with
    | BottomState -> BottomState
    | Vars m ->
        let oldValue = m |> Map.tryFind x |> Option.defaultValue dom.top
        let newValue = dom.meet oldValue value
        if dom.leq newValue dom.bottom then
            BottomState
        else
            Vars (m |> Map.add x newValue)

let stateBottom<'A> : State<'A> = BottomState

let stateIsBottom (state: State<'A>) =
    match state with
    | BottomState -> true
    | _ -> false

let private allKeys (m1: Map<string,'A>) (m2: Map<string,'A>) =
    Seq.append (m1 |> Map.toSeq |> Seq.map fst) (m2 |> Map.toSeq |> Seq.map fst)
    |> Set.ofSeq

let joinStates (dom: Domain<'A>) (s1: State<'A>) (s2: State<'A>) : State<'A> =
    match s1, s2 with
    | BottomState, s
    | s, BottomState -> s
    | Vars m1, Vars m2 ->
        let merged =
            allKeys m1 m2
            |> Seq.fold (fun acc k ->
                let v1 = m1 |> Map.tryFind k |> Option.defaultValue dom.bottom
                let v2 = m2 |> Map.tryFind k |> Option.defaultValue dom.bottom
                acc |> Map.add k (dom.join v1 v2)
            ) Map.empty
        Vars merged

let meetStates (dom: Domain<'A>) (s1: State<'A>) (s2: State<'A>) : State<'A> =
    match s1, s2 with
    | BottomState, _
    | _, BottomState -> BottomState
    | Vars m1, Vars m2 ->
        let merged =
            allKeys m1 m2
            |> Seq.fold (fun acc k ->
                let v1 = m1 |> Map.tryFind k |> Option.defaultValue dom.top
                let v2 = m2 |> Map.tryFind k |> Option.defaultValue dom.top
                acc |> Map.add k (dom.meet v1 v2)
            ) Map.empty

        if merged |> Map.exists (fun _ v -> dom.leq v dom.bottom) then
            BottomState
        else
            Vars merged

// ===================================
// Utility comuni sulle condizioni
// ===================================

let rec negateCond cond =
    match cond with
    | True -> False
    | False -> True
    | Neg c -> c
    | And (c1, c2) -> Or (negateCond c1, negateCond c2)
    | Or (c1, c2) -> And (negateCond c1, negateCond c2)
    | Equi (e1, e2) -> Diff (e1, e2)
    | Diff (e1, e2) -> Equi (e1, e2)
    | Min (e1, e2) -> MagEqui (e1, e2)
    | Mag (e1, e2) -> MinEqui (e1, e2)
    | MinEqui (e1, e2) -> Mag (e1, e2)
    | MagEqui (e1, e2) -> Min (e1, e2)

// ===================================
// Scheletro comune per assume/refine
// ===================================

let rec condWith
    (joinState: State<'A> -> State<'A> -> State<'A>)
    (condAtom: State<'A> -> Cond -> State<'A>)
    (state: State<'A>, cond: Cond) : State<'A> =

    match state, cond with
    | BottomState, _ -> BottomState

    | _, True -> state
    | _, False -> BottomState

    | _, Neg c ->
        condWith joinState condAtom (state, negateCond c)

    | _, And (c1, c2) ->
        let s1 = condWith joinState condAtom (state, c1)
        condWith joinState condAtom (s1, c2)

    | _, Or (c1, c2) ->
        let s1 = condWith joinState condAtom (state, c1)
        let s2 = condWith joinState condAtom (state, c2)
        joinState s1 s2

    | _, (Equi _ | Diff _ | Min _ | Mag _ | MinEqui _ | MagEqui _) ->
        condAtom state cond