module Analyser

open CFGBuilder
open Parser
open Eval

type AnalysisConfig =
    { useWidening : bool
      widenAfter : int
      useNarrowing : bool
      narrowingSteps : int }

let leqState (dom: Domain<'A>) s1 s2 =
    match s1, s2 with
    | BottomState, _ -> true
    | _, BottomState -> false
    | Vars m1, Vars m2 ->
        let keys =
            Seq.append (Map.keys m1) (Map.keys m2)
            |> Set.ofSeq

        keys
        |> Set.forall (fun k ->
            let v1 = m1 |> Map.tryFind k |> Option.defaultValue dom.top
            let v2 = m2 |> Map.tryFind k |> Option.defaultValue dom.top
            dom.leq v1 v2)

let joinStates (dom: Domain<'A>) s1 s2 =
    match s1, s2 with
    | BottomState, s
    | s, BottomState -> s
    | Vars m1, Vars m2 ->
        let keys =
            Seq.append (Map.keys m1) (Map.keys m2)
            |> Set.ofSeq

        let merged =
            keys
            |> Seq.fold (fun acc k ->
                let v1 = m1 |> Map.tryFind k |> Option.defaultValue dom.top
                let v2 = m2 |> Map.tryFind k |> Option.defaultValue dom.top
                acc |> Map.add k (dom.join v1 v2)
            ) Map.empty

        Vars merged

let widenState (dom: Domain<'A>) s1 s2 =
    match s1, s2 with
    | BottomState, s
    | s, BottomState -> s
    | Vars m1, Vars m2 ->
        let keys =
            Seq.append (Map.keys m1) (Map.keys m2)
            |> Set.ofSeq

        let merged =
            keys
            |> Seq.fold (fun acc k ->
                let v1 = m1 |> Map.tryFind k |> Option.defaultValue dom.top
                let v2 = m2 |> Map.tryFind k |> Option.defaultValue dom.top
                acc |> Map.add k (dom.widen v1 v2)
            ) Map.empty

        Vars merged

let narrowState (dom: Domain<'A>) s1 s2 =
    match s1, s2 with
    | BottomState, _ -> BottomState
    | _, BottomState -> BottomState
    | Vars m1, Vars m2 ->
        let keys =
            Seq.append (Map.keys m1) (Map.keys m2)
            |> Set.ofSeq

        let merged =
            keys
            |> Seq.fold (fun acc k ->
                let v1 = m1 |> Map.tryFind k |> Option.defaultValue dom.top
                let v2 = m2 |> Map.tryFind k |> Option.defaultValue dom.top
                acc |> Map.add k (dom.narrow v1 v2)
            ) Map.empty

        Vars merged

let transfer (dom: Domain<'A>) lbl sIn =
    match sIn with
    | BottomState -> BottomState
    | Vars vars ->
        match lbl with
        | Epsilon -> sIn

        | EdgeLabel.Assign (x, e) ->
            let res = evaluateExpr dom sIn e
            if not res.EvalError then
                Vars (vars |> Map.add x res.bound)
            else
                BottomState

        | EdgeLabel.Assert c ->
            dom.AssumeAndRefine (sIn, c)

        | GuardIf (c, takeTrue) ->
            let cc = if takeTrue then c else Neg c
            dom.AssumeAndRefine (sIn, cc)

        | GuardWhile (c, takeTrue) ->
            let cc = if takeTrue then c else Neg c
            dom.AssumeAndRefine (sIn, cc)

        | _ -> sIn

let runWideningPhase dom cfg entryState config =
    let updateCount = System.Collections.Generic.Dictionary<NodeId, int>()

    let mutable inState = Map.empty |> Map.add cfg.Entry entryState

    let q = System.Collections.Generic.Queue<NodeId>()
    let inQueue = System.Collections.Generic.HashSet<NodeId>()

    q.Enqueue cfg.Entry
    inQueue.Add cfg.Entry |> ignore

    while q.Count > 0 do
        let n = q.Dequeue()
        inQueue.Remove n |> ignore

        let sN =
            inState |> Map.tryFind n |> Option.defaultValue BottomState

        match Map.tryFind n cfg.Edges with
        | None -> ()
        | Some outs ->
            for (lbl, succ) in outs do
                let sOut = transfer dom lbl sN
                let oldSucc = inState |> Map.tryFind succ |> Option.defaultValue BottomState

                let count =
                    match updateCount.TryGetValue succ with
                    | true, c -> c
                    | false, _ -> 0

                let combined =
                    if config.useWidening
                       && Set.contains succ cfg.WhileHeaders
                       && count >= config.widenAfter then
                        widenState dom oldSucc sOut
                    else
                        joinStates dom oldSucc sOut

                let changed = not (leqState dom combined oldSucc)

                if changed then
                    updateCount.[succ] <- count + 1
                    inState <- inState |> Map.add succ combined
                    if inQueue.Add succ then
                        q.Enqueue succ

    inState

let private collectRhs dom cfg entryState currentState =
    let mutable rhs = Map.empty |> Map.add cfg.Entry entryState

    for KeyValue(n, outs) in cfg.Edges do
        let sN = 
            if n = cfg.Entry then entryState
            else currentState |> Map.tryFind n |> Option.defaultValue BottomState

        match sN with
        | BottomState -> ()
        | _ ->
            for (lbl, succ) in outs do
                let sOut = transfer dom lbl sN
                let old =
                    rhs |> Map.tryFind succ |> Option.defaultValue BottomState
                rhs <- rhs |> Map.add succ (joinStates dom old sOut)

    rhs

let runNarrowingPhase dom cfg entryState baseState steps =
    let mutable st = baseState

    for _ in 1 .. steps do
        let rhs = collectRhs dom cfg entryState st

        let keys =
            Seq.append (Map.keys st) (Map.keys rhs)
            |> Set.ofSeq
            |> Set.add cfg.Entry

        let next =
            keys
            |> Seq.fold (fun acc n ->
                if n = cfg.Entry then
                    acc |> Map.add n entryState
                else
                    let oldState =
                        st |> Map.tryFind n |> Option.defaultValue BottomState
                    let rhsState =
                        rhs |> Map.tryFind n |> Option.defaultValue BottomState
                    let refined = narrowState dom oldState rhsState
                    acc |> Map.add n refined
            ) Map.empty

        st <- next

    st

let analyseFixpoint
    (dom: Domain<'A>)
    (cfg: CFG)
    (entryState: State<'A>)
    (config: AnalysisConfig)
    : Map<NodeId, State<'A>> =

    let widened = runWideningPhase dom cfg entryState config

    if config.useNarrowing && config.narrowingSteps > 0 then
        runNarrowingPhase dom cfg entryState widened config.narrowingSteps
    else
        widened