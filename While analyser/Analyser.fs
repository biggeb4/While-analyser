module Analyser

open CFGBuilder
open Parser
open Eval

type AnalysisConfig =
    { useWidening : bool
      widenAfter : int
      useNarrowing : bool
      narrowingSteps : int }

let leqState (dom:Domain<'A>) s1 s2 =
    match s1, s2 with
    | BottomState, _ -> true
    | _, BottomState -> false
    | Vars m1, Vars m2 ->
        m1
        |> Map.forall (fun k v1 ->
            let v2 = m2 |> Map.tryFind k |> Option.defaultValue dom.bottom
            dom.leq v1 v2)

let lubState (dom:Domain<'A>) s1 s2 =
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
                let v1 = m1 |> Map.tryFind k |> Option.defaultValue dom.bottom
                let v2 = m2 |> Map.tryFind k |> Option.defaultValue dom.bottom
                acc |> Map.add k (dom.join v1 v2)
            ) Map.empty

        Vars merged

let widenState (dom:Domain<'A>) s1 s2 =
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
                let v1 = m1 |> Map.tryFind k |> Option.defaultValue dom.bottom
                let v2 = m2 |> Map.tryFind k |> Option.defaultValue dom.bottom
                acc |> Map.add k (dom.widen v1 v2)
            ) Map.empty

        Vars merged

let narrowState (dom:Domain<'A>) s1 s2 =
    match s1, s2 with
    | BottomState, _
    | _, BottomState -> BottomState
    | Vars m1, Vars m2 ->
        let keys =
            Seq.append (Map.keys m1) (Map.keys m2)
            |> Set.ofSeq

        let merged =
            keys
            |> Seq.fold (fun acc k ->
                let v1 = m1 |> Map.tryFind k |> Option.defaultValue dom.bottom
                let v2 = m2 |> Map.tryFind k |> Option.defaultValue dom.bottom
                acc |> Map.add k (dom.narrow v1 v2)
            ) Map.empty

        Vars merged

let transfer (dom:Domain<'A>) lbl sIn =
    match sIn with
    | BottomState -> BottomState
    | Vars vars ->
        match lbl with
        | Epsilon -> sIn

        | EdgeLabel.Assign (x, e) ->
            let b = (evaluateExpr dom sIn e).bound
            Vars (vars |> Map.add x b)

        | EdgeLabel.Assert c ->
            let s1 = dom.assume (sIn, c)
            match dom.refine with
            | Some refine -> refine (s1, c)
            | None -> s1

        | GuardIf (c, takeTrue) ->
            let cc = if takeTrue then c else Neg c
            let s1 = dom.assume (sIn, cc)
            match dom.refine with
            | Some refine -> refine (s1, cc)
            | None -> s1

        | GuardWhile (c, takeTrue) ->
            let cc = if takeTrue then c else Neg c
            let s1 = dom.assume (sIn, cc)
            match dom.refine with
            | Some refine -> refine (s1, cc)
            | None -> s1

        | _ -> sIn

let private runFixpointPhase dom cfg entryState combine initialState =
    let mutable inState = initialState

    let q = System.Collections.Generic.Queue<NodeId>()
    let inQueue = System.Collections.Generic.HashSet<NodeId>()

    q.Enqueue cfg.Entry
    inQueue.Add cfg.Entry |> ignore

    while q.Count > 0 do
        let n = q.Dequeue()
        inQueue.Remove n |> ignore

        let sN =
            if n = cfg.Entry then entryState
            else inState |> Map.tryFind n |> Option.defaultValue BottomState

        match Map.tryFind n cfg.Edges with
        | None -> ()
        | Some outs ->
            for (lbl, succ) in outs do
                let sOut = transfer dom lbl sN
                let oldSucc = inState |> Map.tryFind succ |> Option.defaultValue BottomState
                let combined = combine succ oldSucc sOut

                if not (leqState dom combined oldSucc) then
                    inState <- inState |> Map.add succ combined
                    if inQueue.Add succ then q.Enqueue succ

    inState

let runWideningPhase dom cfg entryState config =
    let updateCount = System.Collections.Generic.Dictionary<NodeId,int>()

    let combine succ oldSucc sOut =
        let count =
            match updateCount.TryGetValue succ with
            | true, c -> c
            | false, _ -> 0

        let res =
            if config.useWidening
               && Set.contains succ cfg.WhileHeaders
               && count >= config.widenAfter then
                widenState dom oldSucc sOut
            else
                lubState dom oldSucc sOut

        if not (leqState dom res oldSucc) then
            updateCount.[succ] <- count + 1

        res
    runFixpointPhase dom cfg entryState combine (Map.empty |> Map.add cfg.Entry entryState)

let runNarrowingPhase dom cfg entryState baseState steps =
    let combine succ oldSucc sOut =
        if Set.contains succ cfg.WhileHeaders then
            narrowState dom oldSucc sOut
        else
            lubState dom oldSucc sOut

    let mutable st = baseState
    for _ in 1 .. steps do
        st <- runFixpointPhase dom cfg entryState combine st
    st

let analyseFixpoint
    (dom:Domain<'A>)
    (cfg:CFG)
    (entryState:State<'A>)
    (config:AnalysisConfig)
    : Map<NodeId, State<'A>> =
    
    let domNoRefine = { dom with refine = None }
    let widened = runWideningPhase domNoRefine cfg entryState config

    if config.useNarrowing && config.narrowingSteps > 0 then
        runNarrowingPhase dom cfg entryState widened config.narrowingSteps
    else
        widened