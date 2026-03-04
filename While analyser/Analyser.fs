module Analyser
open CFGBuilder
open Parser
open Eval
open Refine

let rec analyseStartingState (cfg: CFG,id:NodeId,state:State) : State =
    let currentNode = Map.tryFind id cfg.Edges
    match currentNode with
    | Some edges ->
        match edges with
        | [(lbl, nextNode)] ->
            match lbl with
            | Epsilon -> analyseStartingState (cfg, nextNode,state)
            | EdgeLabel.MaxBound b ->
                maxBound <- b
                if maxBound < minBound then
                    printfn "Errore, il massimo è minore del minimo"
                analyseStartingState (cfg, nextNode,state)
            | EdgeLabel.MinBound b ->
                minBound <- b
                if maxBound < minBound then
                    printfn "Errore, il massimo è minore del minimo"
                analyseStartingState (cfg, nextNode,state)
            | EdgeLabel.Assign (var, expr) ->
                match expr,state with
                | _ , BottomState -> 
                    printfn "Bottom state iniziale"
                    state
                | InputInt (lower, upper),Vars vars ->
                    let newState = Vars (vars |> Map.add var (createVarBound(lower, upper)))
                    analyseStartingState (cfg, nextNode,newState)
                | _ -> 
                    printfn "Errore Lo stato iniziale riceve solo intervalli"
                    state
            | _ -> 
                    printfn "Errore Lo stato iniziale riceve solo Dominio e intervalli delle variabili"
                    state
        | [] -> 
            printfn "Errore, nodo senza archi nello stato iniziale"
            state
        | _ ->
            printfn "Errore: branching nello stato iniziale (atteso 1 arco uscente)"
            state
    | None -> 
            state

let leqBound a b =
    match a,b with
    | Bottom, _ -> true
    | _, Bottom -> false
    | Interval(l1,u1), Interval(l2,u2) -> l2 <= l1 && u1 <= u2

let leqState s1 s2 =
    match s1,s2 with
    | BottomState, _ -> true
    | _, BottomState -> false
    | Vars m1, Vars m2 ->
        m1
        |> Map.forall (fun k v1 ->
            let v2 = m2 |> Map.tryFind k |> Option.defaultValue Bottom
            leqBound v1 v2)

let lubState s1 s2 =
    match s1,s2 with
    | BottomState, s
    | s, BottomState -> s
    | Vars m1, Vars m2 ->
        let keys =
            Seq.append (m1 |> Map.toSeq |> Seq.map fst) (m2 |> Map.toSeq |> Seq.map fst)
            |> Set.ofSeq
        let merged =
            keys
            |> Seq.fold (fun acc k ->
                let v1 = m1 |> Map.tryFind k |> Option.defaultValue Bottom
                let v2 = m2 |> Map.tryFind k |> Option.defaultValue Bottom
                acc |> Map.add k (lub v1 v2)
            ) Map.empty
        Vars merged

let transfer (lbl:EdgeLabel) (sIn:State) : State =
    match sIn with
    | BottomState -> BottomState
    | Vars vars ->
        match lbl with
        | Epsilon -> sIn

        | EdgeLabel.Assign (x, e) ->
            let b = (evaluateExpr sIn e).bound
            Vars (vars |> Map.add x b)

        | EdgeLabel.Assert c ->
            assumeCond (sIn, c)

        | Guard (c, takeTrue) ->
            if takeTrue then assumeCond (sIn, c)
            else assumeCond (sIn, Neg c)   // Neg = ¬c nel tuo AST

        // queste di solito stanno solo nella prima riga; se capitano nel mezzo le ignori
        | EdgeLabel.MaxBound _ -> sIn
        | EdgeLabel.MinBound _ -> sIn

let analyseFixpoint (cfg:CFG) (entryState:State) : Map<NodeId, State> =
    let mutable inState : Map<NodeId, State> =
        Map.empty |> Map.add cfg.Entry entryState

    let q = System.Collections.Generic.Queue<NodeId>()
    let inQueue = System.Collections.Generic.HashSet<NodeId>()
    q.Enqueue cfg.Entry
    inQueue.Add cfg.Entry |> ignore

    while q.Count > 0 do
        let n = q.Dequeue()
        inQueue.Remove n |> ignore

        let sN = inState |> Map.tryFind n |> Option.defaultValue BottomState

        match Map.tryFind n cfg.Edges with
        | None -> ()
        | Some outs ->
            for (lbl, succ) in outs do
                let sOut = transfer lbl sN

                let oldSucc = inState |> Map.tryFind succ |> Option.defaultValue BottomState
                let joined = lubState oldSucc sOut

                if not (leqState joined oldSucc) then
                    inState <- inState |> Map.add succ joined
                    if inQueue.Add succ then q.Enqueue succ

    inState