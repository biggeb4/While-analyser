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
                match expr with
                | InputInt (lower, upper) ->
                    let newState = state |> Map.add var (createVarBound(lower, upper))
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


let rec analyseProgram (cfg: CFG, id: NodeId, state: State) =
    let currentNode = Map.tryFind id cfg.Edges
    match currentNode with
    | Some edges ->
        match edges with
        | [(lbl,nextNode)] ->
            match lbl with
            | Epsilon -> analyseProgram (cfg, nextNode, state)
            | EdgeLabel.MaxBound _ -> printfn "Errore, non è consentito ridefinire il dominio lungo il programma"
            | EdgeLabel.MinBound _ -> printfn "Errore, non è consentito ridefinire il dominio lungo il programma"
            | EdgeLabel.Assign (var, expr) ->
                let newState = state |> Map.add var (evaluateExpr state expr).bound
                states<-states |> Map.add id newState
                if(nextNode=cfg.Exit) then
                    ()
                else
                    analyseProgram (cfg, nextNode, newState)
            | EdgeLabel.Assert(cond)->
                let newState = assumeCond(state,cond)
                states<- states |> Map.add id newState
                if(nextNode=cfg.Exit) then
                    ()
                else
                    analyseProgram (cfg, nextNode, newState)
            | _ -> 
                    printfn "Errore Lo stato iniziale riceve solo Dominio e intervalli delle variabili"
                //analyseProgram (cfg, nextNode,state)
        // Analizza anche gli altri archi uscenti dallo stesso nodo
        //analyseProgram (cfg, id, state) // Continua con lo stesso nodo per analizzare gli altri archi)

