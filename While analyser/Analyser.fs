module Analyser
open CFGBuilder
open Parser

type VariableBound = Bound * Bound
type State = Map<string, VariableBound>

let mutable states : Map<NodeId, State> = Map.empty
let mutable maxBound = Bound.PlusInf
let mutable minBound = Bound.MinusInf

let rec analyseStartingState (cfg: CFG,id:NodeId,state:State) : State =
    let currentNode = Map.tryFind id cfg.Edges
    match currentNode with
    | Some edges ->
        match edges with
        | (lbl, nextNode) :: _ ->
            match lbl with
            | Epsilon -> analyseStartingState (cfg, nextNode,state)
            | EdgeLabel.MaxBound b ->
                maxBound <- b
                analyseStartingState (cfg, nextNode,state)
            | EdgeLabel.MinBound b ->
                minBound <- b
                analyseStartingState (cfg, nextNode,state)
            | EdgeLabel.Assign (var, expr) ->
                match expr with
                | InputInt (lower, upper) ->
                    let newState = state |> Map.add var (lower, upper)
                    analyseStartingState (cfg, nextNode,newState)
                | _ -> 
                    printfn "Errore Lo stato iniziale riceve solo intervalli"
                    state
            | _ -> 
                    printfn "Errore Lo stato iniziale riceve solo Dominio e intervalli delle variabili"
                    state
        | _ -> 
            printfn "Errore, nella prima riga sono solo consentite assegnazioni per lo stato iniziale"
            state
    | None -> state
                
