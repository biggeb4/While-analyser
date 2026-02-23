module Analyser
open CFGBuilder
open Parser

type VariableBound = 
    |Interval of Bound * Bound
    |Bottom
type State = Map<string, VariableBound>

let mutable states : Map<NodeId, State> = Map.empty
let mutable maxBound = Bound.PlusInf
let mutable minBound = Bound.MinusInf

let createVarBound (lower: Bound, upper: Bound) : VariableBound =
    if upper < lower then Bottom
    else Interval (max minBound lower, min maxBound upper)

let containsZero (interval)=
    match interval with
    | Interval (lower, upper) ->
        match lower, upper with
        | Finite l, Finite u -> l <= 0 && u >= 0
        | MinusInf, _ | _, PlusInf -> true
        | PlusInf, _ | _, MinusInf -> false
    | Bottom -> false

let hasUnbounded (interval) =
    match interval with
    | Interval (lower, upper) ->
        match lower, upper with
        | Finite _, Finite _ -> false
        | _ -> true
    | Bottom -> false

let isPositive (interval) =
    match interval with
    | Interval (lower, upper) ->
        match lower, upper with
        | Finite l, Finite u -> l > 0 && u > 0
        | MinusInf, _ | _, PlusInf -> false
        | PlusInf, _ | _, MinusInf -> true
    | Bottom -> false

let isNegative (interval) =
    match interval with
    | Interval (lower, upper) ->
        match lower, upper with
        | Finite l, Finite u -> l < 0 && u < 0
        | MinusInf, _ | _, PlusInf -> false
        | PlusInf, _ | _, MinusInf -> true
    | Bottom -> false

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
            printfn "nessuno stato iniziale fornito"
            state

let rec evaluateExpr (state:State)(expr:Expr)=
    match expr with
    | Int v -> Interval (Finite v, Finite v)
    | Var v -> state |> Map.tryFind v |> Option.defaultValue Bottom
    | Add (e1,e2) ->
        let evalE1 = evaluateExpr state e1
        let evalE2 = evaluateExpr state e2
        match evalE1, evalE2 with
        | Interval (l1, u1), Interval (l2, u2) ->
            let newLower = match l1, l2 with
                            | Finite v1, Finite v2 -> Finite (v1 + v2)
                            | MinusInf, _ | _, MinusInf -> MinusInf
                            | PlusInf, _ | _, PlusInf -> PlusInf
            let newUpper = match u1, u2 with
                            | Finite v1, Finite v2 -> Finite (v1 + v2)
                            | MinusInf, _ | _, MinusInf -> MinusInf
                            | PlusInf, _ | _, PlusInf -> PlusInf
            createVarBound(newLower, newUpper)
        | Bottom, _ | _, Bottom -> Bottom
    | Sub (e1,e2) ->
        let evalE1 = evaluateExpr state e1
        let evalE2 = evaluateExpr state e2
        match evalE1, evalE2 with
        | Interval (l1, u1), Interval (l2, u2) ->
            let newLower = match l1, u2 with
                            | Finite v1, Finite v2 -> Finite (v1 - v2)
                            | MinusInf, _ | _, PlusInf -> MinusInf
                            | PlusInf, _ | _, MinusInf -> PlusInf
            let newUpper = match u1, l2 with
                            | Finite v1, Finite v2 -> Finite (v1 - v2)
                            | MinusInf, _ | _, PlusInf -> MinusInf
                            | PlusInf, _ | _, MinusInf -> PlusInf
            createVarBound(newLower, newUpper)
        | Bottom, _ | _, Bottom -> Bottom
    | Mul (e1,e2) ->
        let v1 = evaluateExpr state e1
        let v2 = evaluateExpr state e2
        match v1, v2 with
        | Bottom, _ | _, Bottom -> Bottom
        | i1, i2 ->
            if (hasUnbounded i1 && containsZero i2) || (hasUnbounded i2 && containsZero i1) then
                createVarBound (MinusInf, PlusInf)
            else
                let (Interval (l1, u1)) = i1
                let (Interval (l2, u2)) = i2
                let candidates = [ (l1,l2); (l1,u2); (u1,l2); (u1,u2) ]
                let prods =
                    candidates
                    |> List.map (fun (a,b) ->
                        match a,b with
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
                let newLower = prods |> List.min   // usa la tua comparazione Bound già definita
                let newUpper = prods |> List.max
                createVarBound (newLower, newUpper)
    | Div (e1,e2) ->
        let v1 = evaluateExpr state e1
        let v2 = evaluateExpr state e2
        match v1, v2 with
        | Bottom, _ | _, Bottom -> Bottom
        | i1, i2 ->
            if containsZero i2 then
                if i2 = Interval (Finite 0, Finite 0) then
                    Bottom
                else
            else

           
    | InputInt (lower, upper) -> createVarBound(lower, upper)

let rec analyseProgram (cfg: CFG, id: NodeId, state: State) : unit =
    let currentNode = Map.tryFind id cfg.Edges
    match currentNode with
    | Some edges ->
        match edges with
        | (lbl,nextNode) :: rest ->
            match lbl with
            | Epsilon -> analyseProgram (cfg, nextNode, state)
            | EdgeLabel.MaxBound _ -> printfn "Errore, non è consentito ridefinire il dominio lungo il programma"
            | EdgeLabel.MinBound _ -> printfn "Errore, non è consentito ridefinire il dominio lungo il programma"
            | EdgeLabel.Assign (var, expr) ->
                match expr with
                | Int v -> 
                    let newState = state |> Map.add var (Interval (Finite v, Finite v))
                    analyseProgram (cfg, nextNode, newState)
                | Var v -> 
                    let newState = state |> Map.add var (state |> Map.tryFind v |> Option.defaultValue Bottom)
                    analyseProgram (cfg, nextNode, newState)
                | Add (e1,e2) ->
                    match e1, e2 with
                    | Int v1, Int v2 -> 
                        let newState = state |> Map.add var (Interval (Finite (v1 + v2), Finite (v1 + v2)))
                        analyseProgram (cfg, nextNode, newState)
                | InputInt (lower, upper) ->
                    let newState = state |> Map.add var (createVarBound(lower, upper))
                    analyseProgram (cfg, nextNode, newState)
                | _ -> 
                    printfn "Errore Lo stato iniziale riceve solo intervalli"
                    analyseProgram (cfg, nextNode,state)
            | _ -> 
                    printfn "Errore Lo stato iniziale riceve solo Dominio e intervalli delle variabili"
                    analyseProgram (cfg, nextNode,state)
            // Analizza anche gli altri archi uscenti dallo stesso nodo
            analyseProgram (cfg, id, state) // Continua con lo stesso nodo per analizzare gli altri archi)
