module Analyser
open CFGBuilder
open Parser

type VariableBound = 
    |Interval of Bound * Bound
    |Bottom
type State = Map<string, VariableBound>

let mutable states : Map<NodeId, State> = Map.empty
let mutable errors :Set<string> = Set.empty
let mutable maxBound = Bound.PlusInf
let mutable minBound = Bound.MinusInf

let negateBound b =
    match b with
    | Finite v -> Finite (-v)
    | PlusInf -> MinusInf
    | MinusInf -> PlusInf

let createVarBound (lower: Bound, upper: Bound) : VariableBound =
    let l = max minBound lower
    let u = min maxBound upper
    if u < l then Bottom
    else Interval (l,u)

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

let lub a b =
    match a, b with
    | Bottom, x | x, Bottom -> x

    | Interval(l1,u1), Interval(l2,u2) ->
        Interval(min l1 l2, max u1 u2)

let unionOpt s1 s2 =
    match s1, s2 with
    | None, None -> None
    | Some s, None
    | None, Some s -> Some s
    | Some a, Some b -> Some (Set.union a b)

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
type EvalRes =
  { bound: VariableBound
    vars: Set<string>
    steps: Map<Expr, VariableBound> }

let mergeMaps m1 m2 =
    Map.fold (fun acc k v -> Map.add k v acc) m1 m2

let rec evaluateExpr (state:State)(expr:Expr)=
    let inline mk v vars steps = { bound=v; vars=vars; steps=steps }
    match expr with
    | Int v -> mk (Interval(Finite v, Finite v)) Set.empty (Map.empty |> Map.add expr (Interval(Finite v, Finite v)))
    | Var v -> 
        let res = state |> Map.tryFind v |> Option.defaultValue Bottom
        mk res (Set.singleton v) (Map.empty |> Map.add expr res)

    | InputInt (lower, upper) -> 
        let res=createVarBound(lower, upper)
        mk res Set.empty (Map.empty |> Map.add expr res)
    | Minus e ->
        let r = evaluateExpr state e
        match r.bound with
        | Bottom ->
            mk Bottom r.vars (r.steps|> Map.add expr Bottom)
        | Interval(l,u) ->
            let res = Interval(negateBound u, negateBound l)
            mk res r.vars (r.steps|> Map.add expr res)
    | Add (e1,e2) ->
        let r1 = evaluateExpr state e1
        let r2 = evaluateExpr state e2
        match r1.bound, r2.bound with
        | Interval(l1,u1), Interval(l2,u2) ->
            let newLower =
                match l1, l2 with
                | MinusInf, _ | _, MinusInf -> MinusInf
                | PlusInf, _ | _, PlusInf -> PlusInf
                | Finite a, Finite b -> Finite (a + b)

            let newUpper =
                match u1, u2 with
                | PlusInf, _ | _, PlusInf -> PlusInf
                | MinusInf, _ | _, MinusInf -> MinusInf
                | Finite a, Finite b -> Finite (a + b)

            let res = createVarBound(newLower, newUpper)
            mk res (Set.union r1.vars r2.vars) (mergeMaps r1.steps r2.steps |> Map.add expr res )
        | Bottom, _ | _, Bottom ->
            mk Bottom (Set.union r1.vars r2.vars) (mergeMaps r1.steps r2.steps |> Map.add expr Bottom )
    | Sub (e1,e2) ->
        let r1 = evaluateExpr state e1
        let r2 = evaluateExpr state e2
        match r1.bound, r2.bound with
        | Bottom, _ | _, Bottom ->
            mk Bottom (Set.union r1.vars r2.vars) (mergeMaps r1.steps r2.steps |> Map.add expr Bottom )
        | Interval(l1,u1), Interval(l2,u2) ->
            let newLower =
                match l1, u2 with
                | MinusInf, _ | _, PlusInf -> MinusInf
                | PlusInf, _ | _, MinusInf -> PlusInf
                | Finite a, Finite b -> Finite (a - b)

            let newUpper =
                match u1, l2 with
                | PlusInf, _ | _, MinusInf -> PlusInf
                | MinusInf, _ | _, PlusInf -> MinusInf
                | Finite a, Finite b -> Finite (a - b)

            let res = createVarBound(newLower, newUpper)
            mk res (Set.union r1.vars r2.vars) (mergeMaps r1.steps r2.steps |> Map.add expr res )
    | Mul (e1,e2) ->
        let r1 = evaluateExpr state e1
        let r2 = evaluateExpr state e2
        match r1.bound, r2.bound with
        | Bottom, _ | _, Bottom ->
            mk Bottom (Set.union r1.vars r2.vars) (mergeMaps r1.steps r2.steps |> Map.add expr Bottom )

        | i1, i2 ->
            // se unbounded * contiene 0 -> Top (nel tuo dominio: [-inf,+inf] clippato)
            if (hasUnbounded i1 && containsZero i2) || (hasUnbounded i2 && containsZero i1) then
                let res = createVarBound(MinusInf, PlusInf)
                mk res (Set.union r1.vars r2.vars) (mergeMaps r1.steps r2.steps |> Map.add expr res )
            else
                let (Interval(l1,u1)) = i1
                let (Interval(l2,u2)) = i2
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

                let res = createVarBound(List.min prods, List.max prods)
                mk res (Set.union r1.vars r2.vars) (mergeMaps r1.steps r2.steps |> Map.add expr res )
    | Div (e1,e2) ->
        let r1 = evaluateExpr state e1
        let r2 = evaluateExpr state e2
        match r1.bound, r2.bound with
        | Bottom, _ | _, Bottom ->
            mk Bottom (Set.union r1.vars r2.vars) (mergeMaps r1.steps r2.steps |> Map.add expr Bottom )

        | Interval(l1,u1), Interval(l2,u2) ->

            let divNoZero (dl,du) : VariableBound =
                let candidates = [ (l1,dl); (l1,du); (u1,dl); (u1,du) ]

                let vals =
                    candidates
                    |> List.choose (fun (a,b) ->
                        match a,b with
                        | Finite x, Finite y -> Some (Finite (x / y)) // y != 0

                        | PlusInf, Finite k ->
                            if k > 0 then Some PlusInf
                            elif k < 0 then Some MinusInf
                            else None

                        | MinusInf, Finite k ->
                            if k > 0 then Some MinusInf
                            elif k < 0 then Some PlusInf
                            else None

                        | Finite _, PlusInf
                        | Finite _, MinusInf ->
                            Some (Finite 0)

                        // ∞ / ∞ indeterminato: scarta
                        | PlusInf, PlusInf
                        | MinusInf, MinusInf
                        | PlusInf, MinusInf
                        | MinusInf, PlusInf ->
                            None
                    )

                if List.isEmpty vals then
                    createVarBound(MinusInf, PlusInf)
                else
                    createVarBound(List.min vals, List.max vals)

            let res =
                if l2 = Finite 0 && u2 = Finite 0 then
                    errors <- errors |> Set.add "divisione per zero"
                    Bottom
                elif containsZero r2.bound then
                    errors <- errors |> Set.add "potrebbe dividere per zero"
                    let parts =
                        [ if l2 < Finite 0 then yield (l2, Finite -1)
                          if u2 > Finite 0 then yield (Finite 1, u2) ]

                    parts
                    |> List.map divNoZero
                    |> List.reduce lub
                else
                    divNoZero (l2,u2)

            mk res (Set.union r1.vars r2.vars) (mergeMaps r1.steps r2.steps |> Map.add expr res )


let rec assumeCond(state:State,cond:Cond):unit =
    match cond with
    | Equi(e1,e2) ->
        let evalE1 = evaluateExpr state e1
        let evalE2 = evaluateExpr state e2

let rec analyseProgram (cfg: CFG, id: NodeId, state: State) : unit =
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

            | _ -> 
                    printfn "Errore Lo stato iniziale riceve solo Dominio e intervalli delle variabili"
                //analyseProgram (cfg, nextNode,state)
        // Analizza anche gli altri archi uscenti dallo stesso nodo
        //analyseProgram (cfg, id, state) // Continua con lo stesso nodo per analizzare gli altri archi)
