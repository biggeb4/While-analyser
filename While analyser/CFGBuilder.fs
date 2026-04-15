module CFGBuilder
open Parser

type NodeId = int

type EdgeLabel =
    | Epsilon              
    | Assign of string * Expr      
    | GuardIf of Cond * bool   
    | GuardWhile of Cond * bool         
    | Assert of Cond               

type CFG =
    { Entry: NodeId
      Exit: NodeId
      Edges: Map<NodeId, (EdgeLabel * NodeId) list> 
      WhileHeaders : Set<NodeId>}

module internal Cfg =
    let empty =
        { Entry = 0; Exit = 0; Edges = Map.empty; WhileHeaders = Set.empty}

    let addEdge (fromN: NodeId) (lbl: EdgeLabel) (toN: NodeId) (g: CFG) =
        let out = g.Edges |> Map.tryFind fromN |> Option.defaultValue []
        { g with Edges = g.Edges |> Map.add fromN (out @ [ (lbl, toN) ]) }

    let merge (g1: CFG) (g2: CFG) =
        let edges =
            (g1.Edges, g2.Edges)
            ||> Map.fold (fun acc k v ->
                let cur = acc |> Map.tryFind k |> Option.defaultValue []
                acc |> Map.add k (cur @ v))

        { g1 with
            Edges = edges
            WhileHeaders = Set.union g1.WhileHeaders g2.WhileHeaders }

    let addWhileHeader (n: NodeId) (g: CFG) =
        { g with WhileHeaders = g.WhileHeaders |> Set.add n }

type Fresh() =
    let mutable nextId = 0
    member _.New() =
        let id = nextId
        nextId <- nextId + 1
        id

let buildCfg (fresh: Fresh) (stmt: Stmt) : CFG =
    let rec build (s: Stmt) : CFG =
        match s with
        | Skip ->
            let n1 = fresh.New()
            let n2 = fresh.New()
            Cfg.empty
            |> fun g -> { g with Entry = n1; Exit = n2 }
            |> Cfg.addEdge n1 Epsilon n2
        | Stmt.Assign (x, e) ->
            let n1 = fresh.New()
            let n2 = fresh.New()
            Cfg.empty
            |> fun g -> { g with Entry = n1; Exit = n2 }
            |> Cfg.addEdge n1 (Assign (x, e)) n2
        | Stmt.Assert c ->
            let n1 = fresh.New()
            let n2 = fresh.New()
            Cfg.empty
            |> fun g -> { g with Entry = n1; Exit = n2 }
            |> Cfg.addEdge n1 (Assert c) n2
        | Seq ss ->
            match ss with
            | first:: rest ->
                let gFirst = build first
                rest
                |> List.fold (fun acc st ->
                    let g2 = build st
                    let merged = Cfg.merge acc g2
                    merged
                    |> Cfg.addEdge acc.Exit Epsilon g2.Entry
                    |> fun g -> { g with Entry = acc.Entry; Exit = g2.Exit }   
                ) gFirst
        | If (c, sThen, sElse) ->
            let gThen = build sThen
            let gElse = build sElse
            let test = fresh.New()
            let join = fresh.New()
            Cfg.empty
            |> fun g -> { g with Entry = test; Exit = join }
            |> fun g -> Cfg.merge g (Cfg.merge gThen gElse)
            |> Cfg.addEdge test (GuardIf (c, true)) gThen.Entry
            |> Cfg.addEdge test (GuardIf (c, false)) gElse.Entry
            |> Cfg.addEdge gThen.Exit Epsilon join
            |> Cfg.addEdge gElse.Exit Epsilon join
        | While (c, body) ->
            let gBody = build body
            let test = fresh.New()
            let exit = fresh.New()
            Cfg.empty
            |> fun g -> { g with Entry = test; Exit = exit }
            |> fun g -> Cfg.merge g gBody
            |> Cfg.addEdge test (GuardWhile (c, true)) gBody.Entry
            |> Cfg.addEdge test (GuardWhile (c, false)) exit
            |> Cfg.addEdge gBody.Exit Epsilon test
            |> Cfg.addWhileHeader test
    build stmt

let boundToString b =
    match b with
    | PlusInf -> "+inf"
    | MinusInf -> "-inf"
    | Finite n-> sprintf ("%d") n

let rec exprToString e =
    match e with
    | Int n -> string n
    | Var x -> x
    | Add(a,b) -> sprintf "(%s + %s)" (exprToString a) (exprToString b)
    | Sub(a,b) -> sprintf "(%s - %s)" (exprToString a) (exprToString b)
    | Mul(a,b) -> sprintf "(%s * %s)" (exprToString a) (exprToString b)
    | Div(a,b) -> sprintf "(%s / %s)" (exprToString a) (exprToString b)
    | Minus a    -> sprintf "-%s" (exprToString a)
    | InputInt (min, max) -> sprintf "inputInt("+boundToString min+","+boundToString max+")"

let rec condToString c =
    match c with
    | True -> "true"
    | False -> "false"
    | Equi(a,b) -> sprintf "%s = %s" (exprToString a) (exprToString b)
    | Diff(a,b) -> sprintf "%s != %s" (exprToString a) (exprToString b)
    | Min(a,b) -> sprintf "%s < %s" (exprToString a) (exprToString b)
    | Mag(a,b) -> sprintf "%s > %s" (exprToString a) (exprToString b)
    | MinEqui(a,b) -> sprintf "%s <= %s" (exprToString a) (exprToString b)
    | MagEqui(a,b) -> sprintf "%s >= %s" (exprToString a) (exprToString b)
    | And(a,b) -> sprintf "(%s ∧ %s)" (condToString a) (condToString b)
    | Or(a,b) -> sprintf "(%s ∨ %s)" (condToString a) (condToString b)
    | Neg a -> sprintf "¬(%s)" (condToString a)

let labelToString lbl =
    match lbl with
    | Epsilon -> "ε"
    | Assign(x,e) -> sprintf "%s := %s" x (exprToString e)
    | GuardIf(c,true) -> sprintf "[%s] true" (condToString c)
    | GuardIf(c,false) -> sprintf "[%s] false" (condToString c)
    | GuardWhile(c,true) -> sprintf "[%s] true" (condToString c)
    | GuardWhile(c,false) -> sprintf "[%s] false" (condToString c)
    | Assert c -> sprintf "assert %s" (condToString c)
