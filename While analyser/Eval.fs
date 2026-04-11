module Eval

open Parser

type State<'A> =
    | Vars of Map<string, 'A>
    | BottomState

type WarningTypes =
    | DivisionByZero
    | MayDivideByZero

type Warning = 
    {   
    name: WarningTypes
    critical: bool
    }

type EvalRes<'A> =
  { bound: 'A
    vars: Set<string>
    steps: Map<Expr, 'A>
    EvalError:bool}

type Domain<'A> =
  { 
    bottom : 'A
    top : 'A
    zero : 'A

    leq : 'A -> 'A -> bool
    join : 'A -> 'A -> 'A
    meet : 'A -> 'A -> 'A
    widen : 'A -> 'A -> 'A
    narrow : 'A -> 'A -> 'A

    neg : 'A -> 'A
    add : 'A -> 'A -> 'A
    sub : 'A -> 'A -> 'A
    mul : 'A -> 'A -> 'A
    div : 'A -> 'A -> 'A * Option<Warning>

    constInt : int -> 'A
    inputInt : Bound * Bound -> 'A 
    AssumeAndRefine : ((State<'A> * Cond) -> State<'A>) 
  }

let mutable warnings : Set<Warning*Expr> = Set.empty

let mergeMaps m1 m2 =
    Map.fold (fun acc k v -> Map.add k v acc) m1 m2

let rec evaluateExpr (dom:Domain<'A>) (state:State<'A>) (expr:Expr) : EvalRes<'A> =
    let inline mk v vars steps err = { bound = v; vars = vars; steps = steps; EvalError=err}

    match expr with
    | Int v ->
        let res = dom.constInt v
        mk res Set.empty (Map.empty |> Map.add expr res) false

    | Var v ->
        match state with
        | BottomState ->
            mk dom.bottom Set.empty (Map.empty |> Map.add expr dom.bottom) false
        | Vars s ->
            let res = s |> Map.tryFind v |> Option.defaultValue dom.top
            mk res (Set.singleton v) (Map.empty |> Map.add expr res) false

    | InputInt (lower, upper) ->
        let res = dom.inputInt (lower, upper)
        mk res Set.empty (Map.empty |> Map.add expr res) false

    | Minus e ->
        let r = evaluateExpr dom state e
        let res = dom.neg r.bound
        mk res r.vars (r.steps |> Map.add expr res) r.EvalError

    | Add (e1,e2) ->
        let r1 = evaluateExpr dom state e1
        let r2 = evaluateExpr dom state e2
        let err = r1.EvalError || r2.EvalError
        match e1,e2 with
            |Var (x),Minus(Var (y)) | Minus(Var (x)),Var (y) when x=y ->
                let res=dom.zero
                mk res (Set.singleton x) (mergeMaps r1.steps r2.steps |> Map.add expr res) err
            | _->
                let res = dom.add r1.bound r2.bound
                mk res (Set.union r1.vars r2.vars) (mergeMaps r1.steps r2.steps |> Map.add expr res) err

    | Sub (e1,e2) ->
        let r1 = evaluateExpr dom state e1
        let r2 = evaluateExpr dom state e2
        let err = r1.EvalError || r2.EvalError
        match e1,e2 with
            |Var (x),Var (y) when x=y ->
                let res=dom.zero
                mk res (Set.singleton x) (mergeMaps r1.steps r2.steps |> Map.add expr res) err
            | _->
                let res = dom.sub r1.bound r2.bound
                mk res (Set.union r1.vars r2.vars) (mergeMaps r1.steps r2.steps |> Map.add expr res) err

    | Mul (e1,e2) ->
        let r1 = evaluateExpr dom state e1
        let r2 = evaluateExpr dom state e2
        let err = r1.EvalError || r2.EvalError
        let res = dom.mul r1.bound r2.bound
        mk res (Set.union r1.vars r2.vars) (mergeMaps r1.steps r2.steps |> Map.add expr res) err

    | Div (e1,e2) ->
        let r1 = evaluateExpr dom state e1
        let r2 = evaluateExpr dom state e2
        let res = dom.div r1.bound r2.bound
        match res with
            | res, Some w ->
                warnings <- warnings |> Set.add (w,expr)
                mk res (Set.union r1.vars r2.vars) (mergeMaps r1.steps r2.steps |> Map.add expr res) (r1.EvalError || r2.EvalError || w.critical)
            | res, None ->
                mk res (Set.union r1.vars r2.vars) (mergeMaps r1.steps r2.steps |> Map.add expr res) (r1.EvalError || r2.EvalError)