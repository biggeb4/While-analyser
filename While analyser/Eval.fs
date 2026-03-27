module Eval

open CFGBuilder
open Parser

type State<'A> =
    | Vars of Map<string, 'A>
    | BottomState

type EvalRes<'A> =
  { bound: 'A
    vars: Set<string>
    steps: Map<Expr, 'A> }

type Domain<'A> =
  { 
    bottom : 'A
    top : 'A

    leq : 'A -> 'A -> bool
    join : 'A -> 'A -> 'A
    meet : 'A -> 'A -> 'A
    widen : 'A -> 'A -> 'A
    narrow : 'A -> 'A -> 'A

    neg : 'A -> 'A
    add : 'A -> 'A -> 'A
    sub : 'A -> 'A -> 'A
    mul : 'A -> 'A -> 'A
    div : 'A -> 'A -> 'A

    constInt : int -> 'A
    inputInt : Bound * Bound -> 'A 
    assume : (State<'A> * Cond -> State<'A>)
    refine : ((State<'A> * Cond) -> State<'A>) option 
  }

let mutable warnings : Set<string> = Set.empty

let mergeMaps m1 m2 =
    Map.fold (fun acc k v -> Map.add k v acc) m1 m2

let rec evaluateExpr (dom:Domain<'A>) (state:State<'A>) (expr:Expr) : EvalRes<'A> =
    let inline mk v vars steps = { bound = v; vars = vars; steps = steps }

    match expr with
    | Int v ->
        let res = dom.constInt v
        mk res Set.empty (Map.empty |> Map.add expr res)

    | Var v ->
        match state with
        | BottomState ->
            mk dom.bottom Set.empty (Map.empty |> Map.add expr dom.bottom)
        | Vars s ->
            let res = s |> Map.tryFind v |> Option.defaultValue dom.top
            mk res (Set.singleton v) (Map.empty |> Map.add expr res)

    | InputInt (lower, upper) ->
        let res = dom.inputInt (lower, upper)
        mk res Set.empty (Map.empty |> Map.add expr res)

    | Minus e ->
        let r = evaluateExpr dom state e
        let res = dom.neg r.bound
        mk res r.vars (r.steps |> Map.add expr res)

    | Add (e1,e2) ->
        let r1 = evaluateExpr dom state e1
        let r2 = evaluateExpr dom state e2
        let res = dom.add r1.bound r2.bound
        mk res (Set.union r1.vars r2.vars) (mergeMaps r1.steps r2.steps |> Map.add expr res)

    | Sub (e1,e2) ->
        let r1 = evaluateExpr dom state e1
        let r2 = evaluateExpr dom state e2
        let res = dom.sub r1.bound r2.bound
        mk res (Set.union r1.vars r2.vars) (mergeMaps r1.steps r2.steps |> Map.add expr res)

    | Mul (e1,e2) ->
        let r1 = evaluateExpr dom state e1
        let r2 = evaluateExpr dom state e2
        let res = dom.mul r1.bound r2.bound
        mk res (Set.union r1.vars r2.vars) (mergeMaps r1.steps r2.steps |> Map.add expr res)

    | Div (e1,e2) ->
        let r1 = evaluateExpr dom state e1
        let r2 = evaluateExpr dom state e2
        let res = dom.div r1.bound r2.bound
        mk res (Set.union r1.vars r2.vars) (mergeMaps r1.steps r2.steps |> Map.add expr res)