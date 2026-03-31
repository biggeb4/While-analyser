open System
open System.IO

open Parser
open CFGBuilder
open Analyser
open Eval
open IntervalDomain
open ConstantPropagationDomain
open SignDomain
open CongruenceDomain

type ImplementedDomain =
    | Intervals
    | ConstantPropagation
    | Sign
    | Congruence

type PreparedAnalysis<'A> =
    { Name : string
      Info : string
      Domain : Domain<'A>
      InitialState : State<'A>
      Config : AnalysisConfig }

type PreparedRun = string -> int

let tryReadProgram (path: string) : Result<string, string> =
    try
        if File.Exists(path) then
            Ok (File.ReadAllText(path))
        else
            Error (sprintf "File non trovato: %s" path)
    with ex ->
        Error (sprintf "Errore durante la lettura del file: %s" ex.Message)

let rec askNonEmptyLine (prompt: string) =
    printf "%s" prompt
    let s = Console.ReadLine()
    if isNull s || String.IsNullOrWhiteSpace s then
        printfn "Input non valido."
        askNonEmptyLine prompt
    else
        s.Trim()

let rec askSN (prompt: string) =
    printf "%s" prompt
    match Console.ReadLine().Trim().ToUpperInvariant() with
    | "S" -> true
    | "N" -> false
    | _ ->
        printfn "Inserisci solo S oppure N."
        askSN prompt

let rec askInt (prompt: string) =
    printf "%s" prompt
    match Int32.TryParse(Console.ReadLine().Trim()) with
    | true, v -> v
    | false, _ ->
        printfn "Inserisci un intero valido."
        askInt prompt

let rec askCong () =
    printf "Inserisci m e r per Cong(m,r) oppure BOT: "
    let s=Console.ReadLine().Trim()
    match s.Trim() with
    | x when x.ToUpper() = "BOT" ->
        CongruenceValue.Bottom

    | x ->
        let parts = x.Split([|' '|], System.StringSplitOptions.RemoveEmptyEntries)
        match parts with
        | [|a; b|] ->
            match System.Int32.TryParse(a), System.Int32.TryParse(b) with
            | (true, m), (true, r) -> Cong (m, r)
            | _ ->
                printfn "Inserisci due interi validi oppure BOT."
                askCong()
        | _ ->
            printfn "Formato non valido. Usa: m r oppure BOT."
            askCong()

let parseBound (s: string) =
    match s.Trim().ToLowerInvariant() with
    | "-inf" | "-infty" | "-infinity" -> Some MinusInf
    | "+inf" | "inf" | "+infty" | "infty" | "+infinity" | "infinity" -> Some PlusInf
    | txt ->
        match Int32.TryParse txt with
        | true, v -> Some (Finite v)
        | false, _ -> None

let rec askBound (prompt: string) =
    printf "%s" prompt
    let s = Console.ReadLine()
    match parseBound s with
    | Some b -> b
    | None ->
        printfn "Bound non valido. Usa un intero, -inf oppure +inf."
        askBound prompt

let printState (state: State<'A>) =
    match state with
    | BottomState ->
        printfn "  Bottom state"
    | Vars vars ->
        if Map.isEmpty vars then
            printfn "  <empty map>"
        else
            for KeyValue(v,b) in vars do
                printfn "  %s = %A" v b

let chooseDomain () =
    let implemented =
        [ (1, "Intervals Domain", Intervals)
          (2, "Constant Propagation Domain", ConstantPropagation)
          (3, "Sign Domain", Sign)
          (4, "Congruence Domain", Congruence) ]

    printfn "Seleziona il dominio usando il numero:"
    for (i, name, _) in implemented do
        printfn "%d) %s" i name

    let rec loop () =
        let choice = askInt "> "
        match implemented |> List.tryFind (fun (i,_,_) -> i = choice) with
        | Some (_,_,dom) -> dom
        | None ->
            printfn "Scelta non valida."
            loop ()

    loop ()

let askAnalysisConfig () =
    let defaultWidening = true
    let defaultWidenAfter = 3
    let defaultNarrowing = true
    let defaultNarrowingSteps = 2

    printfn ""
    printfn "Configurazione widening/narrowing:"
    printfn "Default widening: %s  passaggi: %d"
        (if defaultWidening then "SI" else "NO")
        defaultWidenAfter
    printfn "Default narrowing: %s  passaggi: %d"
        (if defaultNarrowing then "SI" else "NO")
        defaultNarrowingSteps

    let acceptDefault =
        askSN "Inserisci S per accettare il default, N per modificare: "

    if acceptDefault then
        { useWidening = defaultWidening
          widenAfter = defaultWidenAfter
          useNarrowing = defaultNarrowing
          narrowingSteps = defaultNarrowingSteps }
    else
        let useWidening = askSN "Vuoi usare il widening? S/N: "
        let widenAfter =
            if useWidening then
                askInt "Dopo quanti aggiornamenti del loop head applicare widening? "
            else 0

        let useNarrowing = askSN "Vuoi usare il narrowing? S/N: "
        let narrowingSteps =
            if useNarrowing then
                askInt "Quanti passi di narrowing vuoi fare? "
            else 0

        { useWidening = useWidening
          widenAfter = widenAfter
          useNarrowing = useNarrowing
          narrowingSteps = narrowingSteps }

let askIntervalDomainParameters () =
    let acceptDefault =
        askSN "Usare i bound di dominio di default [-inf,+inf]? S/N: "

    if acceptDefault then
        MinusInf, PlusInf
    else
        let m = askBound "Inserisci m (lower bound del dominio, es. -inf, -10, 0): "
        let n = askBound "Inserisci n (upper bound del dominio, es. +inf, 10, 100): "
        m, n

let askInitialStateGeneric<'A>
    (title: string)
    (helpLines: string list)
    (askValue: unit -> 'A option)
    : State<'A> =

    printfn ""
    printfn "%s" title
    for line in helpLines do
        printfn "%s" line

    let count = askInt "Quante variabili vuoi inizializzare? "

    let rec loop i (acc: Map<string, 'A>) =
        if i > count then
            Vars acc
        else
            printfn ""
            printfn "Variabile %d di %d" i count
            let name = askNonEmptyLine "Nome variabile: "

            match askValue() with
            | Some value ->
                loop (i + 1) (acc |> Map.add name value)
            | None ->
                printfn "Valore non valido, reinserisci questa variabile."
                loop i acc

    loop 1 Map.empty

let askInitialIntervalState (createVarBound: Bound * Bound -> VariableBound) : State<VariableBound> =
    let askValue () =
        let lower = askBound "Lower bound (es. -inf, 0, 5): "
        let upper = askBound "Upper bound (es. +inf, 10, 20): "
        match createVarBound (lower, upper) with
        | VariableBound.Bottom -> None
        | vb -> Some vb

    askInitialStateGeneric
        "Inserimento stato iniziale per il dominio intervalli."
        [ "Le variabili NON inserite saranno trattate come Top quando lette nelle espressioni." ]
        askValue

let askInitialConstantState () : State<ConstantValue> =
    let parseConstValue (s: string) =
        let t = s.Trim().ToUpperInvariant()
        if t = "TOP" then Some ConstantValue.Top
        else
            match Int32.TryParse t with
            | true, v -> Some (ConstantValue.Const v)
            | false, _ -> None

    let askValue () =
        printf "Valore iniziale (intero oppure TOP): "
        let s = Console.ReadLine()
        parseConstValue s

    askInitialStateGeneric
        "Inserimento stato iniziale per il dominio constant propagation."
        [ "Per ogni variabile puoi inserire:"
          "  - un intero (es. 5)"
          "  - TOP"
          "Le variabili non inserite saranno trattate come Top quando lette nelle espressioni." ]
        askValue

let askInitialSignState () : State<SignValue> =
    let parseSignValue (s: string) =
        match s.Trim().ToUpperInvariant() with
        | "BOTTOM" -> Some SignValue.Bottom
        | "NEG" -> Some SignValue.Neg
        | "ZERO" -> Some SignValue.Zero
        | "POS" -> Some SignValue.Pos
        | "NONPOS" -> Some SignValue.NonPos
        | "NONZERO" -> Some SignValue.NonZero
        | "NONNEG" -> Some SignValue.NonNeg
        | "TOP" -> Some SignValue.Top
        | _ -> None

    let askValue () =
        printf "Valore iniziale (NEG, ZERO, POS, NONPOS, NONZERO, NONNEG, TOP): "
        let s = Console.ReadLine()
        parseSignValue s

    askInitialStateGeneric
        "Inserimento stato iniziale per il dominio dei segni."
        [ "Per ogni variabile puoi inserire uno tra:"
          "  NEG, ZERO, POS, NONPOS, NONZERO, NONNEG, TOP"
          "Le variabili non inserite saranno trattate come Top quando lette nelle espressioni." ]
        askValue

let askInitialCongruenceState () : State<CongruenceValue> =
    let askValue () =
        Some (normalizeCong (askCong()))

    askInitialStateGeneric
        "Inserimento stato iniziale per il dominio di congruenze."
        [ "Per ogni variabile puoi inserire:"
          "  - due interi m r per costruire Cong(m, r)"
          "  - BOT"
          "Convenzioni:"
          "  Cong(m, r) con m > 0 rappresenta { x in Z | x ≡ r (mod m) }"
          "  Cong(0, c) rappresenta la costante esatta {c}"
          "  Cong(1, 0) rappresenta Top"
          "Le variabili non inserite saranno trattate come Top quando lette nelle espressioni." ]
        askValue

let makePreparedAnalysis
    (name: string)
    (info: string)
    (domain: Domain<'A>)
    (initialState: State<'A>)
    (config: AnalysisConfig)
    : PreparedAnalysis<'A> =
    { Name = name
      Info = info
      Domain = domain
      InitialState = initialState
      Config = config }

let printCfgWithAnalysis (cfg: CFG) (resultStates: Map<NodeId, State<'A>>) =
    let allNodes =
        seq {
            yield cfg.Entry
            yield cfg.Exit
            for KeyValue(src, outs) in cfg.Edges do
                yield src
                for (_, dst) in outs do
                    yield dst
        }
        |> Set.ofSeq
        |> Set.toList
        |> List.sort

    let nodeTag n =
        [
            if n = cfg.Entry then yield "Entry"
            if n = cfg.Exit then yield "Exit"
            if Set.contains n cfg.WhileHeaders then yield "WhileHeader"
        ]
        |> String.concat ", "

    printfn "================ CFG + ANALYSIS ================"

    for n in allNodes do
        let tag = nodeTag n
        if tag = "" then
            printfn "Node %d:" n
        else
            printfn "Node %d (%s):" n tag

        match resultStates |> Map.tryFind n with
        | Some BottomState ->
            printfn "  State: BottomState"
        | Some (Vars vars) ->
            if Map.isEmpty vars then
                printfn "  State: <empty>"
            else
                printfn "  State:"
                for KeyValue(v, b) in vars do
                    printfn "    %s = %A" v b
        | None ->
            printfn "  State: <not reached>"

        match cfg.Edges |> Map.tryFind n with
        | Some outs when not (List.isEmpty outs) ->
            printfn "  Outgoing edges:"
            for (lbl, succ) in outs do
                printfn "    -- %A --> %d" lbl succ
        | _ ->
            printfn "  Outgoing edges: <none>"

        printfn ""

    printfn "==============================================="

let runPreparedAnalysis (prepared: PreparedAnalysis<'A>) (path: string) =
    printfn ""
    printfn "Dominio selezionato: %s" prepared.Name
    printfn "%s" prepared.Info
    printfn "Configurazione analisi:"
    printfn "  widening       = %b" prepared.Config.useWidening
    printfn "  widenAfter     = %d" prepared.Config.widenAfter
    printfn "  narrowing      = %b" prepared.Config.useNarrowing
    printfn "  narrowingSteps = %d" prepared.Config.narrowingSteps
    printfn "Stato iniziale:"
    printState prepared.InitialState

    match tryReadProgram path with
    | Error msg ->
        eprintfn "%s" msg
        1

    | Ok text ->
        let ast = runParser text
        match ast with
        | None ->
            eprintfn "Errore nel parsing del programma."
            1

        | Some programAst ->
            let cfg = buildCfg (Fresh()) programAst
            let resultStates =
                analyseFixpoint prepared.Domain cfg prepared.InitialState prepared.Config

            printCfgWithAnalysis cfg resultStates

            printfn ""
            printfn "Warnings:"
            if Set.isEmpty warnings then
                printfn "  Nessun warning."
            else
                for warning in warnings do
                    printfn "  %s" warning

            0

let prepareSignAnalysis (config: AnalysisConfig) : PreparedRun =
    let dom = makeSignDomain ()
    let startingState = askInitialSignState ()

    let prepared =
        makePreparedAnalysis
            "Sign Domain"
            "Dominio dei segni esteso"
            dom
            startingState
            config

    runPreparedAnalysis prepared

let prepareConstantPropagationAnalysis (config: AnalysisConfig) : PreparedRun =
    let dom = makeConstantPropagationDomain ()
    let startingState = askInitialConstantState ()

    let prepared =
        makePreparedAnalysis
            "Constant Propagation Domain"
            "Dominio di propagazione delle costanti"
            dom
            startingState
            config

    runPreparedAnalysis prepared

let prepareCongruenceAnalysis (config: AnalysisConfig) : PreparedRun =
    let dom = makeCongruenceDomain ()
    let startingState = askInitialCongruenceState ()

    let prepared =
        makePreparedAnalysis
            "Congruence Domain"
            "Dominio delle congruenze"
            dom
            startingState
            config

    runPreparedAnalysis prepared

let prepareIntervalAnalysis (config: AnalysisConfig) : PreparedRun =
    let (minBound, maxBound) = askIntervalDomainParameters ()

    if not (boundLe minBound maxBound) then
        printfn ""
        printfn "Hai inserito m > n."
        printfn "Int_{m,n} coincide con il Constant Propagation Domain."
        prepareConstantPropagationAnalysis config
    else
        let createVarBound = makeCreateVarBound minBound maxBound
        let dom = makeIntervalDomain minBound maxBound
        let startingState = askInitialIntervalState createVarBound

        let prepared =
            makePreparedAnalysis
                "Intervals Domain"
                (sprintf "Parametri dominio: [%A, %A]" minBound maxBound)
                dom
                startingState
                config

        runPreparedAnalysis prepared

[<EntryPoint>]
let main argv =
    if argv.Length <> 1 then
        printfn "Uso: dotnet run -- <file.while>"
        2
    else
        let path = argv[0]
        let config = askAnalysisConfig ()

        let run =
            match chooseDomain() with
            | ConstantPropagation -> prepareConstantPropagationAnalysis config
            | Intervals -> prepareIntervalAnalysis config
            | Sign -> prepareSignAnalysis config
            | Congruence -> prepareCongruenceAnalysis config

        run path