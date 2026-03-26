open System
open System.IO

open Parser
open CFGBuilder
open Analyser
open Eval
open IntervalDomain
open RefineIntervals

type ImplementedDomain =
    | Intervals

type PreparedAnalysis<'A> =
    { Name : string
      Info : string
      Domain : Domain<'A>
      InitialState : State<'A>
      Config : AnalysisConfig }

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
        [ (1, "Intervals Domain", Intervals) ]

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
    let defaultNarrowing = false
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
        let rec loop () =
            let m = askBound "Inserisci m (lower bound del dominio, es. -inf, -10, 0): "
            let n = askBound "Inserisci n (upper bound del dominio, es. +inf, 10, 100): "
            if boundLe m n then
                m, n
            else
                printfn "Valori non validi: deve valere m <= n."
                loop ()
        loop ()

let askInitialIntervalState (createVarBound: Bound * Bound -> VariableBound) : State<VariableBound> =
    printfn ""
    printfn "Inserimento stato iniziale per il dominio intervalli."
    printfn "Le variabili NON inserite saranno trattate come Top quando lette nelle espressioni."

    let count = askInt "Quante variabili vuoi inizializzare? "

    let rec loop i (acc: Map<string, VariableBound>) =
        if i > count then
            Vars acc
        else
            printfn ""
            printfn "Variabile %d di %d" i count
            let name = askNonEmptyLine "Nome variabile: "
            let lower = askBound "Lower bound (es. -inf, 0, 5): "
            let upper = askBound "Upper bound (es. +inf, 10, 20): "
            let vb = createVarBound (lower, upper)
            match vb with
            | Bottom ->
                printfn "Intervallo non valido, reinserisci questa variabile."
                loop i acc
            | _ ->
                loop (i + 1) (acc |> Map.add name vb)

    loop 1 Map.empty

let prepareIntervalAnalysis () : PreparedAnalysis<VariableBound> =
    let (minBound, maxBound) = askIntervalDomainParameters ()
    let config = askAnalysisConfig ()

    let createVarBound = makeCreateVarBound minBound maxBound
    let dom0 = makeIntervalDomain minBound maxBound
    let startingState = askInitialIntervalState createVarBound
    let useRefiner = askSN "Per il Dominio intervalli è possibile usare un back refiner, vuoi usarlo S/N?"
    if useRefiner then
        let refiner = makeIntervalRefiner dom0 createVarBound
        let dom = { dom0 with refine = Some refiner }
        { Name = "Intervals Domain"
          Info = sprintf "Parametri dominio: [%A, %A]" minBound maxBound
          Domain = dom
          InitialState = startingState
          Config = config }
    else
        { Name = "Intervals Domain"
          Info = sprintf "Parametri dominio: [%A, %A]" minBound maxBound
          Domain = dom0
          InitialState = startingState
          Config = config }

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
        let ast = test text
        match ast with
        | None ->
            eprintfn "Errore nel parsing del programma."
            1

        | Some programAst ->
            let cfg = buildCfg (Fresh()) programAst
            printfn ""
            printCfg cfg
            printfn ""

            let resultStates =
                analyseFixpoint prepared.Domain cfg prepared.InitialState prepared.Config

            printfn "Risultato analisi:"
            for KeyValue(id, st) in resultStates do
                printfn "Node %d:" id
                printState st

            printfn ""
            printfn "Warnings:"
            if Set.isEmpty warnings then
                printfn "  Nessun warning."
            else
                for warning in warnings do
                    printfn "  %s" warning

            0

[<EntryPoint>]
let main argv =
    if argv.Length <> 1 then
        printfn "Uso: dotnet run -- <file.while>"
        2
    else
        let path = argv[0]

        match chooseDomain() with
        | Intervals ->
            let prepared = prepareIntervalAnalysis()
            runPreparedAnalysis prepared path