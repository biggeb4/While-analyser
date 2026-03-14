open System
open System.IO
open Parser
open CFGBuilder
open Analyser
open Eval

let tryReadFirstLineAndProgram (path: string): Result<string*string, string> =
    try
        if File.Exists(path) then
            let lines = File.ReadLines(path)
            let list = Seq.toList lines
            match list with
            | [] -> Error (sprintf "File vuoto: %s" path)
            | h::t -> Ok (h,t |> String.concat "\n")
        else
            Error (sprintf "File non trovato: %s" path)
    with ex ->
        Error (sprintf "Errore durante la lettura del file: %s" ex.Message)

let tryReadProgram (path: string) : Result<string, string> =
    try
        if File.Exists(path) then
            Ok (File.ReadAllText(path))
        else
            Error (sprintf "File non trovato: %s" path)
    with ex ->
        Error (sprintf "Errore durante la lettura del file: %s" ex.Message)

[<EntryPoint>]
let main argv =
    if argv.Length <> 1 then
        printfn "Uso: dotnet run -- <file.while>"
        2
    else
        let path = argv[0]
        match tryReadFirstLineAndProgram path with
        | Ok (line,text) ->
            let astfirstline = runParser line
            if astfirstline.IsSome then
                let cfg = buildCfg (Fresh()) astfirstline.Value
                let startingState=analyseStartingState (cfg,cfg.Entry,Vars(Map.empty))
                printfn "Dominio: [%A,%A]" minBound maxBound
                match startingState with
                | BottomState -> printfn "Bottom state iniziale"
                | Vars vars ->
                    for KeyValue(var,interval) in vars do
                        printfn "%s = %A" var interval
                let ast=test text
                if ast.IsSome then
                    let cfg = buildCfg (Fresh()) ast.Value
                    printCfg cfg
                    let resultStates = analyseFixpoint cfg startingState
                    for KeyValue(id,st) in resultStates do
                        printfn "Node %d:" id
                        match st with
                        | BottomState -> printfn "  Bottom state"
                        | Vars m ->
                            for KeyValue(v,b) in m do
                                printfn "  %s = %A" v b
                    printfn "Warnings:" 
                    for warning in warnings do
                        printfn "  %s" warning
            0
        | Error msg ->
            eprintfn "%s" msg
            1