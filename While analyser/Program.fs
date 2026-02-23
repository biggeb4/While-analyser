open System
open System.IO
open Parser
open CFGBuilder
open Analyser

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
                let startingState=analyseStartingState (cfg,cfg.Entry,Map.empty)
                printfn "Dominio: [%A,%A]" minBound maxBound
                printfn "Stato iniziale: %A" startingState
            let ast=test text
            if ast.IsSome then
                let cfg = buildCfg (Fresh()) ast.Value
                printCfg cfg
            0
        | Error msg ->
            eprintfn "%s" msg
            1