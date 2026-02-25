
module Parser

open System
open FParsec
// ---------- AST minimale ----------
[<CustomComparison; CustomEquality>]
type Bound =
    | MinusInf
    | PlusInf
    | Finite of int
    interface IComparable with
        member this.CompareTo other =
            match other with
            | :? Bound as o ->
                match this, o with
                | MinusInf, MinusInf -> 0
                | PlusInf, PlusInf -> 0
                | Finite a, Finite b -> compare a b

                | MinusInf, _ -> -1
                | _, MinusInf -> 1

                | PlusInf, _ -> 1
                | _, PlusInf -> -1
            | _ -> invalidArg "other" "not a Bound"
    override this.Equals(other) =
        match other with
        | :? Bound as o ->
            match this, o with
            | MinusInf, MinusInf -> true
            | PlusInf, PlusInf -> true
            | Finite a, Finite b -> a = b
            | _ -> false
        | _ -> false
    override this.GetHashCode() =
        match this with
        | MinusInf -> hash 0
        | PlusInf -> hash 1
        | Finite v -> hash (2,v)

type Expr =
    | Int of int
    | Var of string
    | Minus of Expr
    | InputInt of Bound*Bound
    | Add of Expr * Expr
    | Sub of Expr * Expr
    | Div of Expr * Expr
    | Mul of Expr * Expr

type Cond =
    | Equi of Expr * Expr
    | Diff of Expr * Expr
    | Min of Expr * Expr
    | Mag of Expr * Expr
    | MinEqui of Expr * Expr
    | MagEqui of Expr * Expr
    | True
    | False
    | Neg of Cond
    | And of Cond * Cond
    | Or of Cond * Cond

type Stmt =
    | Skip
    | Assign of string * Expr
    | MaxBound of Bound
    | MinBound of Bound
    | Seq of Stmt list
    | If of Cond * Stmt * Stmt
    | While of Cond * Stmt
    | Assert of Cond

// ---------- Lexer helpers ----------
let ws : Parser<unit, unit> = spaces  // include newline
let str_ws (s: string) : Parser<string, unit> = pstring s .>> ws

let isIdentStart c = isLetter c || c = '_'
let isIdentCont c = isLetter c || isDigit c || c = '_'
let keywords = set [ "true"; "false"; "if"; "then"; "else"; "endif"; "while"; "do"; "done"; "skip"; "assert";"maxBound";"minBound"]

let keyword (s: string) : Parser<unit, unit> =
    pstring s .>> notFollowedBy (satisfy isIdentCont) .>> ws >>% ()

/// Parser identificatore: legge un nome valido e fallisce se è una keyword
let pIdent : Parser<string, unit> =
    many1Satisfy2L isIdentStart isIdentCont "identifier"
    >>= fun name ->
        if keywords.Contains name then
            fail $"'{name}' is a reserved keyword"
        else
            preturn name
    .>> ws

let pBoolConst : Parser<Cond, unit> =
    choice [
        keyword "true"  >>% True
        keyword "false" >>% False
    ]

let pInt : Parser<Expr, unit> =
    pint32 .>> ws |>> Int

let pBound : Parser<Bound, unit> =
    choice [
        stringReturn "-inf" MinusInf
        stringReturn "+inf" PlusInf
        pint32 |>> Finite
    ] .>> ws

let pInputInt : Parser<Expr, unit> =
    pipe2 (str_ws "[" >>. pBound) (str_ws "," >>. pBound .>> str_ws "]") (fun min max -> InputInt(min, max))


// ---------- Expression parser (precedenza: * > +) ----------
let expr, exprRef = createParserForwardedToRef<Expr, unit>()

let pParens : Parser<Expr, unit> =
    between (str_ws "(") (str_ws ")") expr
    
let pAtom, pAtomRef = createParserForwardedToRef<Expr, unit>()

let pMinus : Parser<Expr, unit> =
    str_ws "-" >>. pAtom |>> Minus

do pAtomRef.Value <-
    choice [
        pInt
        pInputInt
        pIdent |>> Var
        pParens
        pMinus
    ]


let oppMul : Parser<(Expr -> Expr -> Expr), unit> =
    str_ws "*" >>% (fun a b -> Mul(a,b))

let oppAdd : Parser<(Expr -> Expr -> Expr), unit> =
    str_ws "+" >>% (fun a b -> Add(a,b))

let oppSub : Parser<(Expr -> Expr -> Expr), unit> =
    str_ws "-" >>% (fun a b -> Sub(a,b))

let oppDiv : Parser<(Expr -> Expr -> Expr), unit> =
    str_ws "/" >>% (fun a b -> Div(a,b))

let oppAddSub : Parser<(Expr -> Expr -> Expr), unit> =
    choice [ oppAdd; oppSub ]

let oppMulDiv : Parser<(Expr -> Expr -> Expr), unit> =
    choice [ oppMul; oppDiv ]

do exprRef.Value <-
    // chainl1 costruisce espressioni left-associative
    let pTerm = chainl1 pAtom oppMulDiv
    chainl1 pTerm oppAddSub
//conditional parser
let cond, condRef = createParserForwardedToRef<Cond, unit>()

let pParensCond : Parser<Cond, unit> =
    between (str_ws "(") (str_ws ")") cond
    
let pAtomCond, pAtomCondRef = createParserForwardedToRef<Cond, unit>()

let pNeg : Parser<Cond, unit> =
    str_ws "¬" >>. pAtomCond |>> Neg

let oppEqui : Parser<(Expr -> Expr -> Cond), unit> =
    str_ws "=" >>% (fun a b -> Equi(a,b))

let oppDiff : Parser<(Expr -> Expr -> Cond), unit> =
    str_ws "!=" >>% (fun a b -> Diff(a,b))

let oppMin : Parser<(Expr -> Expr -> Cond), unit> =
    str_ws "<" >>% (fun a b -> Min(a,b))

let oppMag : Parser<(Expr -> Expr -> Cond), unit> =
    str_ws ">" >>% (fun a b -> Mag(a,b))

let oppMinEqui : Parser<(Expr -> Expr -> Cond), unit> =
    str_ws "<=" >>% (fun a b -> MinEqui(a,b))

let oppMagEqui : Parser<(Expr -> Expr -> Cond), unit> =
    str_ws ">=" >>% (fun a b -> MagEqui(a,b))
    
let oppAnd : Parser<(Cond -> Cond -> Cond), unit> =
    str_ws "∧" >>% (fun a b -> And(a,b))
    
let oppOr : Parser<(Cond -> Cond -> Cond), unit> =
    str_ws "∨" >>% (fun a b -> Or(a,b))



let oppRel : Parser<(Expr -> Expr -> Cond), unit> =
    choice [ oppDiff; oppEqui; oppMinEqui; oppMagEqui; oppMin; oppMag ]

let pRel : Parser<Cond, unit> =
    pipe3 expr oppRel expr (fun e1 op e2 -> op e1 e2)


do pAtomCondRef.Value <-
    choice [
        pBoolConst
        attempt pRel
        pParensCond
        pNeg
    ]
let oppCondCond : Parser<(Cond -> Cond -> Cond), unit> =
    choice [ oppAnd; oppOr ]

do condRef.Value <-
    // chainl1 costruisce espressioni left-associative
    let pTermCond = chainl1 pAtomCond oppAnd
    chainl1 pTermCond oppOr

// ---------- Statement parser ----------
let stmt, stmtRef = createParserForwardedToRef<Stmt, unit>()

let pSkip : Parser<Stmt, unit> =
    keyword "skip" >>% Skip
    
let pMaxBound : Parser<Stmt, unit> =
    pipe2 (keyword "maxBound" >>. str_ws ":=") pBound (fun x b -> MaxBound(b))

let pMinBound : Parser<Stmt, unit> =
    pipe2 (keyword "minBound" >>. str_ws ":=") pBound (fun x b -> MinBound(b))

let pAssign : Parser<Stmt, unit> =
    pipe2 (pIdent .>> str_ws ":=") expr (fun x e -> Assign(x, e))


let pSeq : Parser<Stmt, unit> =
    sepBy1 stmt (str_ws ";") |>> (fun ss -> if ss.Length = 1 then ss[0] else Seq ss)

let pIf : Parser<Stmt, unit> =
    pipe3 (keyword "if" >>. cond .>> keyword "then") pSeq  (keyword "else" >>. pSeq .>> keyword "endif")
        (fun c s1 s2 -> If(c, s1, s2))

let pWhile : Parser<Stmt, unit> =
    pipe2 (keyword "while" >>. cond .>> keyword "do") (pSeq .>> keyword "done") (fun c s -> While(c, s))

let pAssert : Parser<Stmt, unit> =
    (keyword "assert" >>. cond) |>> Assert

do stmtRef.Value <- choice [ pSkip;  pIf; pWhile; pAssert; pMaxBound; pMinBound; pAssign;]

// Programma = lista di statement separati da ';'
let pProgram : Parser<Stmt, unit> =
    ws >>. pSeq .>> ws .>> eof

// ---------- Test rapido ----------
let test (input: string) =
    match run pProgram input with
    | Success(ast, _, _) ->
        printfn "OK: %A" ast
        Some(ast)
    | Failure(err, _, _) ->
        printfn "ERR:\n%s" err
        None

let runParser (input: string) =
    match run pProgram input with
    | Success(ast, _, _) ->
        Some(ast)
    | Failure(err, _, _) ->
        printfn "ERR:\n%s" err
        None
