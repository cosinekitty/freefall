// Freefall command-line interpreter program.
// Don Cross - http://cosinekitty.com
open Freefall.Scanner
open Freefall.Expr
open Freefall.Stmt
open Freefall.Parser
open Freefall.Intrinsic

let PrintTokenDiagnostic token =
    printfn "Near '%s' @ col %d" token.Text token.ColumnNumber
    match token.Origin with
    | None -> ()
    | Some({Filename=fn; LineNumber=ln;}) -> printfn "File %s [line %d]" fn ln

let PrintLineDiagnostic line token =
    let prefix = "===>  "
    printfn "%s%s" prefix line
    if token.ColumnNumber > 0 then
        let indent = String.replicate (prefix.Length + token.ColumnNumber - 1) " "
        printfn "%s^" indent
    PrintTokenDiagnostic token

let ExecuteStatements context tokenlist =
    let mutable scan = tokenlist
    while MoreTokensIn scan do
        let statement, scan2 = ParseStatement scan
        printfn "Statement: %s" (FormatStatement statement)
        ExecuteStatement context statement
        scan <- scan2

let PromptLine (lineNumber:int) =
    if not System.Console.IsInputRedirected then
        System.Console.Write("Freefall:{0}> ", lineNumber)
        System.Console.Out.Flush()
    System.Console.ReadLine()

let ExecuteLine context line lineNumber =
    try
        TokenizeLine line |> ExecuteStatements context
    with 
        | SyntaxException(token,message) ->
            printfn "SYNTAX ERROR : %s" message
            PrintLineDiagnostic line token

        | ExpressionException(expr,message) ->
            printfn "Error in subexpression '%s': %s" (FormatExpression expr) message
            match PrimaryToken expr with
            | None -> ()
            | Some(token) -> PrintLineDiagnostic line token

        | UnexpectedEndException(None) ->
            printfn "Syntax error: unexpected end of input"

        | UnexpectedEndException(Some(filename)) ->
            printfn "Syntax error: unexpected end of file '%s'" filename

let ExecuteFile context filename =
    if filename = "-" then
        // Placeholder for a console session instead of an input file.
        let mutable lineNumber = 1
        let mutable line = PromptLine lineNumber
        while line <> null do
            ExecuteLine context line lineNumber
            lineNumber <- 1 + lineNumber
            line <- PromptLine lineNumber
    else
        TokenizeFile filename |> ExecuteStatements context

let MyAssignmentHook (targetName:option<string>) (refIndex:int) (assignedExpr:Expression) =
    match targetName with
    | None -> ()
    | Some(name) -> printf "%s := " name
    printfn "#%d := %s" refIndex (FormatExpression assignedExpr)
    printfn ""

let MyProbeHook (expr:Expression) (range:NumericRange) (concept:PhysicalConcept) =
    printfn "PROBE(expr)    : %s" (FormatExpression expr)
    printfn "PROBE(range)   : %s" (RangeName range)
    printfn "PROBE(concept) : %s" (FormatConcept concept)
    printfn ""

[<EntryPoint>]
let main argv = 
    try
        let context = MakeContext MyAssignmentHook MyProbeHook
        Array.map (ExecuteFile context) argv |> ignore
        0
    with 
        | SyntaxException(token,message) ->
            printfn "SYNTAX ERROR : %s" message
            PrintTokenDiagnostic token
            1

        | ExpressionException(expr,message) ->
            printfn "Error in subexpression '%s': %s" (FormatExpression expr) message
            match PrimaryToken expr with
            | None -> ()
            | Some(token) -> PrintTokenDiagnostic token
            1

        | UnexpectedEndException(None) ->
            printfn "Syntax error: unexpected end of input"
            1

        | UnexpectedEndException(Some(filename)) ->
            printfn "Syntax error: unexpected end of file '%s'" filename
            1
