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

let ExecuteStatements context tokenlist =
    let mutable scan = tokenlist
    while MoreTokensIn scan do
        let statement, scan2 = ParseStatement scan
        printfn "Statement: %s" (FormatStatement statement)
        ExecuteStatement context statement
        scan <- scan2

let ExecuteFile context filename =
    if filename = "-" then
        // Placeholder for a console session instead of an input file.
        printf "Freefall> "
        let mutable line = System.Console.ReadLine()
        let mutable lineNumber = 0
        while line <> null do
            lineNumber <- 1 + lineNumber
            try
                TokenizeLine line |> ExecuteStatements context
            with 
                | SyntaxException(token,message) ->
                    printfn "SYNTAX ERROR : %s" message
                    PrintTokenDiagnostic token

                | ExpressionException(expr,message) ->
                    printfn "Error in subexpression '%s': %s" (FormatExpression expr) message
                    match PrimaryToken expr with
                    | None -> ()
                    | Some(token) -> PrintTokenDiagnostic token

                | UnexpectedEndException(None) ->
                    printfn "Syntax error: unexpected end of input"

                | UnexpectedEndException(Some(filename)) ->
                    printfn "Syntax error: unexpected end of file '%s'" filename

            printf "Freefall> "
            line <- System.Console.ReadLine()
    else
        TokenizeFile filename |> ExecuteStatements context

let MyAssignmentHook (targetName:option<string>) (refIndex:int) (assignedExpr:Expression) =
    match targetName with
    | None -> ()
    | Some(name) -> printf "%s := " name
    printfn "#%d := %s" refIndex (FormatExpression assignedExpr)
    printfn ""

let MyProbeHook (expr:Expression) (range:NumericRange) =
    printfn "PROBE(expr ): %s" (FormatExpression expr)
    printfn "PROBE(range): %s" (RangeName range)
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
