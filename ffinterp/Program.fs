﻿// Freefall command-line interpreter program.
// Don Cross - http://cosinekitty.com
open Freefall.Partitions
open Freefall.Scanner
open Freefall.Expr
open Freefall.Stmt
open Freefall.Parser
open Freefall.Intrinsic
open Freefall.Latex
open Freefall.Html

let PrintTokenDiagnostic token =
    printfn "Near '%s' @ col %d" token.Text token.ColumnNumber
    match token.Origin with
    | None -> ()
    | Some({Filename=fn; LineNumber=ln;}) -> printfn "File %s [line %d]" fn ln

let PrintExecutionContext {FirstTokenInExecutingStatement = firstTokenRef} =
    let firstToken = !firstTokenRef
    if firstToken.Kind <> TokenKind.EndOfFile then
        printfn ""
        printfn "Executing statement diagnostic:"
        PrintTokenDiagnostic firstToken

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
        let firstTokenInStatement, statement, scan2 = ParseStatement scan
        printfn "Statement: %s" (FormatStatement statement)
        ExecuteStatement context firstTokenInStatement statement true
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
            PrintExecutionContext context

        | ExpressionException(expr,message) ->
            printfn "Error in subexpression '%s': %s" (FormatExpression expr) message
            match PrimaryToken expr with
            | None -> ()
            | Some(token) -> PrintLineDiagnostic line token
            PrintExecutionContext context

        | FreefallRuntimeException(message) ->
            printfn "Runtime error: %s" message
            PrintExecutionContext context

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
            // In console session, semicolons are optional to terminate a one-line statement.
            // It is a lot easier to hack here by putting a semicolon on when missing than
            // it is to rework the parser.
            if not (line.TrimEnd().EndsWith(";")) then      // FIXFIXFIX : does not handle comments in line
                line <- line + ";"
            ExecuteLine context line lineNumber
            lineNumber <- 1 + lineNumber
            line <- PromptLine lineNumber
    elif filename = "-t" then
        UnitTests context
        RunStandardScript context "tests.ff"
    else
        TokenizeFile filename |> ExecuteStatements context

let MyAssignmentHook (targetName:option<string>) (refIndex:int) (assignedExpr:Expression) =
    match targetName with
    | None -> ()
    | Some(name) -> printf "%s := " name
    printfn "#%d := %s" refIndex (FormatExpression assignedExpr)
    printfn ""

let MyProbeHook context expr range concept =
    printfn "PROBE(expr)    : %s" (FormatExpression expr)
    printfn "PROBE(raw)     : %s" (FormatExpressionRaw expr)
    printfn "PROBE(latex)   : %s" (FormatLatex context expr)
    printfn "PROBE(range)   : %s" (FormatRange range)
    printfn "PROBE(concept) : %s" (FormatConcept concept)
    printfn ""

let MyDecompHook (context:Context) (nodeArray:ResizeArray<DecompNode>) =
    for node in nodeArray do
        let fmt = FormatExpression node.Expr
        let raw = FormatExpressionRaw node.Expr
        if fmt = raw then
            // If there is no difference, don't be redundant in the output.
            printfn "DECOMP(%3d) : %s" node.Index fmt
        elif fmt.Length + raw.Length > 70 then
            // Split very long output across lines.
            printfn "DECOMP(%3d) : %s" node.Index fmt
            printfn "            : %s" raw
            printfn ""
        else
            // Fit all on one line
            printfn "DECOMP(%3d) : %s : %s" node.Index fmt raw

let PartitionTest (letters:string) =
    let mutable count = 0
    for part in Partitions (List.ofSeq letters) do
        String.concat ", " (List.map (fun charlist -> System.String(charlist |> List.toArray)) part) |> printfn "[%s]" 
        count <- count + 1

    // Printing the total count is handy for sanity-checking the algorithm.
    // See the sequence of "Bell numbers" at
    // http://mathworld.wolfram.com/BellNumber.html
    // 1, 2, 5, 15, 52, 203, 877, 4140, 21147, 115975, 678570, 4213597 ...
    // http://oeis.org/A000110/list
    printfn "count = %d" count

[<EntryPoint>]
let main argv = 
    match argv with
    | [| "-p"; letters |] ->
        PartitionTest letters
        0

    | [| "-pt"; letters |] ->       // partition speed test
        List.ofSeq letters |> Partitions |> Seq.length |> printfn "count = %d"
        0

    | _ ->
        let context = MakeContext MyAssignmentHook MyProbeHook HtmlSave MyDecompHook
        try
            InitContext context
            Array.iter (ExecuteFile context) argv
            0
        with 
            | SyntaxException(token,message) ->
                printfn "EXCEPTION : %s" message
                PrintTokenDiagnostic token
                PrintExecutionContext context
                1

            | ExpressionException(expr,message) ->
                printfn "EXCEPTION in subexpression '%s': %s" (FormatExpression expr) message
                match PrimaryToken expr with
                | None -> ()
                | Some(token) -> PrintTokenDiagnostic token
                PrintExecutionContext context
                1

            | FreefallRuntimeException(message) ->
                printfn "Runtime error: %s" message
                PrintExecutionContext context
                1

            | UnexpectedEndException(None) ->
                printfn "Syntax error: unexpected end of input"
                PrintExecutionContext context
                1

            | UnexpectedEndException(Some(filename)) ->
                printfn "Syntax error: unexpected end of file '%s'" filename
                PrintExecutionContext context
                1

            | :? System.IO.FileNotFoundException as ex ->
                printfn "ERROR: %s" ex.Message
                PrintExecutionContext context
                1
