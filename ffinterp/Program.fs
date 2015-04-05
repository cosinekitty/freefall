// Freefall command-line interpreter program.
// Don Cross - http://cosinekitty.com
open Freefall.Scanner
open Freefall.Expr
open Freefall.Stmt
open Freefall.Parser
open Freefall.Intrinsic

let ExecuteFile context filename =
    let mutable scan = TokenizeFile filename
    while MoreTokensIn scan do
        let statement, scan2 = ParseStatement scan
        printfn "Statement: %s" (FormatStatement statement)
        ExecuteStatement context statement
        scan <- scan2

let MyAssignmentHook (targetName:option<string>) (refIndex:int) (assignedExpr:Expression) =
    match targetName with
    | None -> ()
    | Some(name) -> printf "%s := " name
    printfn "#%d := %s" refIndex (FormatExpression assignedExpr)
    printfn ""

[<EntryPoint>]
let main argv = 
    try
        let context = MakeContext MyAssignmentHook
        Array.map (ExecuteFile context) argv |> ignore
        0
    with 
        | SyntaxException(message,token) ->
            printfn "Syntax error near '%s' @ col %d: %s" token.Text token.ColumnNumber message
            match token.Origin with
            | None -> ()
            | Some({Filename=fn; LineNumber=ln;}) -> printfn "File %s [line %d]" fn ln
            1

        | ExpressionException(expr,message) ->
            printfn "Error in subexpression '%s': %s" (FormatExpression expr) message
            1

        | UnexpectedEndException(None) ->
            printfn "Syntax error: unexpected end of input"
            1

        | UnexpectedEndException(Some(filename)) ->
            printfn "Syntax error: unexpected end of file '%s'" filename
            1
