// Freefall command-line interpreter program.
// Don Cross - http://cosinekitty.com

open Freefall.Expr
open Freefall.Scanner
open Freefall.Parser

let ExecuteFile filename =
    let mutable scan = TokenizeFile filename
    while scan <> [] do
        let statement, scan2 = ParseStatement scan
        printfn "Statement: %A" statement
        scan <- scan2

[<EntryPoint>]
let main argv = 
    try
        let context = MakeContext ()
        Array.map ExecuteFile argv |> ignore
        0
    with 
        | SyntaxException(message,token) ->
            printfn "Syntax error near '%s' @ col %d: %s" token.Text token.ColumnNumber message
            match token.Origin with
            | None -> ()
            | Some({Filename=fn; LineNumber=ln;}) -> printfn "File %s [line %d]" fn ln
            1

        | UnexpectedEndException ->
            printfn "Syntax error: unexpected end of file"   // FIXFIXFIX: determine WHICH file!
            1
