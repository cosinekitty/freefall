module UnitTest

open System.Collections.Generic
open Freefall.Expr
open Freefall.Scanner
open Freefall.Parser
open Freefall.Intrinsic

let MakeIdentifierToken name : Token =
    {Text=name; Precedence=Precedence_Atom; Kind=TokenKind.Identifier; Origin=None; ColumnNumber=0;}

let MyAssignmentHook (targetName:option<string>) (refIndex:int) (assignedExpr:Expression) =
    printf "ASSIGNMENT: "
    match targetName with
    | None -> ()
    | Some(name) -> printf "%s := " name
    printfn "#%d := %s" refIndex (FormatExpression assignedExpr)

let MyContext = MakeContext MyAssignmentHook

let VarTokenX = MakeIdentifierToken "x"
DefineSymbol MyContext VarTokenX (VariableEntry(RealRange,Dimensionless))

let SpeedConcept = DivideConcepts DistanceConcept TimeConcept
let AccelerationConcept = DivideConcepts SpeedConcept TimeConcept
let ForceConcept = MultiplyConcepts MassConcept AccelerationConcept

let VarTokenF = MakeIdentifierToken "F"
let ForceVar = Solitaire(VarTokenF)
DefineSymbol MyContext VarTokenF (VariableEntry(RealRange,ForceConcept))

let AlmostPi = Amount(PhysicalQuantity(Rational(22L,7L), Dimensionless))

let Weight = Amount(PhysicalQuantity(Rational(3L,4L), ForceConcept))

let WeightSquared = Product[Weight;Weight]

let IdentityTest a b =
    if not (AreIdentical MyContext a b) then
        failwith (sprintf "IdentityTest FAILED: %s <> %s" (FormatExpression a) (FormatExpression b))
    else
        printfn "%s = %s" (FormatExpression a) (FormatExpression b)

let SimplifyTest raw expected =
    let simp = Simplify MyContext raw
    if simp <> expected then
        printfn "SimplifyTest failed:"
        printfn "raw      = %s" (FormatExpression raw)
        printfn "simp     = %s" (FormatExpression simp)
        printfn "expected = %s" (FormatExpression expected)
        failwith "SimplifyTest failure"

let PrintToken ({Text=text; Kind=kind; Precedence=precedence; ColumnNumber=columnNumber; Origin=origin}) =
    let kindString = sprintf "%A" kind
    let originText = 
        match origin with
        | Some({Filename=filename; LineNumber=lineNumber}) -> sprintf "%s L[%5d] " filename lineNumber 
        | None -> ""

    printfn "%s C[%5d] %d %-20s %-10s" originText columnNumber precedence kindString text

let FileTokenizerTest filename =
    let filepath = System.IO.Path.Combine("..", "..", "scripts", filename)
    printfn "Tokens for file %s :" filepath
    let tokenlist = TokenizeFile filepath
    for token in tokenlist do
        PrintToken token

let ParseStatementsTest filename =
    let filepath = System.IO.Path.Combine("..", "..", "scripts", filename)
    let tokenlist = TokenizeFile filepath
    let mutable scan = tokenlist
    while scan <> [] do
        let statement, scan2 = ParseStatement scan
        printfn "Statement: %A" statement
        scan <- scan2

[<EntryPoint>]
let main argv = 
    try
        printfn "AlmostPi = %s" (FormatExpression AlmostPi)
        printfn "OneNewton = %s" (FormatExpression Weight)
        printfn "WeightSquared = %s" (FormatExpression WeightSquared)
        printfn "concept(WeightSquared) = %s" (FormatConcept (ExpressionConcept MyContext WeightSquared))

        let MyScalar = Amount(PhysicalQuantity(Real(7.28), Dimensionless))
        let WeirdValue = Power(Solitaire(VarTokenF),AlmostPi)
        printfn "WeirdValue = %s, concept = %s" 
            (FormatExpression WeirdValue) 
            (FormatConcept (ExpressionConcept MyContext WeirdValue))

        IdentityTest (Product[AlmostPi;ForceVar;MyScalar]) (Product[MyScalar;AlmostPi;ForceVar])

        SimplifyTest (Sum[Sum[];Sum[ForceVar]])  ForceVar

        //FileTokenizerTest "token.ff"
        //FileTokenizerTest "pebble.ff"
        ParseStatementsTest "statement.ff"

        0   // success exit code

    with SyntaxException(message,token) ->
        printfn "ERROR: %s" message
        PrintToken token
        1   // failure exit code