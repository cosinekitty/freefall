module UnitTest

open Freefall.Expr
open Freefall.Scanner
open Freefall.Parser

let MakeIdentifierToken name : Token =
    {Text=name; Precedence=Precedence_Atom; Kind=TokenKind.Identifier; Origin=None; ColumnNumber=0;}

let Unknown = Variable ((MakeIdentifierToken "x"), Dimensionless)

let AlmostPi = Amount(PhysicalQuantity(Rational(22L,7L), Dimensionless))

let Weight = Amount(PhysicalQuantity(Rational(3L,4L), ForceConcept))

let WeightSquared = Product[Weight;Weight]

let IdentityTest a b =
    if not (AreIdentical a b) then
        failwith (sprintf "IdentityTest FAILED: %s <> %s" (FormatExpression a) (FormatExpression b))
    else
        printfn "%s = %s" (FormatExpression a) (FormatExpression b)

let SimplifyTest raw expected =
    let simp = Simplify raw
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
        | Some({Filename=filename; LineNumber=lineNumber}) -> sprintf "%s %5d " filename lineNumber 
        | None -> ""

    printfn "%s %5d %d %-20s %-10s" originText columnNumber precedence kindString text

let FileTokenizerTest filename =
    let filepath = System.IO.Path.Combine("..", "..", "scripts", filename)
    printfn "Tokens for file %s :" filepath
    let tokenlist = TokenizeFile filepath
    for token in tokenlist do
        PrintToken token

[<EntryPoint>]
let main argv = 
    printfn "AlmostPi = %s" (FormatExpression AlmostPi)
    printfn "OneNewton = %s" (FormatExpression Weight)
    printfn "WeightSquared = %s" (FormatExpression WeightSquared)
    printfn "concept(WeightSquared) = %s" (FormatConcept (ExpressionConcept WeightSquared))

    let ForceVar = Variable((MakeIdentifierToken "F"), ForceConcept)
    let MyScalar = Amount(PhysicalQuantity(Real(7.28), Dimensionless))
    let WeirdValue = Power(ForceVar,AlmostPi)
    printfn "WeirdValue = %s, concept = %s" (FormatExpression WeirdValue) (FormatConcept (ExpressionConcept WeirdValue))

    IdentityTest (Product[AlmostPi;ForceVar;MyScalar]) (Product[MyScalar;AlmostPi;ForceVar])

    SimplifyTest (Sum[Sum[];Sum[ForceVar]])  ForceVar

    FileTokenizerTest "token.ff"
    FileTokenizerTest "pebble.ff"

    0 // return an integer exit code

