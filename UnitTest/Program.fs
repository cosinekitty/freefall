open Freefall.Expr
open Freefall.Scanner
open Freefall.Parser

let Unknown = Variable ("x", Dimensionless)

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

let FileTokenizerTest filename =
    let filepath = System.IO.Path.Combine("..", "..", "scripts", filename)
    printfn "Tokens for file %s :" filepath
    let tokenlist = TokenizeFile filepath
    for token in tokenlist do
        printfn "%A" token

[<EntryPoint>]
let main argv = 
    printfn "AlmostPi = %s" (FormatExpression AlmostPi)
    printfn "OneNewton = %s" (FormatExpression Weight)
    printfn "WeightSquared = %s" (FormatExpression WeightSquared)
    printfn "concept(WeightSquared) = %s" (FormatConcept (ExpressionConcept WeightSquared))

    let ForceVar = Variable("F", ForceConcept)
    let MyScalar = Amount(PhysicalQuantity(Real(7.28), Dimensionless))
    let WeirdValue = Power(ForceVar,AlmostPi)
    printfn "WeirdValue = %s, concept = %s" (FormatExpression WeirdValue) (FormatConcept (ExpressionConcept WeirdValue))

    IdentityTest (Product[AlmostPi;ForceVar;MyScalar]) (Product[MyScalar;AlmostPi;ForceVar])

    SimplifyTest (Sum[Sum[];Sum[ForceVar]])  ForceVar

    FileTokenizerTest "token.ff"

    0 // return an integer exit code

