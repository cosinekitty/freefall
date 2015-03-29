open Freefall.Expr

let Unknown = Variable ("x", Dimensionless)

let AlmostPi = Amount(PhysicalQuantity(Rational(22L,7L), Dimensionless))


let Weight = Amount(PhysicalQuantity(Rational(3L,4L), ForceConcept))

let WeightSquared = Product[Weight;Weight]

let IdentityTest a b =
    if not (AreIdentical a b) then
        failwith (sprintf "IdentityTest FAILED: %s <> %s" (FormatExpression a) (FormatExpression b))
    else
        printfn "%s = %s" (FormatExpression a) (FormatExpression b)

[<EntryPoint>]
let main argv = 
    printfn "AlmostPi = %s" (FormatExpression AlmostPi)
    printfn "OneNewton = %s" (FormatExpression Weight)
    printfn "WeightSquared = %s" (FormatExpression WeightSquared)
    printfn "concept(WeightSquared) = %s" (FormatConcept (ExpressionConcept WeightSquared))

    let ForceVar = Variable("F", ForceConcept)
    let MyScalar = Amount(PhysicalQuantity(Real(7.28), Dimensionless))

    IdentityTest (Product[AlmostPi;ForceVar;MyScalar]) (Product[MyScalar;AlmostPi;ForceVar])

    0 // return an integer exit code

