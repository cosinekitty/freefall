open Freefall.Expr

let Unknown = Variable ("x", Dimensionless)

let AlmostPi = Amount(PhysicalQuantity(Rational(22L,7L), Dimensionless))

let Weight = Amount(PhysicalQuantity(Rational(3L,4L), Concept[(1L,1L); (1L,1L); (-2L,1L); (0L,1L); (0L,1L); (0L,1L); (0L,1L)]))

let WeightSquared = Product[Weight;Weight]

[<EntryPoint>]
let main argv = 
    printfn "AlmostPi = %s" (FormatExpression AlmostPi)
    printfn "OneNewton = %s" (FormatExpression Weight)
    printfn "WeightSquared = %s" (FormatExpression WeightSquared)
    printfn "concept(WeightSquared) = %s" (FormatOptConcept (ExpressionConcept WeightSquared))

    0 // return an integer exit code

