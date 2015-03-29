open Freefall.Expr

let Unknown = Variable ("x", Dimensionless)

let AlmostPi = Amount(PhysicalQuantity(Rational(22L,7L), Dimensionless))

let OneNewton = Amount(PhysicalQuantity(Rational(1L,1L), Concept[(1L,1L); (1L,1L); (-2L,1L); (0L,1L); (0L,1L); (0L,1L); (0L,1L)]))

[<EntryPoint>]
let main argv = 
    printfn "AlmostPi = %s" (FormatExpression AlmostPi)
    printfn "OneNewton = %s" (FormatExpression OneNewton)
    0 // return an integer exit code

