open Freefall.Expr

let Unknown = Variable ("x", Dimensionless)

let AlmostPi = Amount(PhysicalQuantity(Rational(22L,7L), Dimensionless))


[<EntryPoint>]
let main argv = 
    printfn "AlmostPi = %A = %s" AlmostPi (FormatExpression AlmostPi)
    0 // return an integer exit code

