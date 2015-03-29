open Freefall.Expr

let Unknown = Variable "x"

let AlmostPi = PhysicalQuantity(Rational(22L,7L), Dimensionless)


[<EntryPoint>]
let main argv = 
    printfn "%A" AlmostPi
    0 // return an integer exit code

