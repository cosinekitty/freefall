open Freefall.Expr

let AlmostPi:Expression = Number(Rational(22L,7L))

[<EntryPoint>]
let main argv = 
    printfn "%A" AlmostPi
    0 // return an integer exit code

