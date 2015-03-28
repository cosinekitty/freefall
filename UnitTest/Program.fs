open Freefall.Expr

let AlmostPi:Expression = Number(Real(3.14))

[<EntryPoint>]
let main argv = 
    printfn "%A" AlmostPi
    0 // return an integer exit code

