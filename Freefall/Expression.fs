namespace Freefall
module Expr =

    // FIXFIXFIX: Take a look at using BigRational, complex, etc, from https://github.com/fsprojects/powerpack

    type Number = 
        | Rational of int64 * int64
        | Real of float
        | Complex of float * float

    // Based on the 7 SI base units:
    // http://www.npl.co.uk/reference/measurement-units/
    // [0] mass         : kilogram
    // [1] distance     : meter
    // [2] time         : second
    // [3] temperature  : kelvin
    // [4] substance    : mole
    // [5] current      : ampere
    // [6] luminosity   : candela
    let NumDimensions = 7
    type PhysicalConcept = Concept of (int64 * int64) list       // list must have 7 elements, each representing a rational number - see comments above

    let Dimensionless = Concept (List.replicate NumDimensions (0L,0L))

    // A physical quantity is a numeric scalar attached to a physical concept.
    type PhysicalQuantity = PhysicalQuantity of Number * PhysicalConcept

    let Unity = PhysicalQuantity(Rational(1L,1L), Dimensionless)

    type Expression =
        | Quantity of PhysicalQuantity
        | Variable of string
