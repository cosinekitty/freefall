namespace Freefall
module Expr =

    // FIXFIXFIX: Take a look at using BigRational, complex, etc, from https://github.com/fsprojects/powerpack

    type Number = 
        | Rational of int64 * int64
        | Real of float
        | Complex of float * float

    let ConceptNames  = [ "mass"     ; "distance" ; "time"   ; "temperature" ; "substance" ; "current" ; "luminosity" ]
    let BaseUnitNames = [ "kilogram" ; "meter"    ; "second" ; "kelvin"      ; "mole"      ; "ampere"  ; "candela"    ]
    let NumDimensions = List.length ConceptNames

    type PhysicalConcept = Concept of (int64 * int64) list       // list must have 7 elements, each representing a rational number - see comments above

    let Dimensionless = Concept (List.replicate NumDimensions (0L,1L))

    // A physical quantity is a numeric scalar attached to a physical concept.
    type PhysicalQuantity = PhysicalQuantity of Number * PhysicalConcept

    let Unity = PhysicalQuantity(Rational(1L,1L), Dimensionless)

    type Expression =
        | Amount of PhysicalQuantity
        | Variable of string * PhysicalConcept      // (name, units)
        | Negative of Expression
        | Reciprocal of Expression
        | Sum of Expression list
        | Product of Expression list
        | Power of Expression * Expression

    let FormatNumber x =
        match x with
        | Rational(numer,denom) ->
            if denom = 0L then
                failwith "Rational number had zero denominator."
            elif denom = 1L then
                numer.ToString()
            else
                numer.ToString() + "/" + denom.ToString()
        | Real re -> re.ToString()
        | Complex(re,im) -> "(" + re.ToString() + "," + im.ToString() + ")"

    let FormatDimension prefix name (numer,denom) =
        if numer = 0L then
            prefix      // this dimension does not contribute
        elif numer = 1L && denom = 1L then
            prefix + "*" + name
        elif denom = 1L then
            prefix + "*" + name + "^" + numer.ToString()
        else
            prefix + "*" + name + "^(" + numer.ToString() + "/" + denom.ToString() + ")"

    let FormatConcept namelist (Concept(powlist)) =
        List.fold2 FormatDimension "" namelist powlist

    let FormatQuantity (PhysicalQuantity(scalar,concept)) =

        let scalarText = FormatNumber scalar
        let conceptText = FormatConcept BaseUnitNames concept
        if conceptText = "" then
            scalarText
        else
            scalarText + "*" + conceptText

    let rec FormatExpression expr =
        match expr with
        | Amount quantity -> FormatQuantity quantity
        | Variable(name,_) -> name
        | Negative arg -> "neg(" + FormatExpression arg + ")"
        | Reciprocal arg -> "recip(" + FormatExpression arg + ")"
        | Sum terms -> "sum(" + FormatExprList terms + ")"
        | Product factors -> "prod(" + FormatExprList factors + ")"
        | Power(a,b) -> "pow(" + FormatExpression a + "," + FormatExpression b + ")"

    and FormatExprList list =
        match list with
        | [] -> ""
        | [single] -> FormatExpression single
        | first :: rest -> FormatExpression first + "," + FormatExprList rest