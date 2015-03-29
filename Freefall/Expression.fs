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

    type PhysicalConcept = Concept of (int64 * int64) list       // list must have NumDimensions elements, each representing a rational number for the exponent of that dimension

    let Dimensionless = Concept (List.replicate NumDimensions (0L,1L))

    // A physical quantity is a numeric scalar attached to a physical concept.
    type PhysicalQuantity = PhysicalQuantity of Number * PhysicalConcept

    let Unity = PhysicalQuantity(Rational(1L,1L), Dimensionless)

    let IsZero number =
        match number with
        | Rational(numer,denom) -> numer=0L && denom<>0L
        | Real re -> re=0.0
        | Complex(re,im) -> re=0.0 && im=0.0

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

    let FormatDimension name (numer,denom) =
        if numer = 0L then
            ""      // this dimension does not contribute to formatting, e.g. meter^0
        elif numer = 1L && denom = 1L then
            name    // meter^(1/1) is written as "meter"
        elif denom = 1L then
            if numer < 0L then
                name + "^(" + numer.ToString() + ")"        // meter^(-1)
            else
                name + "^" + numer.ToString()               // meter^(3)
        else
            name + "^(" + numer.ToString() + "/" + denom.ToString() + ")"       // meter^(-1/3)

    let AccumDimension prefix name (numer,denom) =
        let text = FormatDimension name (numer,denom)
        match (prefix,text) with
        | ("","") -> ""
        | ("",_)  -> text
        | (_,"")  -> prefix
        | (_,_)   -> prefix + "*" + text

    let FormatConcept namelist (Concept(powlist)) =
        List.fold2 AccumDimension "" namelist powlist

    let FormatQuantity (PhysicalQuantity(scalar,concept)) =
        if IsZero scalar then
            "0"     // special case because zero makes all units irrelevant
        else
            let scalarText = FormatNumber scalar
            let conceptText = FormatConcept BaseUnitNames concept
            if conceptText = "" then
                scalarText
            elif scalarText = "1" then
                conceptText
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