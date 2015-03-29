namespace Freefall
module Expr =

    // FIXFIXFIX: Take a look at using BigRational, complex, etc, from https://github.com/fsprojects/powerpack

    type Number = 
        | Rational of int64 * int64
        | Real of float
        | Complex of float * float

    let rec GreatestCommonDivisor (a:int64) (b:int64) =         // caller must ensure that a and b are both non-negative
        if b = 0L then
            if a = 0L then 1L else a
        else
            GreatestCommonDivisor b (a%b)

    let rec MakeRationalPair (numer:int64) (denom:int64) =
        if denom = 0L then 
            failwith "Rational number cannot have zero denominator."
        elif numer = 0L then
            (0L,1L)
        elif denom < 0L then
            MakeRationalPair (-numer) (-denom)
        else
            let gcd = GreatestCommonDivisor (System.Math.Abs(numer)) denom
            (numer/gcd, denom/gcd)

    let MakeRational (numer:int64) (denom:int64) =
        Rational(MakeRationalPair numer denom)

    let ConceptNames  = [ "mass"     ; "distance" ; "time"   ; "temperature" ; "substance" ; "current" ; "luminosity" ]
    let BaseUnitNames = [ "kilogram" ; "meter"    ; "second" ; "kelvin"      ; "mole"      ; "ampere"  ; "candela"    ]
    let NumDimensions = List.length ConceptNames

    type PhysicalConcept = 
        | Zero
        | Concept of (int64 * int64) list       // list must have NumDimensions elements, each representing a rational number for the exponent of that dimension

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

    //-----------------------------------------------------------------------------------------------------
    // Formatting - conversion of expressions to human-readable strings.

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

    let FormatDimensions namelist concept =
        match concept with
        | Zero -> "0"
        | Concept(powlist) -> List.fold2 AccumDimension "" namelist powlist

    let FormatConcept = FormatDimensions ConceptNames

    let FormatUnits = FormatDimensions BaseUnitNames

    let FormatQuantity (PhysicalQuantity(scalar,concept)) =
        if IsZero scalar then
            "0"     // special case because zero makes all units irrelevant
        else
            let scalarText = FormatNumber scalar
            let conceptText = FormatDimensions BaseUnitNames concept
            if conceptText = "" then
                scalarText
            elif conceptText = "0" then
                "0"
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

    //-----------------------------------------------------------------------------------------------------
    // Unit determination - verify that units are coherent and determine what they are.
    // For example, sum(3*meter,4*second) should raise an exception because adding distance to time is illegal.
    // However, sum(3*meter,4*meter) should be seen as distance units (expressible in meters).
    // Returns an Option(Concept) because None is needed for 0*anything, which has no specific units.
    // No other reason for returning None should be allowed;
    // must throw an exception for any unit compatibility violation.

    let AddExponentLists (alist:(int64 * int64) list) (blist:(int64 * int64) list) =
        List.map2 (fun (a,b) (c,d) -> MakeRationalPair (a*d + c*b) (b*d)) alist blist

    let rec ExpressionConcept expr =
        match expr with
        | Amount(PhysicalQuantity(number,concept)) -> if IsZero number then Zero else concept
        | Variable(_,concept) -> concept
        | Negative(arg) -> ExpressionConcept arg
        | Reciprocal(arg) -> ReciprocalConcept arg
        | Sum(terms) -> SumConcept terms
        | Product(factors) -> ProductConcept factors
        | Power(a,b) -> PowerConcept a b

    and SumConcept terms =
        match terms with 
        | [] -> Zero        // sum() = 0, which has no specific units -- see comments above.
        | first::rest -> 
            let firstConcept = ExpressionConcept first
            let restConcept = SumConcept rest
            match (firstConcept, restConcept) with
            | (Zero,Zero) -> Zero                    // 0+0 = 0, which has no specific units
            | (Concept(_),Zero) -> firstConcept      // x+0 = x with specific units
            | (Zero,Concept(_)) -> restConcept       // 0+y = y
            | (Concept(f),Concept(r)) ->
                if f <> r then
                    failwith (sprintf "Incompatible units: cannot add %s and %s" (FormatConcept firstConcept) (FormatConcept restConcept))
                else
                    firstConcept

    and ProductConcept factors =
        match factors with 
        | [] -> Dimensionless     // product() = 1, which has dimensionless units
        | first::rest ->
            let firstOptConcept = ExpressionConcept first
            let restOptConcept = ProductConcept rest
            match (firstOptConcept, restOptConcept) with
            | (Zero,_) -> Zero      // 0*y = 0, which has no definite units
            | (_,Zero) -> Zero      // x*0 = 0, which has no definite units
            | (Concept(alist),Concept(blist)) -> Concept(AddExponentLists alist blist)

    and PowerConcept a b =
        // FIXFIXFIX: plan - numerically reduce b, require it to be dimensionless rational.
        failwith "Not yet implemented."

    and ReciprocalConcept arg =
        match ExpressionConcept arg with
        | Zero -> Zero
        | Concept(dimlist) -> 
            // Take the reciprocal by negating each rational number in the list of dimensional exponents.
            Concept(List.map (fun (numer,denom) -> MakeRationalPair (-numer) denom) dimlist)
