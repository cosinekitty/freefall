// Expression.fs  -  Don Cross  -  http://cosinekitty.com
// Symbolic algebra/physics helper.

module Freefall.Expr
open Scanner

// FIXFIXFIX: Take a look at using BigRational, complex, etc, from https://github.com/fsprojects/powerpack

type Number = 
    | Rational of int64 * int64
    | Real of float
    | Complex of float * float

let NegateNumber number =
    match number with
    | Rational(numer,denom) -> Rational(-numer,denom)
    | Real(x) -> Real(-x)
    | Complex(x,y) -> Complex(-x,-y)

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

let AddExponentLists (alist:(int64 * int64) list) (blist:(int64 * int64) list) =
    List.map2 (fun (a,b) (c,d) -> MakeRationalPair (a*d + c*b) (b*d)) alist blist

let SubtractExponentLists (alist:(int64 * int64) list) (blist:(int64 * int64) list) =
    List.map2 (fun (a,b) (c,d) -> MakeRationalPair (a*d - c*b) (b*d)) alist blist        

let NegateExponentList (clist:(int64 * int64) list) =
    List.map (fun (a,b) -> MakeRationalPair (-a) b) clist

let rec AddNumbers anum bnum =
    match (anum, bnum) with
    | (Rational(a,b), Rational(c,d)) -> MakeRational (a*d + b*c) (b*d)
    | (Rational(a,b), Real(r)) -> Real(r + (float a)/(float b))
    | (Rational(a,b), Complex(x,y)) -> Complex(x + (float a)/(float b), y)
    | (Real(_), Rational(_,_)) -> AddNumbers bnum anum
    | (Real(x), Real(y)) -> Real(x + y)
    | (Real(r), Complex(x,y)) -> Complex(r+x, y)
    | (Complex(_,_), Rational(_,_)) -> AddNumbers bnum anum
    | (Complex(_,_), Real(_)) -> AddNumbers bnum anum
    | (Complex(x,y), Complex(u,v)) -> Complex(x+u, y+v)

let rec MultiplyNumbers anum bnum =
    match (anum, bnum) with
    | (Rational(a,b), Rational(c,d)) -> MakeRational (a*c) (b*d)
    | (Rational(a,b), Real(r)) -> Real(r * (float a)/(float b))
    | (Rational(a,b), Complex(x,y)) -> 
        let ratio = (float a) / (float b)
        Complex(ratio*x, ratio*y)
    | (Real(_), Rational(_,_)) -> MultiplyNumbers bnum anum
    | (Real(x), Real(y)) -> Real(x * y)
    | (Real(r), Complex(x,y)) -> Complex(r*x, r*y)
    | (Complex(_,_), Rational(_,_)) -> MultiplyNumbers bnum anum
    | (Complex(_,_), Real(_)) -> MultiplyNumbers bnum anum
    | (Complex(x,y), Complex(u,v)) -> Complex(x*u - y*v, x*v + y*u)

let ConceptNames  = [ "mass"     ; "distance" ; "time"   ; "temperature" ; "substance" ; "current" ; "luminosity" ]
let BaseUnitNames = [ "kilogram" ; "meter"    ; "second" ; "kelvin"      ; "mole"      ; "ampere"  ; "candela"    ]
let NumDimensions = List.length ConceptNames

type PhysicalConcept = 
    | Zero
    | Concept of (int64 * int64) list       // list must have NumDimensions elements, each representing a rational number for the exponent of that dimension

// Functions to help build concepts from other concepts...

let AddConcepts a b =
    match (a,b) with
    | (_,Zero) -> a
    | (Zero,_) -> b
    | (Concept(alist),Concept(blist)) ->
        if alist = blist then
            a
        else
            failwith "Cannot add incompatible concepts."

let MultiplyConcepts a b =
    match (a,b) with
    | (_,Zero) -> Zero
    | (Zero,_) -> Zero
    | (Concept(alist),Concept(blist)) -> Concept(AddExponentLists alist blist)

let DivideConcepts a b =
    match (a,b) with
    | (_,Zero) -> failwith "Cannot divide concept by 0."
    | (Zero,_) -> Zero
    | (Concept(alist),Concept(blist)) -> Concept(SubtractExponentLists alist blist)

let InvertConcept c =
    match c with
    | Zero -> failwith "Cannot take reciprocal of 0 concept."
    | Concept(clist) -> Concept(NegateExponentList clist)

let ExponentiateConcept xconcept ynum yden =
    match xconcept with
    | Concept(xlist) -> Concept(List.map (fun (xnum,xden) -> MakeRationalPair (xnum*ynum) (xden*yden)) xlist)
    | Zero ->
        if ynum = 0L then
            failwith "Cannot raise 0 to the 0 power."
        elif ynum < 0L then
            failwith "Cannot raise 0 to a negative power."
        else
            Zero    // 0^x = 0 for all positive rational x

// Handy concepts by name...

// A concept to represent any dimensionless quantity...
let Dimensionless       = Concept[(0L,1L); (0L,1L); (0L,1L); (0L,1L); (0L,1L); (0L,1L); (0L,1L)]

// Fundamental base concepts...
let MassConcept         = Concept[(1L,1L); (0L,1L); (0L,1L); (0L,1L); (0L,1L); (0L,1L); (0L,1L)]
let DistanceConcept     = Concept[(0L,1L); (1L,1L); (0L,1L); (0L,1L); (0L,1L); (0L,1L); (0L,1L)]
let TimeConcept         = Concept[(0L,1L); (0L,1L); (1L,1L); (0L,1L); (0L,1L); (0L,1L); (0L,1L)]
let TemperatureConcept  = Concept[(0L,1L); (0L,1L); (0L,1L); (1L,1L); (0L,1L); (0L,1L); (0L,1L)]
let SubstanceConcept    = Concept[(0L,1L); (0L,1L); (0L,1L); (0L,1L); (1L,1L); (0L,1L); (0L,1L)]
let CurrentConcept      = Concept[(0L,1L); (0L,1L); (0L,1L); (0L,1L); (0L,1L); (1L,1L); (0L,1L)]
let LuminosityConcept   = Concept[(0L,1L); (0L,1L); (0L,1L); (0L,1L); (0L,1L); (0L,1L); (1L,1L)]

// Compound concepts...

let SpeedConcept = DivideConcepts DistanceConcept TimeConcept           // speed = distance/time
let AccelerationConcept = DivideConcepts SpeedConcept TimeConcept       // accleration = speed/time
let ForceConcept = MultiplyConcepts MassConcept AccelerationConcept     // force = mass * acceleration

// A physical quantity is a numeric scalar attached to a physical concept.
type PhysicalQuantity = PhysicalQuantity of Number * PhysicalConcept

let ZeroQuantity = PhysicalQuantity(Rational(0L,1L), Zero)
let Unity = PhysicalQuantity(Rational(1L,1L), Dimensionless)

let IsNumberEqualToInteger n x =
    match x with
    | Rational(numer,denom) -> (numer = n) && (denom = 1L)      // assumes rational was created using MakeRational to normalize
    | Real re -> re = (float n)
    | Complex(re,im) -> (im = 0.0) && (re = (float n))

let IsNumberZero = IsNumberEqualToInteger 0L

let InvertNumber number =        // calculate the numeric reciprocal
    if IsNumberZero number then
        failwith "Cannot take reciprocal of 0."
    else
        match number with
        | Rational(a,b) -> Rational(b,a)
        | Real x -> Real(1.0 / x)
        | Complex(x,y) -> 
            // 1/(x+iy) = (x-iy)/(x^2+y^2)
            let denom = x*x + y*y
            Complex(x/denom, -y/denom)

type Expression =
    | Amount of PhysicalQuantity
    | Variable of Token * PhysicalConcept      // (name, units)
    | Negative of Expression
    | Reciprocal of Expression
    | Sum of Expression list
    | Product of Expression list
    | Power of Expression * Expression
 
let ZeroAmount = Amount(ZeroQuantity)
let UnityAmount = Amount(Unity)

let IsZeroExpression expr =
    match expr with
    | Amount(PhysicalQuantity(number,concept)) -> (concept = Zero) || (IsNumberZero number)
    | _ -> false

let IsUnityExpression expr =
    match expr with
    | Amount(PhysicalQuantity(number,concept)) -> (concept = Dimensionless) && (IsNumberEqualToInteger 1L number)
    | _ -> false

let RemoveZeroes terms = 
    List.filter (fun t -> not (IsZeroExpression t)) terms

let RemoveUnities factors =
    List.filter (fun f -> not (IsUnityExpression f)) factors

let SkipUnity first rest =
    if IsUnityExpression first then rest else first :: rest

let SkipZero first rest =
    if IsZeroExpression first then rest else first :: rest

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
    if IsNumberZero scalar then
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
    | Variable(token,_) -> token.Text
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
// Identity tester : determines if two expressions have equivalent values.
// For example, sum(a,b,c) looks different from sum(b,c,a), but are identical.

let IsZeroNumberConceptPair number concept =
    (concept = Zero) || (IsNumberZero number)

let rec AreIdenticalNumbers a b =
    match (a,b) with
    | (Rational(anum,aden),Rational(bnum,bden)) -> anum*bden = bnum*aden
    | (Rational(anum,aden),Real(br)) -> (float anum) = br*(float aden)
    | (Rational(anum,aden),Complex(br,bi)) -> (bi = 0.0) && (AreIdenticalNumbers a (Real(br)))
    | (Real(ar),Rational(_,_)) -> AreIdenticalNumbers b a
    | (Real(ar),Real(br)) -> ar = br
    | (Real(ar),Complex(br,bi)) -> (bi = 0.0) && (ar = br)
    | (Complex(_,_),Rational(_,_)) -> AreIdenticalNumbers b a
    | (Complex(_,_),Real(_)) -> AreIdenticalNumbers b a
    | (Complex(ar,ai),Complex(br,bi)) -> (ar = br) && (ai = bi)

let rec AreIdentical a b =
    match (a,b) with
    | (Amount(PhysicalQuantity(aNumber,aConcept)), Amount(PhysicalQuantity(bNumber,bConcept))) -> 
        AreIdenticalQuantities aNumber aConcept bNumber bConcept
    | (Amount(_), _) -> false
    | (Variable(aToken,aConcept), Variable(bToken,bConcept)) ->
        (aToken.Text = bToken.Text) && (
            (aConcept = bConcept) || 
            // FIXFIXFIX : create exception type for attributing errors to tokens
            failwith (sprintf "Mismatching variable %s concepts : %s and %s" aToken.Text (FormatConcept aConcept) (FormatConcept bConcept))
        )
    | (Variable(_), _) -> false
    | (Negative(na),Negative(nb)) -> AreIdentical na nb
    | (Negative(_), _) -> false
    | (Reciprocal(ra),Reciprocal(rb)) -> AreIdentical ra rb
    | (Reciprocal(_), _) -> false
    | (Sum(aterms),Sum(bterms)) -> ArePermutedLists aterms bterms
    | (Sum(_), _) -> false
    | (Product(afactors),Product(bfactors)) -> ArePermutedLists afactors bfactors
    | (Product(_), _) -> false
    | (Power(abase,aexp),Power(bbase,bexp)) -> (AreIdentical abase bbase) && (AreIdentical aexp bexp)
    | (Power(_,_), _) -> false

and AreIdenticalQuantities aNumber aConcept bNumber bConcept =
    let aIsZero = IsZeroNumberConceptPair aNumber aConcept
    let bIsZero = IsZeroNumberConceptPair bNumber bConcept
    if aIsZero || bIsZero then
        // If either is zero, then then both must be zero to match.
        aIsZero = bIsZero
    else
        // Neither is zero, so we must match numbers and concepts both.
        (aConcept = bConcept) && (AreIdenticalNumbers aNumber bNumber)

and ArePermutedLists alist blist =
    if List.length alist <> List.length blist then
        false   // cannot possibly match if the lists have different lengths (important optimization to avoid lots of pointless work)
    else
        match (alist, blist) with
            | ([], []) -> true
            | ([], _::_) -> failwith "impossible case 1"    // cannot happen because we already matched list lengths above
            | (_::_, []) -> failwith "impossible case 2"    // cannot happen because we already matched list lengths above
            | (afirst::arest, bfirst::brest) -> 
                // Try to find afirst in bterms.
                // If not found, immediately return false.
                // If found, cancel it with its buddy in bterms, yielding arest and bshorter, then recurse.
                match FindIdenticalInList afirst blist with
                | None -> false
                | Some(bshorter) -> ArePermutedLists arest bshorter
        
// The following function searches for an element of list that
// is mathematically identical to expr.  If found, returns Some(shorter)
// where shorter is list with the identical element removed.
// Otherwise, returns None.
and FindIdenticalInList expr list =
    match list with
    | [] -> None
    | first::rest -> 
        if AreIdentical expr first then
            Some(rest)
        else
            match FindIdenticalInList expr rest with
            | None -> None
            | Some(shorter) -> Some(first :: shorter)

//-----------------------------------------------------------------------------------------------------
// Expression simplifier.

let AddQuantities (PhysicalQuantity(aNumber,aConcept)) (PhysicalQuantity(bNumber,bConcept)) =
    Amount(PhysicalQuantity(AddNumbers aNumber bNumber, AddConcepts aConcept bConcept))

let MultiplyQuantities (PhysicalQuantity(aNumber,aConcept)) (PhysicalQuantity(bNumber,bConcept)) =
    Amount(PhysicalQuantity(MultiplyNumbers aNumber bNumber, MultiplyConcepts aConcept bConcept))

let AreOppositeTerms a b =
    (AreIdentical a (Negative b)) ||
    (AreIdentical b (Negative a))

let AreOppositeFactors a b =
    (AreIdentical a (Reciprocal b)) ||
    (AreIdentical b (Reciprocal a))

let rec CancelOpposite testfunc termlist =
    match termlist with
    | [] -> []
    | first :: rest -> 
        let rcancel = CancelOpposite testfunc rest
        match rcancel with
        | [] -> [first]
        | next :: others -> 
            if testfunc first next then
                others
            else
                let shorter = first :: others
                let attempt = CancelOpposite testfunc shorter
                if shorter = attempt then
                    first :: rcancel
                else
                    CancelOpposite testfunc (next :: attempt)

let CancelOppositeTerms termlist = CancelOpposite AreOppositeTerms termlist

let CancelOppositeFactors factorlist = CancelOpposite AreOppositeFactors factorlist

// Add together all constant terms in a sum list and move the result to the front of the list.
let rec MergeConstants mergefunc terms =
    match terms with
    | [] -> []
    | [first] -> [first]
    | first :: rest -> 
        let mrest = MergeConstants mergefunc rest
        match (first, mrest) with
        | (Amount(a), Amount(b) :: residue) -> mergefunc a b :: residue
        | (_, Amount(b) :: residue) -> Amount(b) :: first :: residue
        | _ -> first :: mrest

let rec SimplifyStep expr =
    match expr with
    | Amount(_) -> expr     // already as simple as possible
    | Variable(_) -> expr   // already as simple as possible
    | Negative(Negative(x)) -> SimplifyStep x
    | Negative(arg) -> 
        match SimplifyStep arg with
        | Amount(PhysicalQuantity(number,concept)) -> Amount(PhysicalQuantity((NegateNumber number),concept))
        | sarg -> Negative(sarg)

    | Reciprocal(Reciprocal(x)) -> SimplifyStep x
    | Reciprocal(arg) -> 
        match SimplifyStep arg with
        | Amount(PhysicalQuantity(number,concept)) -> Amount(PhysicalQuantity((InvertNumber number), (InvertConcept concept)))
        | sarg -> Reciprocal(sarg)

    | Sum(termlist) ->
        let simpargs = 
            SimplifySumArgs (List.map SimplifyStep termlist) 
            |> CancelOppositeTerms 
            |> MergeConstants AddQuantities
        match simpargs with
        | [] -> ZeroAmount
        | [term] -> term
        | _ -> Sum simpargs

    | Product(factorlist) ->
        let simpfactors = 
            SimplifyProductArgs (List.map SimplifyStep factorlist) 
            |> CancelOppositeFactors
            |> MergeConstants MultiplyQuantities
        if List.exists IsZeroExpression simpfactors then
            ZeroAmount
        else
            match simpfactors with
            | [] -> UnityAmount
            | [factor] -> factor
            | _ -> Product simpfactors
    | Power(x,y) ->
        let sx = SimplifyStep x
        let sy = SimplifyStep y
        // FIXFIXFIX - could use more simplification and validation rules here
        if (IsZeroExpression sx) && (IsZeroExpression sy) then
            failwith "Cannot evaluate 0^0."
        else
            Power(sx,sy)            

// Sum(Sum(A,B,C), Sum(D,E)) = Sum(A,B,C,D,E)
// We want to "lift" all inner Sum() contents to the top level of a list.
and SimplifySumArgs simpargs =           
    match simpargs with
    | [] -> []
    | (Sum terms)::rest -> (RemoveZeroes terms) @ (SimplifySumArgs rest)
    | first::rest -> SkipZero first (SimplifySumArgs rest)

and SimplifyProductArgs simpargs =           
    match simpargs with
    | [] -> []
    | (Product factors)::rest -> (RemoveUnities factors) @ (SimplifyProductArgs rest)
    | first::rest -> SkipUnity first (SimplifyProductArgs rest)

//---------------------------------------------------------------------------
// Aggressive, iterative simplifier...

let Simplify expr =
    // Keep iterating SimplifyStep until the expression stops changing.
    let mutable prev = expr
    let mutable simp = SimplifyStep expr
    while simp <> prev do
        prev <- simp
        simp <- SimplifyStep simp
    simp

//-----------------------------------------------------------------------------------------------------
// Unit determination - verify that units are coherent and determine what they are.
// For example, sum(3*meter,4*second) should raise an exception because adding distance to time is illegal.
// However, sum(3*meter,4*meter) should be seen as distance units (expressible in meters).
// Returns an Option(Concept) because None is needed for 0*anything, which has no specific units.
// No other reason for returning None should be allowed;
// must throw an exception for any unit compatibility violation.

let rec ExpressionConcept expr =
    match expr with
    | Amount(PhysicalQuantity(number,concept)) -> if IsNumberZero number then Zero else concept
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
    | first::rest -> MultiplyConcepts (ExpressionConcept first) (ProductConcept rest)

and PowerConcept x y =
    let yConcept = ExpressionConcept y
    if yConcept = Dimensionless then
        let xConcept = ExpressionConcept x
        if xConcept = Dimensionless then
            // If x is dimensionless, then y may be any dimensionless expression, e.g. 2.7182818^y.
            // A dimensionless value to a dimensionless power is dimensionless.
            Dimensionless
        else
            // If x is dimensional, then y must be rational (e.g. x^(-3/4)).
            // In this case, multiply the exponent list of x's dimensions with the rational value of y.
            let ySimp = Simplify y      // take any possible opportunity to boil this down to a number.
            match ySimp with
            | Amount(PhysicalQuantity(Rational(ynum,yden),ySimpConcept)) ->
                if ySimpConcept <> Dimensionless then
                    failwith "IMPOSSIBLE - y concept changed after simplification."
                else
                    ExponentiateConcept xConcept ynum yden
            | _ -> failwith "Cannot raise a dimensional expression to a non-rational power."
    else
        failwith "Cannot raise an expression to a dimensional power."

and ReciprocalConcept arg =
    match ExpressionConcept arg with
    | Zero -> Zero
    | Concept(dimlist) -> 
        // Take the reciprocal by negating each rational number in the list of dimensional exponents.
        Concept(List.map (fun (numer,denom) -> MakeRationalPair (-numer) denom) dimlist)

