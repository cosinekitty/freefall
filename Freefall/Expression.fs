// Expression.fs  -  Don Cross  -  http://cosinekitty.com
// Symbolic algebra/physics helper.

module Freefall.Expr
open Checked
open System.Collections.Generic
open System.Numerics
open Scanner

exception FreefallRuntimeException of string
exception UnexpectedEndException of option<string>       // Some(filename) or None

let MinConvertibleBigInteger = new BigInteger(System.Int32.MinValue + 1)        // tricky: avoid two's complement bug: -(-2147483648) = -2147483648!  Freaky!
let MaxConvertibleBigInteger = new BigInteger(System.Int32.MaxValue)
let CanConvertBigInteger big = (big >= MinConvertibleBigInteger) && (big <= MaxConvertibleBigInteger) 

type Number = 
    | Rational of BigInteger * BigInteger
    | Real of float
    | Complex of Complex

let IsNumberEqualToInteger n x =
    match x with
    | Rational(numer,denom) -> (numer = n) && (denom.IsOne)      // assumes rational was created using MakeRational to normalize
    | Real re -> re = (float n)
    | Complex(c) -> (c.Imaginary = 0.0) && (c.Real = (float n))

let IsNumberZero x =        // could use (IsNumberEqualToInteger 0 x), but this is a little more efficient
    match x with
    | Rational(numer,denom) -> numer.IsZero
    | Real re -> re = 0.0
    | Complex(c) -> (c.Imaginary = 0.0) && (c.Real = 0.0)

let NegateNumber number =
    match number with
    | Rational(numer,denom) -> Rational(-numer,denom)
    | Real(x) -> Real(-x)
    | Complex(c) -> Complex(-c)

let rec GreatestCommonDivisor (a:BigInteger) (b:BigInteger) =         // caller must ensure that a and b are both non-negative
    if b.IsZero then
        if a.IsZero then BigInteger.One else a
    else
        GreatestCommonDivisor b (a%b)

let rec MakeRationalPair (numer:BigInteger) (denom:BigInteger) =
    if denom.IsZero then 
        raise (FreefallRuntimeException("Rational number cannot have zero denominator."))
    elif numer.IsZero then
        (BigInteger.Zero, BigInteger.One)
    elif denom < BigInteger.Zero then
        MakeRationalPair (-numer) (-denom)
    else
        let gcd = GreatestCommonDivisor (BigInteger.Abs(numer)) denom
        (numer/gcd, denom/gcd)

let MakeRational (numer:BigInteger) (denom:BigInteger) =
    Rational(MakeRationalPair numer denom)

let AddExponentLists (alist:list<BigInteger * BigInteger>) (blist:list<BigInteger * BigInteger>) =
    List.map2 (fun (a,b) (c,d) -> MakeRationalPair (a*d + c*b) (b*d)) alist blist

let SubtractExponentLists (alist:list<BigInteger * BigInteger>) (blist:list<BigInteger * BigInteger>) =
    List.map2 (fun (a,b) (c,d) -> MakeRationalPair (a*d - c*b) (b*d)) alist blist        

let NegateExponentList (clist:list<BigInteger * BigInteger>) =
    List.map (fun (a,b) -> MakeRationalPair (-a) b) clist

let rec AddNumbers anum bnum =
    match (anum, bnum) with
    | (Rational(a,b), Rational(c,d)) -> MakeRational (a*d + b*c) (b*d)
    | (Rational(a,b), Real(r)) -> Real(r + (float a)/(float b))
    | (Rational(a,b), Complex(c)) -> Complex(new Complex(c.Real + (float a)/(float b), c.Imaginary))
    | (Real(_), Rational(_,_)) -> AddNumbers bnum anum
    | (Real(x), Real(y)) -> Real(x + y)
    | (Real(r), Complex(c)) -> Complex(new Complex(r + c.Real, c.Imaginary))
    | (Complex(_), Rational(_,_)) -> AddNumbers bnum anum
    | (Complex(_), Real(_)) -> AddNumbers bnum anum
    | (Complex(c), Complex(d)) -> Complex(c+d)

let rec MultiplyNumbers anum bnum =
    match (anum, bnum) with
    | (Rational(a,b), Rational(c,d)) -> MakeRational (a*c) (b*d)
    | (Rational(a,b), Real(r)) -> Real(r * (float a)/(float b))
    | (Rational(a,b), Complex(c)) -> 
        let ratio = (float a) / (float b)
        Complex(new Complex(ratio*c.Real, ratio*c.Imaginary))
    | (Real(_), Rational(_,_)) -> MultiplyNumbers bnum anum
    | (Real(x), Real(y)) -> Real(x * y)
    | (Real(r), Complex(c)) -> Complex(new Complex(r*c.Real, r*c.Imaginary))
    | (Complex(_), Rational(_,_)) -> MultiplyNumbers bnum anum
    | (Complex(_), Real(_)) -> MultiplyNumbers bnum anum
    | (Complex(c), Complex(d)) -> Complex(c*d)

let PowerNumbers anum bnum =
    // Get this nasty special case out of the way first.
    if (IsNumberZero anum) && (IsNumberZero bnum) then
        raise (FreefallRuntimeException "Cannot evaluate 0^0.")

    match (anum, bnum) with
    | (Rational(an,ad), Rational(bn,bd)) ->
        if bd.IsOne && (CanConvertBigInteger bn) then
            // We can raise any rational to any 32-bit integer power with an exact rational result.
            // BigInteger supports non-negative 32-bit signed exponents only.
            // Raising to any negative power just means we need to take a reciprocal when we are done.
            // (an/ad)^b = (an)^b / (ad)^b          if   b = 0, 1, 2, ...
            // (an/ad)^b = (ad)^(-b) / (an)^(-b)    if b = -1, -2, ...
            let intpow = int bn
            if intpow < 0 then
                Rational(BigInteger.Pow(ad, -intpow), BigInteger.Pow(an, -intpow))
            else
                Rational(BigInteger.Pow(an, intpow), BigInteger.Pow(ad, intpow))                
        else
            // Any nonrational (or very large) power requires numerical approximation.
            let a = (float an) / (float ad)
            let b = (float bn) / (float bd)
            Real(System.Math.Pow(a,b))
    | (Rational(an,ad), Real(b)) ->
        let a = (float an) / (float ad)
        Real(System.Math.Pow(a,b))
    | (Rational(an,ad), Complex(b)) ->
        let a = new Complex((float an) / (float ad), 0.0)
        Complex(Complex.Pow(a,b))
    | (Real(a), Rational(bn,bd)) ->
        let b = (float bn) / (float bd)
        Real(System.Math.Pow(a,b))
    | (Real(a), Real(b)) ->
        Real(System.Math.Pow(a,b))
    | (Real(a), Complex(b)) ->
        Complex(Complex.Pow(new Complex(a,0.0), b))
    | (Complex(a), Rational(bn,bd)) ->
        let b = new Complex((float bn) / (float bd), 0.0)
        Complex(Complex.Pow(a,b))
    | (Complex(a), Real(b)) ->
        Complex(Complex.Pow(a, new Complex(b, 0.0)))
    | (Complex(a), Complex(b)) ->
        Complex(Complex.Pow(a,b))

type PhysicalConcept = 
    | Zero                              // a special case because 0 is considered compatible with any concept: 0*meter = 0*second. Weird but necessary.
    | Concept of list<BigInteger * BigInteger>    // list must have NumDimensions elements, each representing a rational number for the exponent of that dimension

// Functions to help build concepts from other concepts...

let AddConcepts a b =
    match (a,b) with
    | (_,Zero) -> a
    | (Zero,_) -> b
    | (Concept(alist),Concept(blist)) ->
        if alist = blist then
            a
        else
            raise (FreefallRuntimeException("Cannot add incompatible concepts."))

let MultiplyConcepts a b =
    match (a,b) with
    | (_,Zero) -> Zero
    | (Zero,_) -> Zero
    | (Concept(alist),Concept(blist)) -> Concept(AddExponentLists alist blist)

let DivideConcepts a b =
    match (a,b) with
    | (_,Zero) -> raise (FreefallRuntimeException("Cannot divide concept by 0."))
    | (Zero,_) -> Zero
    | (Concept(alist),Concept(blist)) -> Concept(SubtractExponentLists alist blist)

let InvertConcept c =
    match c with
    | Zero -> raise (FreefallRuntimeException("Cannot take reciprocal of 0 concept."))
    | Concept(clist) -> Concept(NegateExponentList clist)

let ExponentiateConcept xconcept ynum yden =
    match xconcept with
    | Concept(xlist) -> Concept(List.map (fun (xnum,xden) -> MakeRationalPair (xnum*ynum) (xden*yden)) xlist)
    | Zero ->
        if ynum.IsZero then
            raise (FreefallRuntimeException("Cannot raise 0 to the 0 power."))
        elif ynum < BigInteger.Zero then
            raise (FreefallRuntimeException("Cannot raise 0 to a negative power."))
        else
            Zero    // 0^x = 0 for all positive rational x

let R0 = (BigInteger.Zero, BigInteger.One)      // Represents the integer 0 = 0/1
let R1 = (BigInteger.One,  BigInteger.One)      // Represents the integer 1 = 1/1

// A concept to represent any dimensionless quantity...
let Dimensionless = Concept[R0; R0; R0; R0; R0; R0; R0]

let RaiseConceptToNumberPower concept number =
    match number with
    | Rational(a,b) -> 
        ExponentiateConcept concept a b
    | Real(x) ->
        if concept = Zero then
            if x > 0.0 then
                Zero
            else
                failwith "Cannot raise 0 concept to a non-positive power."
        elif concept = Dimensionless then
            Dimensionless
        else
            failwith "Cannot raise dimensional concept to non-rational power."
    | Complex(_) ->
        if concept = Zero then
            failwith "Cannot raise 0 concept to a complex power."
        elif concept = Dimensionless then
            Dimensionless
        else
            failwith "Cannot raise dimensional concept to complex power."

// Base concepts...

type BaseConceptEntry = {
    ConceptName: string;
    BaseUnitName: string;
    ConceptValue: PhysicalConcept;
}

let BaseConcepts = [
    {ConceptName="mass";            BaseUnitName="kilogram";    ConceptValue=Concept[R1; R0; R0; R0; R0; R0; R0]};
    {ConceptName="distance";        BaseUnitName="meter";       ConceptValue=Concept[R0; R1; R0; R0; R0; R0; R0]};
    {ConceptName="time";            BaseUnitName="second";      ConceptValue=Concept[R0; R0; R1; R0; R0; R0; R0]};
    {ConceptName="temperature";     BaseUnitName="kelvin";      ConceptValue=Concept[R0; R0; R0; R1; R0; R0; R0]};
    {ConceptName="substance";       BaseUnitName="mole";        ConceptValue=Concept[R0; R0; R0; R0; R1; R0; R0]};
    {ConceptName="current";         BaseUnitName="ampere";      ConceptValue=Concept[R0; R0; R0; R0; R0; R1; R0]};
    {ConceptName="luminosity";      BaseUnitName="candela";     ConceptValue=Concept[R0; R0; R0; R0; R0; R0; R1]};
]

let NumDimensions = BaseConcepts.Length
let BaseUnitNames = List.map (fun {BaseUnitName=name} -> name) BaseConcepts
let ConceptNames  = List.map (fun {ConceptName=name}  -> name) BaseConcepts

// A physical quantity is a numeric scalar attached to a physical concept.
type PhysicalQuantity = PhysicalQuantity of Number * PhysicalConcept

let Number0 = Rational(R0)
let Number1 = Rational(R1)

let IntegerNumber (n:int) = Rational(new BigInteger(n), BigInteger.One)

let ZeroQuantity = PhysicalQuantity(Number0, Zero)
let Unity = PhysicalQuantity(Number1, Dimensionless)

let IntegerQuantity n = 
    if n = 0 then
        ZeroQuantity    // We want concept to be Zero, not Dimensionless, in this special case
    else
        PhysicalQuantity((IntegerNumber n), Dimensionless)

let NegativeOneQuantity = IntegerQuantity -1

let InvertNumber number =        // calculate the numeric reciprocal
    if IsNumberZero number then
        raise (FreefallRuntimeException("Cannot take reciprocal of 0."))
    else
        match number with
        | Rational(a,b) -> Rational(b,a)
        | Real x -> Real(1.0 / x)
        | Complex(c) -> Complex(Complex.Reciprocal(c))

let InvertQuantity (PhysicalQuantity(number,concept)) =
    PhysicalQuantity((InvertNumber number),(InvertConcept concept))

let NegateQuantity (PhysicalQuantity(number,concept)) =
    PhysicalQuantity((NegateNumber number),concept)

let rec AddQuantityList qlist =
    match qlist with
    | [] -> ZeroQuantity
    | PhysicalQuantity(fnumber,fconcept) :: rest -> 
        let (PhysicalQuantity(rnumber,rconcept)) = AddQuantityList rest
        PhysicalQuantity((AddNumbers fnumber rnumber), (AddConcepts fconcept rconcept))

let rec MultiplyQuantityList qlist =
    match qlist with
    | [] -> Unity
    | PhysicalQuantity(fnumber,fconcept) :: rest ->
        let (PhysicalQuantity(rnumber,rconcept)) = MultiplyQuantityList rest
        PhysicalQuantity((MultiplyNumbers fnumber rnumber), (MultiplyConcepts fconcept rconcept))

type Expression =
    | Amount of PhysicalQuantity
    | Solitaire of Token                            // a symbol representing a unit, concept, named expression, or variable.
    | Functor of Token * list<Expression>           // (func-or-macro-name, [args...])
    | Sum of list<Expression>
    | Product of list<Expression>
    | Power of Expression * Expression
    | Equals of Expression * Expression
    | NumExprRef of Token * int                     // a reference to a prior expression indexed by automatic integer counter
    | PrevExprRef of Token                          // a reference to the previous expression
    | Del of Token * int      // calculus 'd' or 'del' operator applied to a variable, n times, where n = 1, 2, ...

let PrimaryToken expr =     // FIXFIXFIX - rework Expression so that this function can always return a primary token
    match expr with
    | Amount(_) -> None
    | Solitaire(t) -> Some(t)
    | Functor(t,_) -> Some(t)
    | Sum(_) -> None
    | Product(_) -> None
    | Power(_) -> None
    | Equals(_) -> None
    | NumExprRef(t,_) -> Some(t)
    | PrevExprRef(t) -> Some(t)
    | Del(t,_) -> Some(t)

let FailLingeringMacro token =
    SyntaxError token "Internal error - lingering macro after macro expansion. Should not be possible."

exception ExpressionException of Expression * string

let ExpressionError expr message =
    raise (ExpressionException(expr,message))
 
let ZeroAmount = Amount(ZeroQuantity)
let UnityAmount = Amount(Unity)
let IntegerAmount (n:int) = Amount(IntegerQuantity n)
let NegativeOneAmount = IntegerAmount(-1)

let IsZeroQuantity (PhysicalQuantity(number,concept)) =
    (concept = Zero) || (IsNumberZero number)

let IsUnityQuantity (PhysicalQuantity(number,concept)) =
    (concept = Dimensionless) && (IsNumberEqualToInteger BigInteger.One number)

let IsNegativeUnityQuantity (PhysicalQuantity(number,concept)) =
    (concept = Dimensionless) && (IsNumberEqualToInteger BigInteger.MinusOne number)

let IsZeroExpression expr =
    match expr with
    | Amount(quantity) -> IsZeroQuantity quantity
    | _ -> false

let IsUnityExpression expr =
    match expr with
    | Amount(quantity) -> IsUnityQuantity quantity
    | _ -> false

let IsNegativeUnityExpression expr =
    match expr with
    | Amount(quantity) -> IsNegativeUnityQuantity quantity
    | _ -> false

let IsExpressionEqualToInteger expr n =
    if n = 0 then
        IsZeroExpression expr       // must be handled as a special case
    else
        match expr with
        | Amount(PhysicalQuantity(number,concept)) -> 
            (concept = Dimensionless) && (IsNumberEqualToInteger (new BigInteger(n)) number)
        | _ -> false

let MakeNegative expr = 
    match expr with
    | Amount(quantity) -> Amount(NegateQuantity quantity)
    | Product (Amount(quantity) :: rfactors) -> 
        let negQuantity = NegateQuantity quantity
        if IsUnityQuantity negQuantity then
            match rfactors with
            | [] -> UnityAmount
            | [single] -> single
            | _ -> Product(rfactors)
        elif IsZeroQuantity negQuantity then
            ZeroAmount
        else
            Product (Amount(negQuantity) :: rfactors)
    | Product factors -> Product (NegativeOneAmount :: factors)
    | _ -> Product[NegativeOneAmount; expr]

let MakeReciprocal expr = 
    match expr with
    | Amount(PhysicalQuantity(Rational(_,_),concept) as quantity) when concept = Dimensionless -> 
        Amount(InvertQuantity quantity)
    | Power(a,b) -> 
        Power(a, MakeNegative b)
    | _ -> 
        Power(expr, NegativeOneAmount)

let Divide a b = Product[a; MakeReciprocal b]

let IsConceptDimensionless concept =
    (concept = Zero) || (concept = Dimensionless)

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

let RealString (r:float) =
    let t = r.ToString().Replace("E", "e")
    if not (t.Contains("e")) && not (t.Contains(".")) then
        t + ".0"        // force re-parsing as float
    else
        t

let FormatNumber x =
    match x with
    | Rational(numer,denom) ->
        if denom.IsZero then
            raise (FreefallRuntimeException("Rational number had zero denominator."))
        elif denom.IsOne then
            numer.ToString()
        else
            numer.ToString() + "/" + denom.ToString()
    | Real re -> 
        RealString re
    | Complex(c) -> 
        // (-3.4-5.6i)
        // (-3.4+5.6i)
        let rtext = RealString c.Real
        let itext = 
            if c.Imaginary >= 0.0 then
                "+" + (RealString c.Imaginary)
            else
                RealString c.Imaginary
        "(" + rtext + itext + "i)"

let NumberPrecedence x =
    match x with
    | Rational(numer,denom) ->
        if denom.IsOne then
            if numer.Sign < 0 then
                Precedence_Neg
            else
                Precedence_Atom
        else
            Precedence_Mul
    | Real(x) ->
        if x < 0.0 then
            Precedence_Neg
        else
            Precedence_Atom
    | Complex(c) -> Precedence_Atom    // complex numbers are always rendered inside parentheses

let FormatDimension name (numer:BigInteger,denom:BigInteger) =
    if numer.IsZero then
        ""      // this dimension does not contribute to formatting, e.g. meter^0
    elif numer.IsOne && denom.IsOne then
        name    // meter^(1/1) is written as "meter"
    elif denom.IsOne then
        if numer < BigInteger.Zero then
            name + "^(" + numer.ToString() + ")"        // meter^(-1)
        else
            name + "^" + numer.ToString()               // meter^3
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

let DimensionsPrecedence concept =
    // Cheat: convert to string, then inspect the string.
    let text = FormatDimensions BaseUnitNames concept
    if text.Contains("*") then
        Precedence_Mul
    elif text.Contains("^") then
        Precedence_Pow
    else
        Precedence_Atom

let FormatConcept concept = 
    let text = FormatDimensions ConceptNames concept
    if text = "" then
        "1"     // special case: avoid ""
    else
        text

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

let QuantityPrecedence (PhysicalQuantity(scalar,concept)) =
    if IsNumberZero scalar then
        Precedence_Atom
    else
        let scalarPrec = NumberPrecedence scalar
        if concept = Dimensionless then
            scalarPrec
        elif concept = Zero then
            Precedence_Atom
        else
            let conceptPrec = DimensionsPrecedence concept
            if Precedence_Mul < scalarPrec && Precedence_Mul < conceptPrec then
                Precedence_Mul
            elif scalarPrec < conceptPrec then
                scalarPrec
            else
                conceptPrec

//-----------------------------------------------------------------------------------------------------
// The "raw" expression formatter displays an expression showing its actual representation.

let rec FormatExpressionRaw expr =
    match expr with
    | Amount quantity -> FormatQuantity quantity
    | Solitaire(token) -> token.Text
    | Functor(funcName, argList) -> funcName.Text + "(" + FormatExprListRaw argList + ")"
    | Sum terms -> "sum(" + FormatExprListRaw terms + ")"
    | Product factors -> "prod(" + FormatExprListRaw factors + ")"
    | Power(a,b) -> "pow(" + FormatExpressionRaw a + "," + FormatExpressionRaw b + ")"
    | Equals(a,b) -> FormatExpressionRaw a + " = " + FormatExpressionRaw b
    | NumExprRef(_,i) -> "#" + i.ToString()
    | PrevExprRef(_) -> "#"
    | Del(token,order) -> (String.replicate order "@") + token.Text

and FormatExprListRaw exprlist =
    match exprlist with
    | [] -> ""
    | [single] -> FormatExpressionRaw single
    | first :: rest -> FormatExpressionRaw first + "," + FormatExprListRaw rest

//-----------------------------------------------------------------------------------------------------
// The normal expression formatter displays a more conventional notation.

let rec FormatExpression expr =
    FormatExpressionPrec expr Precedence_Or

and ExpressionPrecedence expr =
    match expr with
    | Amount(quantity) -> QuantityPrecedence quantity
    | Solitaire(_) -> Precedence_Atom
    | Functor(_,_) -> Precedence_Atom
    | Sum(terms) -> 
        match terms with
        | [] -> Precedence_Atom                        // formatted as "0"
        | [single] -> ExpressionPrecedence single      // single is rendered by itself
        | _ -> Precedence_Add                          // a+b+c+...
    | Product(factors) -> 
        match factors with
        | [] -> Precedence_Atom                         // formatted as "1"
        | [single] -> ExpressionPrecedence single       // single is rendered by itself
        | _ -> Precedence_Mul                           // a*b*c*...
    | Power(_,_) -> Precedence_Pow
    | Equals(_,_) -> Precedence_Rel
    | NumExprRef(_,_) -> Precedence_Atom
    | PrevExprRef(_) -> Precedence_Atom
    | Del(_,_) -> Precedence_Atom

and FormatExpressionPrec expr parentPrecedence =
    let innerText =
        match expr with
        | Amount quantity -> FormatQuantity quantity
        | Solitaire(token) -> token.Text
        | Functor(funcName, argList) -> funcName.Text + "(" + FormatExprList argList + ")"
        | Sum terms ->
            match terms with
            | [] -> "0"
            | [single] -> FormatExpression single
            | first :: rest -> FormatExpressionPrec first Precedence_Add + JoinRemainingTerms rest
        | Product factors ->
            match factors with
            | [] -> "1"
            | [single] -> FormatExpression single
            | Amount(quantity) :: rest when quantity = NegativeOneQuantity -> "-" + (FormatExpressionPrec (Product rest) Precedence_Neg)
            | first :: rest -> FormatExpressionPrec first Precedence_Mul + JoinRemainingFactors rest
        | Power(a,b) -> FormatExpressionPrec a Precedence_Pow + "^" + FormatExpressionPrec b Precedence_Pow
        | Equals(a,b) -> FormatExpressionPrec a Precedence_Rel + " = " + FormatExpressionPrec b Precedence_Rel
        | NumExprRef(_,i) -> "#" + i.ToString()
        | PrevExprRef(_) -> "#"
        | Del(token,order) -> (String.replicate order "@") + token.Text

    if parentPrecedence < ExpressionPrecedence expr then
        innerText
    else
        "(" + innerText + ")"

and FormatExprList exprlist =
    match exprlist with
    | [] -> ""
    | [single] -> FormatExpression single
    | first :: rest -> FormatExpression first + "," + FormatExprList rest

and JoinRemainingTerms exprlist =
    // sum(a, b, c) -->  JoinRemainingTerms[b;c]
    // If b is Product(a,x) where a is negative, we want to show "- abs(a)*x".
    match exprlist with
    | [] -> ""
    | first :: rest -> RemainingTermText first + JoinRemainingTerms rest

and RemainingTermText expr =
    let rtext = FormatExpressionPrec expr Precedence_Add
    if rtext.StartsWith("-") then       // FIXFIXFIX : seems risky - what about -1^2?
        rtext
    else
        "+" + rtext

and JoinRemainingFactors exprlist =
    match exprlist with 
    | [] -> ""
    | first :: rest -> RemainingFactorText first + JoinRemainingFactors rest

and RemainingFactorText expr =
    match expr with
    | Power(x, Amount(PhysicalQuantity(Rational(a,b),concept))) when (concept = Dimensionless) && (a.Sign < 0) -> 
        let abs_a_text = BigInteger.Negate(a).ToString();
        let xtext = FormatExpressionPrec x Precedence_Mul
        if b.IsOne then
            if abs_a_text = "1" then
                "/" + xtext
            else
                "/" + xtext + "^" + abs_a_text
        else
            "/" + xtext + "^(" + abs_a_text + "/" + b.ToString() + ")"
    | Amount(PhysicalQuantity(Rational(a,b),concept)) when (concept = Dimensionless) && a.IsOne ->
        // Multiplying by 1/b is the same as dividing by b, and is more pleasant to read.
        if b.IsOne then
            ""
        else
            "/" + b.ToString()
    | _ -> 
        "*" + FormatExpressionPrec expr Precedence_Mul
    
//-----------------------------------------------------------------------------------------------------
//  Context provides mutable state needed to execute a series of Freefall statements.
//  Some statements will define units and types of variables that are subsequently referenced.
//  Executed statements will accumulate references that can be used by later statements.
//  Some statements "forget" statement references on purpose. 

type Macro = {
    Expander: Token -> list<Expression> -> Expression;
}

type DerivativeKind = Differential | Derivative

type IFunctionHandler =
    abstract member EvalRange : Token -> list<NumericRange> -> NumericRange
    abstract member EvalConcept : Context -> Token -> list<Expression> -> PhysicalConcept
    abstract member EvalNumeric : Context -> Token -> list<PhysicalQuantity> -> PhysicalQuantity
    abstract member SimplifyStep : Context -> Token -> list<Expression> -> Expression
    abstract member Differential : DerivativeKind -> Context -> list<string> -> Token -> list<Expression> -> Expression
    abstract member DistributeAcrossEquation : Context -> Token -> list<Expression> -> list<Expression> -> Expression
    abstract member LatexName : string

and SymbolEntry =
    | VariableEntry of NumericRange * PhysicalConcept
    | ConceptEntry of PhysicalConcept
    | UnitEntry of PhysicalQuantity
    | AssignmentEntry of Expression         // the value of a named expression is the expression itself
    | MacroEntry of Macro
    | FunctionEntry of IFunctionHandler

and Context = {
    SymbolTable: Dictionary<string,SymbolEntry>;
    NumberedExpressionList: ResizeArray<Expression>;
    AssignmentHook: option<string> -> int -> Expression -> unit;            // AssignmentHook targetName refIndex assignedExpr
    ProbeHook: Context -> Expression -> NumericRange -> PhysicalConcept -> unit;
    SaveToFile: Context -> string -> unit;
}

let AppendNumberedExpression {NumberedExpressionList=numExprList;} expr =
    numExprList.Add(expr)

let FindNumberedExpression {NumberedExpressionList=numExprList;} token index =
    if (index >= 1) && (index <= numExprList.Count) then
        numExprList.[index-1]
    else
        SyntaxError token (sprintf "Invalid expression index: expected 1..%d" numExprList.Count)

let FindPreviousExpression {NumberedExpressionList=numExprList;} token =
    if numExprList.Count > 0 then
        numExprList.[numExprList.Count - 1]
    else
        SyntaxError token "Cannot refer to previous expression because expression list is empty."

let DefineIntrinsicSymbol {SymbolTable=symtable;} symbol entry =
    if symtable.ContainsKey(symbol) then
        failwith (sprintf "Symbol '%s' is already defined" symbol)
    else
        symtable.Add(symbol, entry)

let DefineSymbol {SymbolTable=symtable;} ({Text=symbol; Kind=kind} as symtoken) symentry =
    if kind <> TokenKind.Identifier then
        SyntaxError symtoken "Expected identifier for symbol name"
    elif (symtable.ContainsKey(symbol)) then
        SyntaxError symtoken "Symbol is already defined"
    else
        symtable.Add(symbol, symentry)

let DeletedNumberedExpressions {NumberedExpressionList=numlist} =
    (numlist.Clear())

let DeleteNamedExpression {SymbolTable=symtable;} ({Text=symbol; Kind=kind} as symtoken) =
    if kind <> TokenKind.Identifier then
        SyntaxError symtoken "Expected identifier for expression name"
    elif not (symtable.ContainsKey(symbol)) then
        SyntaxError symtoken "Undefined symbol"
    else
        match symtable.[symbol] with
        | AssignmentEntry(_) -> (symtable.Remove(symbol)) |> ignore
        | _ -> SyntaxError symtoken "Symbol is not an expression name"

let FindSymbolEntry {SymbolTable=symtable;} ({Text=symbol; Kind=kind} as symtoken) =
    if kind <> TokenKind.Identifier then
        SyntaxError symtoken "Expected symbol identifier"
    elif not (symtable.ContainsKey(symbol)) then
        SyntaxError symtoken "Undefined symbol"
    else
        symtable.[symbol]

//-----------------------------------------------------------------------------------------------------
// Identity tester : determines if two expressions have equivalent values.
// For example, sum(a,b,c) looks different from sum(b,c,a), but are identical.

let IsZeroNumberConceptPair number concept =
    (concept = Zero) || (IsNumberZero number)

let IsDeterministicFunctionName funcName =
    true        // FIXFIXFIX - adjust this in case we have something like random() in the future (I hope not!)

let rec AreIdenticalNumbers a b =
    match (a,b) with
    | (Rational(anum,aden),Rational(bnum,bden)) -> anum*bden = bnum*aden
    | (Rational(anum,aden),Real(br)) -> (float anum) = br*(float aden)
    | (Rational(anum,aden),Complex(b)) -> (b.Imaginary = 0.0) && (AreIdenticalNumbers a (Real(b.Real)))
    | (Real(ar),Rational(_,_)) -> AreIdenticalNumbers b a
    | (Real(ar),Real(br)) -> ar = br
    | (Real(ar),Complex(b)) -> (b.Imaginary = 0.0) && (ar = b.Real)
    | (Complex(_),Rational(_,_)) -> AreIdenticalNumbers b a
    | (Complex(_),Real(_)) -> AreIdenticalNumbers b a
    | (Complex(a),Complex(b)) -> a = b

let rec AreIdentical context a b =
    match (a,b) with
    | (Amount(PhysicalQuantity(aNumber,aConcept)), Amount(PhysicalQuantity(bNumber,bConcept))) -> 
        AreIdenticalQuantities aNumber aConcept bNumber bConcept
    | (Amount(_), _) -> false
    | (_, Amount(_)) -> false
    | (Solitaire(aToken), Solitaire(bToken)) -> aToken.Text = bToken.Text
    | (Solitaire(_), _) -> false
    | (_, Solitaire(_)) -> false
    | (Functor(funcName1,argList1), Functor(funcName2,argList2)) -> 
        (funcName1.Text = funcName2.Text) &&
        (IsDeterministicFunctionName funcName1.Text) &&
        (AreIdenticalExprLists context argList1 argList2)
    | (Functor(_), _) -> false
    | (_, Functor(_)) -> false
    | (Sum(aterms),Sum(bterms)) -> ArePermutedLists context aterms bterms
    | (Sum(_), _) -> false
    | (_, Sum(_)) -> false
    | (Product(afactors),Product(bfactors)) -> ArePermutedLists context afactors bfactors
    | (Product(_), _) -> false
    | (Power(abase,aexp),Power(bbase,bexp)) -> (AreIdentical context abase bbase) && (AreIdentical context aexp bexp)
    | (Power(_,_), _) -> false
    | (_, Power(_,_)) -> false
    | (NumExprRef(t,_), _) -> FailLingeringMacro t
    | (_, NumExprRef(t,_)) -> FailLingeringMacro t
    | (PrevExprRef(t), _)  -> FailLingeringMacro t
    | (_, PrevExprRef(t))  -> FailLingeringMacro t
    | (Del(var1,order1),Del(var2,order2)) -> (var1.Text = var2.Text) && (order1 = order2)
    | (Del(_,_),_) -> false
    | (_,Del(_,_)) -> false
    | (Equals(aleft,aright),Equals(bleft,bright)) -> 
        ((AreIdentical context aleft bleft)  && (AreIdentical context aright bright)) ||
        ((AreIdentical context aleft bright) && (AreIdentical context aright bleft))
    | (Equals(_,_), (_)) -> false

and AreIdenticalExprLists context list1 list2 =
    if list1.Length <> list2.Length then
        false
    else
        match list1, list2 with
        | [], [] -> 
            true

        | f1::r1, f2::r2 -> 
            (AreIdentical context f1 f2) && (AreIdenticalExprLists context r1 r2)
        
        | _ ->
            false

and AreIdenticalQuantities aNumber aConcept bNumber bConcept =
    let aIsZero = IsZeroNumberConceptPair aNumber aConcept
    let bIsZero = IsZeroNumberConceptPair bNumber bConcept
    if aIsZero || bIsZero then
        // If either is zero, then then both must be zero to match.
        aIsZero = bIsZero
    else
        // Neither is zero, so we must match numbers and concepts both.
        (aConcept = bConcept) && (AreIdenticalNumbers aNumber bNumber)

and ArePermutedLists context alist blist =
    if alist.Length <> blist.Length then
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
                match FindIdenticalInList context afirst blist with
                | None -> false
                | Some(bshorter) -> ArePermutedLists context arest bshorter
        
// The following function searches for an element of list that
// is mathematically identical to expr.  If found, returns Some(shorter)
// where shorter is list with the identical element removed.
// Otherwise, returns None.
and FindIdenticalInList context expr elist =
    match elist with
    | [] -> None
    | first::rest -> 
        if AreIdentical context expr first then
            Some(rest)
        else
            match FindIdenticalInList context expr rest with
            | None -> None
            | Some(shorter) -> Some(first :: shorter)

//-----------------------------------------------------------------------------------------------------
// Expression simplifier.

let QuantityPairSum (PhysicalQuantity(aNumber,aConcept)) (PhysicalQuantity(bNumber,bConcept)) =
    PhysicalQuantity(AddNumbers aNumber bNumber, AddConcepts aConcept bConcept)

let AddQuantities a b =
    Amount(QuantityPairSum a b)

let MultiplyQuantities (PhysicalQuantity(aNumber,aConcept)) (PhysicalQuantity(bNumber,bConcept)) =
    Amount(PhysicalQuantity(MultiplyNumbers aNumber bNumber, MultiplyConcepts aConcept bConcept))

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
       
//-----------------------------------------------------------------------------------------------
// Advanced pattern-matching simplifier rules.

type TermPattern = TermPattern of PhysicalQuantity * Expression        // represents c*x where c is numeric and x may or may not be constant

let rec MakeTermPattern context term =
    // Transform a term expression into the form c*x
    match term with
    | Amount(x) -> TermPattern(x, UnityAmount)     // coeff ==> ceoff*1
    | Solitaire(token) -> 
        match FindSymbolEntry context token with
        | VariableEntry(_,_) -> TermPattern(Unity, term)      // var ==> 1*var
        | ConceptEntry(_) -> SyntaxError token "Cannot use concept in sum()"
        | UnitEntry(amount) -> TermPattern(amount, UnityAmount)            // unit ==> unit*1
        | AssignmentEntry(_) -> FailLingeringMacro token
        | MacroEntry(_) -> FailLingeringMacro token
        | FunctionEntry(fe) -> SyntaxError token "Cannot use function name as a variable."
    | Functor(funcName, argList) -> 
        TermPattern(Unity, term)     // func(_) => 1*func(_)
    | Sum terms ->
        // This shouldn't happen because flattener should have already folded this into the higher sum.
        failwith "Flattener failure: found sum() term inside a sum()."
    | Product factors ->
        match factors with
        | [] -> TermPattern(Unity, UnityAmount)       // prod() ==> 1*1
        | [arg] -> MakeTermPattern context arg
        | first :: rest ->
            match first with
            | Amount(quantity) -> 
                match rest with
                | [second] -> TermPattern(quantity, second)
                | _ -> TermPattern(quantity, (Product rest))
            | _ -> TermPattern(Unity, term)
    | Power(x,y) -> TermPattern(Unity, term)
    | Equals(_,_) -> ExpressionError term "Equality should not appear in a term."
    | NumExprRef(t,i) -> FailLingeringMacro t
    | PrevExprRef(t) -> FailLingeringMacro t
    | Del(token,order) -> TermPattern(Unity, term)

let UnmakeTermPattern (TermPattern(coeff,var)) =
    if (IsZeroQuantity coeff) || (IsZeroExpression var) then
        ZeroAmount
    elif IsUnityQuantity coeff then
        var
    elif IsUnityExpression var then
        Amount(coeff)
    else
        Product[Amount(coeff); var]

let rec FindMatchingTermPattern context (TermPattern(c1,x1) as pattern) mergedlist : option<TermPattern * list<TermPattern>> =
    match mergedlist with
    | [] -> None
    | (TermPattern(c2,x2) as first) :: rest ->
        // See if pattern matches first, meaning they are compatible to be added.
        if AreIdentical context x1 x2 then
            // Merge pattern with first and report remaining tail of list as the residue.
            Some((TermPattern((QuantityPairSum c1 c2),x1)), rest)
        else
            // If we can do a merge by skipping over first, then do so, with first becoming part of the residue.
            match FindMatchingTermPattern context pattern rest with
            | None -> None
            | Some(mpattern, residue) -> Some(mpattern, first::residue)

let rec MergeLikePatterns finder context plist =
    match plist with
    | [] -> []
    | [single] -> [single]
    | first :: rest -> 
        let mrest = MergeLikePatterns finder context rest
        // Search mrest for a pattern that can be combined to advantage with first.
        // TermPattern(C,x) + TermPattern(D,x) ==> TermPattern(C+D,x)
        match finder context first mrest with
        | None -> first :: mrest
        | Some(merged, residue) -> merged :: residue

let MergeLikeTerms context termlist =
    // Compare each term from a sum() with every later term.
    // For all that turn out to have common numeric coefficients (explicit or implicit 1),
    // total up said coefficients:
    // x + a + 3*x + b - (1/2)*x  ==>  (9/2)*x + a + b
    // The iterative nature of the simplifier will ensure that 
    // eventually constants will be merged together at the front of a product,
    // so we only need to handle that case when we see a product.
    let plist = List.map (MakeTermPattern context) termlist
    let mlist = MergeLikePatterns FindMatchingTermPattern context plist
    List.map UnmakeTermPattern mlist

//-----------------------------------------------------------------------------------------------

type FactorPattern = FactorPattern of Expression * Expression    // represents x^y

let rec MakeFactorPattern context factor =
    // Transform a factor expression into the form x^y.
    match factor with
    | Amount(_) -> FactorPattern(factor, UnityAmount)     // coeff ==> ceoff^1
    | Solitaire(token) -> 
        match FindSymbolEntry context token with
        | VariableEntry(_,_) -> FactorPattern(factor, UnityAmount)      // var ==> var^1
        | ConceptEntry(_) -> SyntaxError token "Cannot use concept in prod()"
        | UnitEntry(amount) -> FactorPattern(factor, UnityAmount)            // unit ==> unit*1
        | AssignmentEntry(_) -> FailLingeringMacro token
        | MacroEntry(_) -> FailLingeringMacro token
        | FunctionEntry(fe) -> SyntaxError token "Cannot use function name as a variable."
    | Functor(funcName, argList) -> FactorPattern(factor, UnityAmount)
    | Sum terms -> FactorPattern(factor, UnityAmount)
    | Product factors -> failwith "Flattener failure: prod() should have been marged into parent."
    | Power(x,y) -> FactorPattern(x,y)
    | Equals(_,_) -> ExpressionError factor "Equality should not appear in a factor."
    | NumExprRef(t,i) -> FailLingeringMacro t
    | PrevExprRef(t) -> FailLingeringMacro t
    | Del(token,order) -> FactorPattern(factor, UnityAmount)

let UnmakeFactorPattern (FactorPattern(x,y)) =
    if IsUnityExpression y then
        x
    elif IsZeroExpression y then
        if IsZeroExpression x then
            ExpressionError x "Cannot raise 0 to the 0 power."
        else
            UnityAmount
    else
        Power(x,y)

let rec FindMatchingFactorPattern context (FactorPattern(x1,y1) as pattern) mergedlist : option<FactorPattern * list<FactorPattern>> =
    match mergedlist with
    | [] -> None
    | (FactorPattern(x2,y2) as first) :: rest ->
        // See if pattern matches first, meaning they are compatible to be multiplied.
        if AreIdentical context x1 x2 then
            // Merge pattern with first and report remaining tail of list as the residue.
            Some(FactorPattern(x1, (Sum [y1;y2])), rest)
        else
            // If we can do a merge by skipping over first, then do so, with first becoming part of the residue.
            match FindMatchingFactorPattern context pattern rest with
            | None -> None
            | Some(mpattern, residue) -> Some(mpattern, first::residue)


let MergeLikeFactors context factorList =
    let plist = List.map (MakeFactorPattern context) factorList
    let mlist = MergeLikePatterns FindMatchingFactorPattern context plist
    List.map UnmakeFactorPattern mlist

//-----------------------------------------------------------------------------------------------

let FailNonFunction token found =
    SyntaxError token (sprintf "Expected function but found %s" found)

let FailNonVariable token found =
    SyntaxError token (sprintf "Expected variable but found %s" found)

let FindFunctionEntry context funcNameToken =
    match FindSymbolEntry context funcNameToken with
    | VariableEntry(_,_) -> FailNonFunction funcNameToken "variable"
    | ConceptEntry(_) -> FailNonFunction funcNameToken "concept"
    | UnitEntry(_) -> FailNonFunction funcNameToken "unit"
    | AssignmentEntry(_) -> FailNonFunction funcNameToken "assignment target"
    | MacroEntry(_) -> FailLingeringMacro funcNameToken
    | FunctionEntry(fe) -> fe

let FindVariableEntry context vartoken =
    match FindSymbolEntry context vartoken with
    | VariableEntry(range,concept) -> (range,concept)
    | ConceptEntry(_) -> FailNonVariable vartoken "concept"
    | UnitEntry(_) -> FailNonVariable vartoken "unit"
    | AssignmentEntry(_) -> FailNonVariable vartoken "assignment target"
    | MacroEntry(_) -> FailLingeringMacro vartoken
    | FunctionEntry(_) -> FailNonVariable vartoken "function name"

let rec SimplifyStep context expr =
    match expr with
    | Amount(_) -> expr     // already as simple as possible
    | Solitaire(_) -> expr  // already as simple as possible
    | Del(_) -> expr        // already as simple as possible

    | Functor(funcName, argList) ->
        let simpArgList = List.map (SimplifyStep context) argList
        let funcHandler = FindFunctionEntry context funcName
        funcHandler.SimplifyStep context funcName simpArgList

    | Sum(termlist) ->
        let simpargs = 
            SimplifySumArgs (List.map (SimplifyStep context) termlist) 
            |> MergeConstants AddQuantities
            |> MergeLikeTerms context

        match simpargs with
        | [] -> ZeroAmount
        | [term] -> term
        | _ -> Sum simpargs

    | Product(factorlist) ->
        let simpfactors = 
            SimplifyProductArgs (List.map (SimplifyStep context) factorlist) 
            |> MergeConstants MultiplyQuantities
            |> MergeLikeFactors context

        if List.exists IsZeroExpression simpfactors then
            ZeroAmount
        else
            match simpfactors with
            | [] -> UnityAmount
            | [factor] -> factor
            | _ -> Product simpfactors

    | Power(x,y) ->
        let sx = SimplifyStep context x
        let sy = SimplifyStep context y
        if IsZeroExpression sy then
            if IsZeroExpression sx then
                ExpressionError expr "Cannot evaluate 0^0."
            else
                UnityAmount
        elif IsUnityExpression sy then
            sx
        else
            Power(sx,sy)            

    | Equals(a,b) ->
        Equals((SimplifyStep context a), (SimplifyStep context b))

    | NumExprRef(t,_) ->
        FailLingeringMacro t

    | PrevExprRef(t) ->
        FailLingeringMacro t

// Sum(Sum(A,B,C), Sum(D,E)) = Sum(A,B,C,D,E)
// We want to "lift" all inner Sum() contents to the top level of a list.
and SimplifySumArgs simpargs =           
    match simpargs with
    | [] -> []
    | (Sum terms)::rest -> (SimplifySumArgs (RemoveZeroes terms)) @ (SimplifySumArgs rest)
    | first::rest -> SkipZero first (SimplifySumArgs rest)

and SimplifyProductArgs simpargs =           
    match simpargs with
    | [] -> []
    | (Product factors)::rest -> (SimplifyProductArgs (RemoveUnities factors)) @ (SimplifyProductArgs rest)
    | first::rest -> SkipUnity first (SimplifyProductArgs rest)

//---------------------------------------------------------------------------
// Aggressive, iterative simplifier...

let Simplify context expr =
    // Keep iterating SimplifyStep until the expression stops changing.
    let mutable prev = expr
    let mutable simp = SimplifyStep context expr
    while simp <> prev do
        prev <- simp
        simp <- SimplifyStep context simp
    simp

//-----------------------------------------------------------------------------------------------------
// Unit determination - verify that units are coherent and determine what they are.
// For example, sum(3*meter,4*second) should raise an exception because adding distance to time is illegal.
// However, sum(3*meter,4*meter) should be seen as distance units (expressible in meters).
// Returns Zero for 0*anything, which has no specific units.

let rec ExpressionConcept context expr =
    match expr with
    | Amount(PhysicalQuantity(number,concept)) -> if IsNumberZero number then Zero else concept
    | Solitaire(vartoken) -> FindSolitaireConcept context vartoken
    | Del(vartoken,_) -> FindSolitaireConcept context vartoken
    | Functor(funcName,argList) -> FindFunctorConcept context funcName argList
    | Sum(terms) -> SumConcept context terms
    | Product(factors) -> ProductConcept context factors
    | Power(a,b) -> PowerConcept context a b
    | Equals(a,b) -> EquationConcept context a b
    | NumExprRef(t,_) -> FailLingeringMacro t
    | PrevExprRef(t) -> FailLingeringMacro t

and FindSolitaireConcept context token =
    match FindSymbolEntry context token with
    | VariableEntry(_,concept) -> concept
    | ConceptEntry(concept) -> SyntaxError token "Not allowed to use concept name in an expression."
    | UnitEntry(PhysicalQuantity(_,concept)) -> concept
    | AssignmentEntry(expr) -> ExpressionConcept context expr
    | MacroEntry(_) -> SyntaxError token "Attempt to use macro name without parenthesized argument list."
    | FunctionEntry(_) -> SyntaxError token "Attempt to use function name without parenthesized argument list."

and FindFunctorConcept context funcNameToken argExprList =
    match FindSymbolEntry context funcNameToken with
    | FunctionEntry(handler) -> handler.EvalConcept context funcNameToken argExprList
    | MacroEntry(_) -> FailLingeringMacro funcNameToken
    | VariableEntry(_) -> SyntaxError funcNameToken "Attempt to use a variable as a function/macro."
    | ConceptEntry(_) -> SyntaxError funcNameToken "Attempt to use a concept as a function/macro."
    | UnitEntry(_) -> SyntaxError funcNameToken "Attempt to use a unit as a function/macro."
    | AssignmentEntry(_) -> SyntaxError funcNameToken "Attempt to use an assignment target as a function/macro."

and EquationConcept context a b =
    let aConcept = ExpressionConcept context a
    let bConcept = ExpressionConcept context b
    if aConcept = Zero then         // zero is compatible with any concept (use other concept)
        bConcept
    elif bConcept = Zero then
        aConcept
    elif aConcept <> bConcept then
        ExpressionError b (sprintf "Incompatible units: cannot equate/compare %s and %s" (FormatConcept aConcept) (FormatConcept bConcept))
    else
        aConcept

and SumConcept context terms =
    match terms with 
    | [] -> Zero        // sum() = 0, which has no specific units -- see comments above.
    | first::rest -> 
        let firstConcept = ExpressionConcept context first
        let restConcept = SumConcept context rest
        match (firstConcept, restConcept) with
        | (Zero,Zero) -> Zero                    // 0+0 = 0, which has no specific units
        | (Concept(_),Zero) -> firstConcept      // x+0 = x with specific units
        | (Zero,Concept(_)) -> restConcept       // 0+y = y
        | (Concept(f),Concept(r)) ->
            if f <> r then
                ExpressionError first (sprintf "Incompatible units: cannot add %s and %s" (FormatConcept firstConcept) (FormatConcept restConcept))
            else
                firstConcept

and ProductConcept context factors =
    match factors with 
    | [] -> Dimensionless     // product() = 1, which has dimensionless units            
    | first::rest -> MultiplyConcepts (ExpressionConcept context first) (ProductConcept context rest)

and PowerConcept context x y =
    let xConcept = ExpressionConcept context x
    let yConcept = ExpressionConcept context y
    if yConcept = Zero then
        if xConcept = Zero then
            ExpressionError y "Cannot raise 0 to 0 power."
        else
            Dimensionless
    elif yConcept = Dimensionless then
        if IsConceptDimensionless xConcept then     // 0^(-3) is an error, but is dimensionless nontheless
            // If x is dimensionless, then y may be any dimensionless expression, e.g. 2.7182818^y.
            // A dimensionless value to a dimensionless power is dimensionless.        
            Dimensionless
        else
            // If x is dimensional, then y must be rational (e.g. x^(-3/4)).
            // In this case, multiply the exponent list of x's dimensions with the rational value of y.
            // FIXFIXFIX - may need to rework 'Simplify context y' as 'EvalQuantity context y' in the following line...
            let ySimp = Simplify context y      // take any possible opportunity to boil this down to a number.
            match ySimp with
            | Amount(PhysicalQuantity(Rational(ynum,yden),ySimpConcept)) ->
                if ySimpConcept <> Dimensionless then
                    failwith "IMPOSSIBLE - y concept changed after simplification."
                else
                    ExponentiateConcept xConcept ynum yden
            | _ -> ExpressionError y "Cannot raise a dimensional expression to a non-rational power."
    else
        ExpressionError y "Cannot raise an expression to a dimensional power."

and ReciprocalConcept context arg =
    match ExpressionConcept context arg with
    | Zero -> Zero
    | Concept(dimlist) -> 
        // Take the reciprocal by negating each rational number in the list of dimensional exponents.
        Concept(List.map (fun (numer,denom) -> MakeRationalPair (-numer) denom) dimlist)

let ValidateExpressionConcept context expr =
    // Call ExpressionConcept just for the side-effect of looking for errors
    ExpressionConcept context expr |> ignore

//---------------------------------------------------------------------------------------------
// Concept evaluator.
// Although concept expressions are parsed just like any other expression,
// their contents are much more limited:
// The special case "1" is allowed to represent a dimensionless concept.
// Other than that, only concept names are allowed to appear (length, voltage, etc.)
// Concepts may be multiplied or divided, but not added or subtracted.
// Concepts may be raised to any rational power, but no other power.
// No functions or macros may appear.
// The special concept Zero may not appear, because it is not a specific concept.

let rec EvalConcept context expr =
    match expr with
    | Amount(PhysicalQuantity(number,concept)) -> 
        if (IsNumberZero number) || (concept = Zero) then 
            ExpressionError expr "Concept evaluated to 0."
        elif number <> Rational(R1) then
            ExpressionError expr (sprintf "Concept evaluated with non-unity coefficient %s" (FormatNumber number))
        else
            concept

    | Solitaire(token) -> 
        match FindSymbolEntry context token with
        | ConceptEntry(concept) -> concept
        | _ -> SyntaxError token "Expected a concept name"

    | Del(vartoken,order) ->
        SyntaxError vartoken "The @ operator is not allowed to appear in a concept expression."

    | Product(factors) -> 
        List.map (EvalConcept context) factors 
        |> List.fold (fun a b -> MultiplyConcepts a b) Dimensionless 

    | Power(a,b) -> 
        let aConcept = EvalConcept context a
        if aConcept = Zero then
            ExpressionError a "Concept 0 is not allowed in a concept expression."
        else
            let bsimp = Simplify context b
            if IsZeroExpression bsimp then
                Dimensionless        
            else
                match bsimp with
                | Amount(PhysicalQuantity(bNumber,bConcept)) ->
                    if bConcept = Dimensionless then
                        match bNumber with
                        | Rational(bnum,bden) -> ExponentiateConcept aConcept bnum bden
                        | _ -> ExpressionError b "Cannot raise concept to non-rational power."
                    else
                        ExpressionError b "Not allowed to raise to a dimensional power."
                | _ -> ExpressionError b "Concept must be raised to a dimensionless rational power."
                        
    | Functor(funcName,argList) -> SyntaxError funcName "Function or macro not allowed in concept expression."
    | Sum(terms) -> ExpressionError expr "Addition/subtraction not allowed in concept expression."
    | Equals(a,b) -> ExpressionError expr "Equality operator not allowed in concept expression."
    | NumExprRef(t,_) -> ExpressionError expr "Numbered expression reference not allowed in concept expression."
    | PrevExprRef(t) -> ExpressionError expr "Previous-expression reference not allowed in concept expression."

//-----------------------------------------------------------------------------------------------------
// Quantity evaluator - forces an expression to reduce to a physical quantity.
// Fails if the expression cannot be reduced to a quantity.

let PowerQuantities expr (PhysicalQuantity(aNumber,aConcept)) (PhysicalQuantity(bNumber,bConcept)) =
    if (IsNumberZero bNumber) || (bConcept = Zero) then
        if (IsNumberZero aNumber) || (aConcept = Zero) then
            ExpressionError expr "Cannot evaluate 0^0."
        else
            Unity
    elif bConcept <> Dimensionless then
        ExpressionError expr "Cannot raise a number to a dimensional power."
    else
        let cNumber = PowerNumbers aNumber bNumber
        let cConcept = RaiseConceptToNumberPower aConcept bNumber
        PhysicalQuantity(cNumber,cConcept)

let rec EvalQuantity context expr =
    match expr with
    | Amount(quantity) -> quantity
    | Solitaire(vartoken) -> 
        match FindSymbolEntry context vartoken with
        | UnitEntry(quantity) -> quantity
        | _ -> SyntaxError vartoken "Expected unit name."
    | Del(vartoken,order) ->
        SyntaxError vartoken "Cannot numerically evaluate infinitesimal."
    | Functor(funcName,argList) -> 
        let handler = FindFunctionEntry context funcName 
        List.map (EvalQuantity context) argList
        |> handler.EvalNumeric context funcName
    | Sum(terms) -> 
        List.map (EvalQuantity context) terms
        |> AddQuantityList
    | Product(factors) -> 
        List.map (EvalQuantity context) factors
        |> MultiplyQuantityList
    | Power(a,b) -> 
        let aval = EvalQuantity context a
        let bval = EvalQuantity context b
        PowerQuantities expr aval bval
    | Equals(a,b) -> ExpressionError expr "Equality operator not allowed in numeric expression."
    | NumExprRef(t,_) -> FailLingeringMacro t
    | PrevExprRef(t) -> FailLingeringMacro t

//-----------------------------------------------------------------------------------------------------
// Numeric range analysis - determines whether an expression will always be integer, rational, real, complex.

let QuantityNumericRange (PhysicalQuantity(number,concept)) =
    match number with
    | Rational(_,b) -> 
        if concept <> Dimensionless then
            RealRange       // We don't consider 3*meter/second an integer; it is a real number because units are an artifice.
        elif b.IsOne then 
            IntegerRange 
        else 
            RationalRange
    | Real(_) -> RealRange
    | Complex(_) -> ComplexRange   // FIXFIXFIX - consider "demoting" complex to real if imaginary part is 0? Would require great care throughout the code.

let PromoteNumericRangePair a b =
    match (a, b) with
    | (ComplexRange, _) | (_, ComplexRange) -> ComplexRange
    | (RealRange, _) | (_, RealRange) -> RealRange
    | (RationalRange, _) | (_, RationalRange) -> RationalRange
    | (IntegerRange, IntegerRange) -> IntegerRange

let rec PromoteNumericRangeList rangeList =
    match rangeList with
    | [] -> IntegerRange      // works for sums and products: sum() = 0, product() = 1, both of which are integers.
    | firstRange :: rest -> PromoteNumericRangePair firstRange (PromoteNumericRangeList rest)

let rec ExpressionNumericRange context expr =
    match expr with
    | Amount(quantity) -> QuantityNumericRange quantity
    | Solitaire(vartoken) -> 
        match FindSymbolEntry context vartoken with
        | UnitEntry(_) -> RealRange             // all physical units are inherently real-valued
        | VariableEntry(range,_) -> range
        | _ -> ExpressionError expr "Cannot determine numeric range for this kind of expression."
    | Del(vartoken,order) ->
        let range, concept = FindVariableEntry context vartoken
        match range with
        | IntegerRange -> SyntaxError vartoken "Cannot apply @ operator to an integer variable."
        | RationalRange -> SyntaxError vartoken "Cannot apply @ operator to a rational variable."
        | RealRange -> RealRange
        | ComplexRange -> ComplexRange
    | Functor(funcName,argList) -> 
        let handler = FindFunctionEntry context funcName 
        let rlist = List.map (ExpressionNumericRange context) argList
        handler.EvalRange funcName rlist
    | Sum(terms) -> 
        List.map (ExpressionNumericRange context) terms
        |> PromoteNumericRangeList
    | Product(factors) -> 
        List.map (ExpressionNumericRange context) factors
        |> PromoteNumericRangeList
    | Power(a,b) -> 
        let aRange = ExpressionNumericRange context a
        let bRange = ExpressionNumericRange context b
        match (aRange, bRange) with
        | (IntegerRange, IntegerRange) -> RationalRange     // 3 ^ (-2) = 1/9
        | (IntegerRange, RationalRange) -> RealRange        // 3 ^ (1/2) = sqrt(3)
        | (IntegerRange, RealRange) -> RealRange
        | (IntegerRange, ComplexRange) -> ComplexRange
        | (RationalRange, IntegerRange) -> RationalRange
        | (RationalRange, RationalRange) -> RealRange
        | (RationalRange, RealRange) -> RealRange
        | (RationalRange, ComplexRange) -> ComplexRange
        | (RealRange, IntegerRange) -> RealRange
        | (RealRange, RationalRange) -> RealRange
        | (RealRange, RealRange) -> RealRange
        | (RealRange, ComplexRange) -> ComplexRange
        | (ComplexRange, IntegerRange) -> ComplexRange
        | (ComplexRange, RationalRange) -> ComplexRange
        | (ComplexRange, RealRange) -> ComplexRange
        | (ComplexRange, ComplexRange) -> ComplexRange
    | Equals(a,b) -> 
        let aRange = ExpressionNumericRange context a
        let bRange = ExpressionNumericRange context b
        PromoteNumericRangePair aRange bRange
    | NumExprRef(t,_) -> FailLingeringMacro t
    | PrevExprRef(t) -> FailLingeringMacro t
