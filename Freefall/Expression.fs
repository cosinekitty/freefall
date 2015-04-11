﻿// Expression.fs  -  Don Cross  -  http://cosinekitty.com
// Symbolic algebra/physics helper.

module Freefall.Expr
open System.Collections.Generic
open System.Numerics
open Scanner

exception FreefallRuntimeException of string
exception UnexpectedEndException of option<string>       // Some(filename) or None

type Number = 
    | Rational of BigInteger * BigInteger
    | Real of float
    | Complex of Complex

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
    match (anum, bnum) with
    | (Rational(an,ad), Rational(bn,bd)) ->
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

let ZeroQuantity = PhysicalQuantity(Rational(R0), Zero)
let Unity = PhysicalQuantity(Rational(R1), Dimensionless)

let IsNumberEqualToInteger n x =
    match x with
    | Rational(numer,denom) -> (numer = n) && (denom.IsOne)      // assumes rational was created using MakeRational to normalize
    | Real re -> re = (float n)
    | Complex(c) -> (c.Imaginary = 0.0) && (c.Real = (float n))

let IsNumberZero = IsNumberEqualToInteger BigInteger.Zero

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
    | Negative of Expression
    | Reciprocal of Expression
    | Sum of list<Expression>
    | Product of list<Expression>
    | Power of Expression * Expression
    | Equals of Expression * Expression
    | NumExprRef of Token * int                     // a reference to a prior expression indexed by automatic integer counter
    | PrevExprRef of Token                          // a reference to the previous expression

let PrimaryToken expr =     // FIXFIXFIX - rework Expression so that this function can always return a primary token
    match expr with
    | Amount(_) -> None
    | Solitaire(t) -> Some(t)
    | Functor(t,_) -> Some(t)
    | Negative(_) -> None
    | Reciprocal(_) -> None
    | Sum(_) -> None
    | Product(_) -> None
    | Power(_) -> None
    | Equals(_) -> None
    | NumExprRef(t,_) -> Some(t)
    | PrevExprRef(t) -> Some(t)

let FailLingeringMacro token =
    SyntaxError token "Internal error - lingering macro after macro expansion. Should not be possible."

exception ExpressionException of Expression * string

let ExpressionError expr message =
    raise (ExpressionException(expr,message))
 
let ZeroAmount = Amount(ZeroQuantity)
let UnityAmount = Amount(Unity)

let IsZeroExpression expr =
    match expr with
    | Amount(PhysicalQuantity(number,concept)) -> (concept = Zero) || (IsNumberZero number)
    | _ -> false

let IsUnityExpression expr =
    match expr with
    | Amount(PhysicalQuantity(number,concept)) -> (concept = Dimensionless) && (IsNumberEqualToInteger BigInteger.One number)
    | _ -> false

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
    | Real re -> re.ToString()
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
    | Solitaire(token) -> token.Text
    | Functor(funcName, argList) -> funcName.Text + "(" + FormatExprList argList + ")"
    | Negative arg -> "neg(" + FormatExpression arg + ")"
    | Reciprocal arg -> "recip(" + FormatExpression arg + ")"
    | Sum terms -> "sum(" + FormatExprList terms + ")"
    | Product factors -> "prod(" + FormatExprList factors + ")"
    | Power(a,b) -> "pow(" + FormatExpression a + "," + FormatExpression b + ")"
    | Equals(a,b) -> FormatExpression a + " = " + FormatExpression b
    | NumExprRef(_,i) -> "#" + i.ToString()
    | PrevExprRef(_) -> "#"

and FormatExprList exprlist =
    match exprlist with
    | [] -> ""
    | [single] -> FormatExpression single
    | first :: rest -> FormatExpression first + "," + FormatExprList rest

//-----------------------------------------------------------------------------------------------------
//  Context provides mutable state needed to execute a series of Freefall statements.
//  Some statements will define units and types of variables that are subsequently referenced.
//  Executed statements will accumulate references that can be used by later statements.
//  Some statements "forget" things statement references on purpose. 

type Macro = {
    Expander: Token -> list<Expression> -> Expression;
}

type Function = {
    Concepter:  Token -> list<Expression> -> PhysicalConcept;
    StepSimplifier: Token -> list<Expression> -> Expression;
    Evaluator: Token -> list<PhysicalQuantity> -> PhysicalQuantity;
    EquationDistributor: Token -> list<Expression> -> list<Expression> -> Expression;
    Ranger: Token -> list<NumericRange> -> NumericRange;
}

type SymbolEntry =
    | VariableEntry of NumericRange * PhysicalConcept
    | ConceptEntry of PhysicalConcept
    | UnitEntry of PhysicalQuantity
    | AssignmentEntry of Expression         // the value of a named expression is the expression itself
    | MacroEntry of Macro
    | FunctionEntry of Function

type Context = {
    SymbolTable: Dictionary<string,SymbolEntry>;
    NumberedExpressionList: ResizeArray<Expression>;
    AssignmentHook: option<string> -> int -> Expression -> unit;            // AssignmentHook targetName refIndex assignedExpr
    ProbeHook: Expression -> NumericRange -> PhysicalConcept -> unit;
}

let AppendNumberedExpression {NumberedExpressionList=numExprList;} expr =
    numExprList.Add(expr)

let FindNumberedExpression {NumberedExpressionList=numExprList;} token index =
    if (index >= 0) && (index < numExprList.Count) then
        numExprList.[index]
    else
        SyntaxError token (sprintf "Invalid expression index: expected 0..%d" (numExprList.Count-1))

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
    | (Negative(na),Negative(nb)) -> AreIdentical context na nb
    | (Negative(_), _) -> false
    | (_, Negative(_)) -> false
    | (Reciprocal(ra),Reciprocal(rb)) -> AreIdentical context ra rb
    | (Reciprocal(_), _) -> false
    | (_, Reciprocal(_)) -> false
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

let AddQuantities (PhysicalQuantity(aNumber,aConcept)) (PhysicalQuantity(bNumber,bConcept)) =
    Amount(PhysicalQuantity(AddNumbers aNumber bNumber, AddConcepts aConcept bConcept))

let MultiplyQuantities (PhysicalQuantity(aNumber,aConcept)) (PhysicalQuantity(bNumber,bConcept)) =
    Amount(PhysicalQuantity(MultiplyNumbers aNumber bNumber, MultiplyConcepts aConcept bConcept))

let AreOppositeTerms context a b =
    (AreIdentical context a (Negative b)) ||
    (AreIdentical context b (Negative a))

let AreOppositeFactors context a b =
    (AreIdentical context a (Reciprocal b)) ||
    (AreIdentical context b (Reciprocal a))

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

let CancelOppositeTerms context termlist = 
    CancelOpposite (AreOppositeTerms context) termlist

let CancelOppositeFactors context factorlist = 
    CancelOpposite (AreOppositeFactors context) factorlist

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

let FailNonFunction token found =
    SyntaxError token (sprintf "Expected function but found %s" found)

let FindFunctionEntry context funcNameToken =
    match FindSymbolEntry context funcNameToken with
    | VariableEntry(_,_) -> FailNonFunction funcNameToken "variable"
    | ConceptEntry(_) -> FailNonFunction funcNameToken "concept"
    | UnitEntry(_) -> FailNonFunction funcNameToken "unit"
    | AssignmentEntry(expr) -> FailNonFunction funcNameToken "assignment target"
    | MacroEntry(_) -> FailLingeringMacro funcNameToken
    | FunctionEntry(fe) -> fe

let rec SimplifyStep context expr =
    match expr with
    | Amount(_) -> expr     // already as simple as possible
    | Solitaire(_) -> expr  // already as simple as possible

    | Functor(funcName, argList) ->
        let simpArgList = List.map (SimplifyStep context) argList
        let {StepSimplifier=stepSimplifier} = FindFunctionEntry context funcName
        stepSimplifier funcName simpArgList

    | Negative(Negative(x)) -> SimplifyStep context x
    | Negative(arg) -> 
        match SimplifyStep context arg with
        | Amount(PhysicalQuantity(number,concept)) -> Amount(PhysicalQuantity((NegateNumber number),concept))
        | sarg -> Negative(sarg)

    | Reciprocal(Reciprocal(x)) -> SimplifyStep context x
    | Reciprocal(arg) -> 
        match SimplifyStep context arg with
        | Amount(PhysicalQuantity(number,concept)) -> Amount(PhysicalQuantity((InvertNumber number), (InvertConcept concept)))
        | sarg -> Reciprocal(sarg)

    | Sum(termlist) ->
        let simpargs = 
            SimplifySumArgs (List.map (SimplifyStep context) termlist) 
            |> CancelOppositeTerms context 
            |> MergeConstants AddQuantities
        match simpargs with
        | [] -> ZeroAmount
        | [term] -> term
        | _ -> Sum simpargs

    | Product(factorlist) ->
        let simpfactors = 
            SimplifyProductArgs (List.map (SimplifyStep context) factorlist) 
            |> CancelOppositeFactors context
            |> MergeConstants MultiplyQuantities
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
        // FIXFIXFIX - could use more simplification and validation rules here
        if (IsZeroExpression sx) && (IsZeroExpression sy) then
            ExpressionError expr "Cannot evaluate 0^0."
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
    | (Sum terms)::rest -> (RemoveZeroes terms) @ (SimplifySumArgs rest)
    | first::rest -> SkipZero first (SimplifySumArgs rest)

and SimplifyProductArgs simpargs =           
    match simpargs with
    | [] -> []
    | (Product factors)::rest -> (RemoveUnities factors) @ (SimplifyProductArgs rest)
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
// Returns an Option(Concept) because None is needed for 0*anything, which has no specific units.
// No other reason for returning None should be allowed;
// must throw an exception for any unit compatibility violation.

let rec ExpressionConcept context expr =
    match expr with
    | Amount(PhysicalQuantity(number,concept)) -> if IsNumberZero number then Zero else concept
    | Solitaire(vartoken) -> FindSolitaireConcept context vartoken
    | Functor(funcName,argList) -> FindFunctorConcept context funcName argList
    | Negative(arg) -> ExpressionConcept context arg
    | Reciprocal(arg) -> ReciprocalConcept context arg
    | Sum(terms) -> SumConcept context terms
    | Product(factors) -> ProductConcept context factors
    | Power(a,b) -> PowerConcept context a b
    | Equals(a,b) -> EquationConcept context a b
    | NumExprRef(t,_) -> FailLingeringMacro t
    | PrevExprRef(t) -> FailLingeringMacro t

and FindSolitaireConcept context token =
    match FindSymbolEntry context token with
    | VariableEntry(_,concept) -> concept
    | ConceptEntry(concept) -> concept
    | UnitEntry(PhysicalQuantity(_,concept)) -> concept
    | AssignmentEntry(expr) -> ExpressionConcept context expr
    | MacroEntry(_) -> SyntaxError token "Attempt to use macro name without parenthesized argument list."
    | FunctionEntry(_) -> SyntaxError token "Attempt to use function name without parenthesized argument list."

and FindFunctorConcept context funcNameToken argExprList =
    match FindSymbolEntry context funcNameToken with
    | FunctionEntry({Concepter=concepter;}) -> concepter funcNameToken argExprList
    | MacroEntry(_) -> FailLingeringMacro funcNameToken
    | VariableEntry(_) -> SyntaxError funcNameToken "Attempt to use a variable as a function/macro."
    | ConceptEntry(_) -> SyntaxError funcNameToken "Attempt to use a concept as a function/macro."
    | UnitEntry(_) -> SyntaxError funcNameToken "Attempt to use a unit as a function/macro."
    | AssignmentEntry(_) -> SyntaxError funcNameToken "Attempt to use an assignment target as a function/macro."

and EquationConcept context a b =
    let aConcept = ExpressionConcept context a
    let bConcept = ExpressionConcept context b
    if aConcept <> bConcept then
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
    let yConcept = ExpressionConcept context y
    if yConcept = Zero then
        if yConcept = Zero then
            ExpressionError y "Cannot raise 0 to 0 power."
        else
            Dimensionless
    elif yConcept = Dimensionless then
        let xConcept = ExpressionConcept context x
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

    | Reciprocal(arg) -> EvalConcept context arg |> InvertConcept

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
    | Negative(arg) -> ExpressionError expr "Negation not allowed in concept expression."
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
    | Functor(funcName,argList) -> 
        let {Evaluator=evaluator} = FindFunctionEntry context funcName 
        List.map (EvalQuantity context) argList
        |> evaluator funcName
    | Negative(arg) -> 
        EvalQuantity context arg
        |> NegateQuantity
    | Reciprocal(arg) ->
        EvalQuantity context arg
        |> InvertQuantity
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

let QuantityNumericRange (PhysicalQuantity(number,_)) =
    match number with
    | Rational(a,b) -> if b.IsOne then IntegerRange else RationalRange
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
    | Functor(funcName,argList) -> 
        let {Ranger=ranger} = FindFunctionEntry context funcName 
        let rlist = List.map (ExpressionNumericRange context) argList
        ranger funcName rlist
    | Negative(arg) -> ExpressionNumericRange context arg
    | Reciprocal(arg) -> PromoteNumericRangePair RationalRange (ExpressionNumericRange context arg)
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


