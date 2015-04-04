﻿// Expression.fs  -  Don Cross  -  http://cosinekitty.com
// Symbolic algebra/physics helper.

module Freefall.Expr
open System.Collections.Generic
open Scanner

exception FreefallRuntimeException of string
exception UnexpectedEndException of option<string>       // Some(filename) or None

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
        raise (FreefallRuntimeException("Rational number cannot have zero denominator."))
    elif numer = 0L then
        (0L,1L)
    elif denom < 0L then
        MakeRationalPair (-numer) (-denom)
    else
        let gcd = GreatestCommonDivisor (System.Math.Abs(numer)) denom
        (numer/gcd, denom/gcd)

let MakeRational (numer:int64) (denom:int64) =
    Rational(MakeRationalPair numer denom)

let AddExponentLists (alist:list<int64 * int64>) (blist:list<int64 * int64>) =
    List.map2 (fun (a,b) (c,d) -> MakeRationalPair (a*d + c*b) (b*d)) alist blist

let SubtractExponentLists (alist:list<int64 * int64>) (blist:list<int64 * int64>) =
    List.map2 (fun (a,b) (c,d) -> MakeRationalPair (a*d - c*b) (b*d)) alist blist        

let NegateExponentList (clist:list<int64 * int64>) =
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
let NumDimensions = ConceptNames.Length

type PhysicalConcept = 
    | Zero
    | Concept of list<int64 * int64>       // list must have NumDimensions elements, each representing a rational number for the exponent of that dimension

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
        if ynum = 0L then
            raise (FreefallRuntimeException("Cannot raise 0 to the 0 power."))
        elif ynum < 0L then
            raise (FreefallRuntimeException("Cannot raise 0 to a negative power."))
        else
            Zero    // 0^x = 0 for all positive rational x

// Handy concepts by name...

// A concept to represent any dimensionless quantity...
let Dimensionless       = Concept[(0L,1L); (0L,1L); (0L,1L); (0L,1L); (0L,1L); (0L,1L); (0L,1L)]

// Base concepts...
let MassConcept         = Concept[(1L,1L); (0L,1L); (0L,1L); (0L,1L); (0L,1L); (0L,1L); (0L,1L)]
let DistanceConcept     = Concept[(0L,1L); (1L,1L); (0L,1L); (0L,1L); (0L,1L); (0L,1L); (0L,1L)]
let TimeConcept         = Concept[(0L,1L); (0L,1L); (1L,1L); (0L,1L); (0L,1L); (0L,1L); (0L,1L)]
let TemperatureConcept  = Concept[(0L,1L); (0L,1L); (0L,1L); (1L,1L); (0L,1L); (0L,1L); (0L,1L)]
let SubstanceConcept    = Concept[(0L,1L); (0L,1L); (0L,1L); (0L,1L); (1L,1L); (0L,1L); (0L,1L)]
let CurrentConcept      = Concept[(0L,1L); (0L,1L); (0L,1L); (0L,1L); (0L,1L); (1L,1L); (0L,1L)]
let LuminosityConcept   = Concept[(0L,1L); (0L,1L); (0L,1L); (0L,1L); (0L,1L); (0L,1L); (1L,1L)]

let BaseConcepts = [
//   concept name       base unit       concept
    ("mass",            "kilogram",     MassConcept);
    ("distance",        "meter",        DistanceConcept);
    ("time",            "second",       TimeConcept);
    ("temperature",     "kelvin",       TemperatureConcept);
    ("substance",       "mole",         SubstanceConcept);
    ("current",         "ampere",       CurrentConcept);
    ("luminosity",      "candela",      LuminosityConcept);
]

// Derived concepts...

let SpeedConcept = DivideConcepts DistanceConcept TimeConcept           // speed = distance/time
let AccelerationConcept = DivideConcepts SpeedConcept TimeConcept       // accleration = speed/time
let ForceConcept = MultiplyConcepts MassConcept AccelerationConcept     // force = mass * acceleration

let DerivedConcepts = [
//   concept name       concept
    ("speed",           SpeedConcept);
    ("acceleration",    AccelerationConcept);
    ("force",           ForceConcept);
]

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
        raise (FreefallRuntimeException("Cannot take reciprocal of 0."))
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

let FailLingeringMacro token =
    raise (SyntaxException("Internal error - lingering macro after macro expansion. Should not be possible.", token))
 
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

let FormatNumber x =
    match x with
    | Rational(numer,denom) ->
        if denom = 0L then
            raise (FreefallRuntimeException("Rational number had zero denominator."))
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
    NumberedExpressionList: System.Collections.Generic.List<Expression>;
    AssignmentHook: option<string> -> int -> Expression -> unit;            // AssignmentHook targetName refIndex assignedExpr
}

let AppendNumberedExpression {NumberedExpressionList=numExprList;} expr =
    numExprList.Add(expr)

let FindNumberedExpression {NumberedExpressionList=numExprList;} token index =
    if (index >= 0) && (index < numExprList.Count) then
        numExprList.[index]
    else
        raise (SyntaxException((sprintf "Invalid expression index: expected 0..%d" (numExprList.Count-1)), token))

let FindPreviousExpression {NumberedExpressionList=numExprList;} token =
    if numExprList.Count > 0 then
        numExprList.[numExprList.Count - 1]
    else
        raise (SyntaxException("Cannot refer to previous expression because expression list is empty.", token))

let DefineIntrinsicSymbol {SymbolTable=symtable;} symbol entry =
    if symtable.ContainsKey(symbol) then
        failwith (sprintf "Symbol '%s' is already defined" symbol)
    else
        symtable.Add(symbol, entry)

let DefineSymbol {SymbolTable=symtable;} ({Text=symbol; Kind=kind} as symtoken) symentry =
    if kind <> TokenKind.Identifier then
        raise (SyntaxException("Expected identifier for symbol name", symtoken))
    elif (symtable.ContainsKey(symbol)) then
        raise (SyntaxException("Symbol is already defined", symtoken))
    else
        (symtable.Add(symbol, symentry))

let FindSymbolEntry {SymbolTable=symtable;} ({Text=symbol; Kind=kind} as symtoken) =
    if kind <> TokenKind.Identifier then
        raise (SyntaxException("Expected symbol identifier", symtoken))
    elif not (symtable.ContainsKey(symbol)) then
        raise (SyntaxException("Undefined symbol", symtoken))
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
    | (Rational(anum,aden),Complex(br,bi)) -> (bi = 0.0) && (AreIdenticalNumbers a (Real(br)))
    | (Real(ar),Rational(_,_)) -> AreIdenticalNumbers b a
    | (Real(ar),Real(br)) -> ar = br
    | (Real(ar),Complex(br,bi)) -> (bi = 0.0) && (ar = br)
    | (Complex(_,_),Rational(_,_)) -> AreIdenticalNumbers b a
    | (Complex(_,_),Real(_)) -> AreIdenticalNumbers b a
    | (Complex(ar,ai),Complex(br,bi)) -> (ar = br) && (ai = bi)

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
    raise (SyntaxException((sprintf "Expected function but found %s" found), token))

let rec SimplifyStep context expr =
    match expr with
    | Amount(_) -> expr     // already as simple as possible
    | Solitaire(_) -> expr  // already as simple as possible

    | Functor(funcName, argList) ->
        let simpArgList = List.map (SimplifyStep context) argList
        match FindSymbolEntry context funcName with
        | VariableEntry(_,_) -> FailNonFunction funcName "variable"
        | ConceptEntry(_) -> FailNonFunction funcName "concept"
        | UnitEntry(_) -> FailNonFunction funcName "unit"
        | AssignmentEntry(expr) -> FailNonFunction funcName "assignment target"
        | MacroEntry(_) -> FailLingeringMacro funcName
        | FunctionEntry{StepSimplifier=stepSimplifier;} -> stepSimplifier funcName simpArgList

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
            raise (FreefallRuntimeException("Cannot evaluate 0^0."))
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
    | MacroEntry(_) -> raise (SyntaxException("Attempt to use macro name without parenthesized argument list.", token))
    | FunctionEntry(_) -> raise(SyntaxException("Attempt to use function name without parenthesized argument list.", token))

and FindFunctorConcept context funcNameToken argExprList =
    match FindSymbolEntry context funcNameToken with
    | FunctionEntry({Concepter=concepter;}) -> concepter funcNameToken argExprList
    | MacroEntry(_) -> FailLingeringMacro funcNameToken
    | VariableEntry(_) -> raise(SyntaxException("Attempt to use a variable as a function/macro.", funcNameToken))
    | ConceptEntry(_) -> raise(SyntaxException("Attempt to use a concept as a function/macro.", funcNameToken))
    | UnitEntry(_) -> raise(SyntaxException("Attempt to use a unit as a function/macro.", funcNameToken))
    | AssignmentEntry(_) -> raise(SyntaxException("Attempt to use an assignment target as a function/macro.", funcNameToken))

and EquationConcept context a b =
    let aConcept = ExpressionConcept context a
    let bConcept = ExpressionConcept context b
    if aConcept <> bConcept then
        raise (FreefallRuntimeException(sprintf "Incompatible units: cannot equate/compare %s and %s" (FormatConcept aConcept) (FormatConcept bConcept)))
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
                raise (FreefallRuntimeException(sprintf "Incompatible units: cannot add %s and %s" (FormatConcept firstConcept) (FormatConcept restConcept)))
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
            failwith "Cannot raise 0 to 0 power."
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
            let ySimp = Simplify context y      // take any possible opportunity to boil this down to a number.
            match ySimp with
            | Amount(PhysicalQuantity(Rational(ynum,yden),ySimpConcept)) ->
                if ySimpConcept <> Dimensionless then
                    failwith "IMPOSSIBLE - y concept changed after simplification."
                else
                    ExponentiateConcept xConcept ynum yden
            | _ -> raise (FreefallRuntimeException("Cannot raise a dimensional expression to a non-rational power."))
    else
        raise (FreefallRuntimeException("Cannot raise an expression to a dimensional power."))

and ReciprocalConcept context arg =
    match ExpressionConcept context arg with
    | Zero -> Zero
    | Concept(dimlist) -> 
        // Take the reciprocal by negating each rational number in the list of dimensional exponents.
        Concept(List.map (fun (numer,denom) -> MakeRationalPair (-numer) denom) dimlist)

let ValidateExpressionConcept context expr =
    // Call ExpressionConcept just for the side-effect of looking for errors
    ExpressionConcept context expr |> ignore

//-------------------------------------------------------------------------------------------------
// Intrinsic macros

let FailExactArgCount symbolType requiredCount actualCount token =
    raise (SyntaxException((sprintf "%s requires exactly %d argument(s), but %d were found" symbolType requiredCount actualCount), token))

let SimplifyMacroExpander context macroToken argList =
    match argList with
    | [arg] -> Simplify context arg
    | _ -> FailExactArgCount "Macro" 1 argList.Length macroToken

let IntrinsicMacros =
    [
        ("simp", SimplifyMacroExpander);
    ]

//-------------------------------------------------------------------------------------------------
// Intrinsic functions

// Token -> list<Expression> -> PhysicalConcept;
let Concept_Exp context funcToken argList =
    match argList with
    | [arg] -> 
        let argConcept = ExpressionConcept context arg
        if IsConceptDimensionless argConcept then
            Dimensionless
        else
            raise (SyntaxException(("exp() requires a dimensionless argument, but found " + FormatConcept argConcept), funcToken))
    | _ -> FailExactArgCount "Function" 1 argList.Length funcToken

let SimplifyStep_Exp context funcToken argList =        // caller will step-simplify argList for us.
    match argList with
    | [arg] -> 
        if IsZeroExpression arg then
            UnityAmount
        else 
            match arg with
            | Amount(PhysicalQuantity(number,concept)) -> 
                if concept <> Dimensionless then
                    raise (SyntaxException(("exp() requires a dimensionless argument, but found " + FormatConcept concept), funcToken))
                else
                    match number with

                    | Rational(a,b) -> 
                        let expx = (System.Math.Exp((float a)/(float b)))
                        Amount(PhysicalQuantity(Real(expx), Dimensionless))

                    | Real(x) -> 
                        let expx = System.Math.Exp(x)
                        Amount(PhysicalQuantity(Real(expx), Dimensionless))

                    | Complex(x,y) ->
                        // exp(x + iy) = exp(x)*exp(iy) = exp(x)*(cos(y) + i*sin(y))
                        let expx = System.Math.Exp(x)
                        let cosy = System.Math.Cos(y)
                        let siny = System.Math.Sin(y)
                        Amount(PhysicalQuantity(Complex(expx*cosy, expx*siny), Dimensionless))

            | _ -> Functor(funcToken, [arg])
    | _ -> FailExactArgCount "Function" 1 argList.Length funcToken

let IntrinsicFunctions = 
    [
        ("exp", Concept_Exp, SimplifyStep_Exp);
    ]

//-------------------------------------------------------------------------------------------------
// Create a context with intrinsic symbols built it.

let MakeContext assignmentHook = 
    let context = {
        SymbolTable = new Dictionary<string, SymbolEntry>();
        NumberedExpressionList = new System.Collections.Generic.List<Expression>();
        AssignmentHook = assignmentHook;
    }

    for conceptName, baseUnitName, concept in BaseConcepts do
        DefineIntrinsicSymbol context conceptName (ConceptEntry(concept))

    for macroName, macroFunc in IntrinsicMacros do
        DefineIntrinsicSymbol context macroName (MacroEntry({Expander=(macroFunc context);}))

    for funcName, concepter, stepSimplifier in IntrinsicFunctions do
        DefineIntrinsicSymbol context funcName (FunctionEntry{Concepter=(concepter context); StepSimplifier=(stepSimplifier context);})

    context
