module Freefall.Intrinsic

open System.Collections.Generic

open Freefall.Partitions
open Freefall.Scanner
open Freefall.Expr
open Freefall.Calculus
open Freefall.Stmt
open Freefall.Parser

//-------------------------------------------------------------------------------------------------

let EvalIntegerIndex context indexExpr (limit:int) =
    match EvalQuantity context indexExpr with
    | PhysicalQuantity(Rational(bigIndex,denom),concept) when IsConceptDimensionless concept && denom.IsOne ->
        let bigLimit = bigint limit
        if 0I <= bigIndex && bigIndex < bigLimit then
            int bigIndex
        else
            ExpressionError indexExpr (sprintf "Index expression = %O, but must be in the range 0..%d" bigIndex (limit-1))
    | _ -> ExpressionError indexExpr "Index expression does not evaluate to a dimensionless integer."

//-------------------------------------------------------------------------------------------------
// Intrinsic macros

let FailExactArgCount symbolType requiredCount actualCount token =
    SyntaxError token (sprintf "%s requires exactly %d argument(s), but %d were found" symbolType requiredCount actualCount)

let FailSingleArgMacro macroToken (argList:list<Expression>) =
    FailExactArgCount "Macro" 1 argList.Length macroToken

let FailDimensionalArgument funcToken argConcept =
    SyntaxError funcToken (sprintf "%s() requires a dimensionless argument, but found %s" funcToken.Text (FormatConcept argConcept))

let VerifyDimensionlessArgument funcToken argConcept =
    if not (IsConceptDimensionless argConcept) then
        FailDimensionalArgument funcToken argConcept

let SimplifyMacroExpander context macroToken argList =
    match argList with
    | [arg] -> Simplify context arg
    | _ -> FailSingleArgMacro macroToken argList

let EvalMacroExpander context macroToken argList =
    match argList with
    | [arg] -> Amount(EvalQuantity context arg)
    | _ -> FailSingleArgMacro macroToken argList

let FloatMacroExpander context macroToken argList =
    match argList with
    | [arg] -> Amount(ApproxQuantity context arg)
    | _ -> FailSingleArgMacro macroToken argList

let DiffVariableToken context expr =
    match expr with
    | Solitaire(token) ->
        match FindSymbolEntry context token with
        | VariableEntry(range,_) -> 
            match range with
            | RealRange -> token
            | ComplexRange -> token
            | _ -> SyntaxError token "Differentiated variable must be real or complex."
        | _ -> SyntaxError token "Expected variable name."
    | _ -> ExpressionError expr "Expected identifier."

let DiffVariableName context expr = (DiffVariableToken context expr).Text

let DiffDerivMacroExpander derivKind context macroToken argList =
    // deriv(expr, var1, ...)  or diff(expr, var1, ...)
    match argList with
    | [] | [_] -> SyntaxError macroToken (sprintf "Expected %s(expr, vars...)" macroToken.Text)
    | expr :: varlist ->
        let varnames = List.map (DiffVariableName context) varlist
        TakeDifferential derivKind context varnames expr |> Simplify context

let AssertIdenticalMacroExpander context macroToken argList =
    // asserti(expr1,expr2)
    match argList with
    | [expr1; expr2] ->
        if AreIdentical context expr1 expr2 then
            expr1       // All macros have to return some expression, so we choose the left expression.
        else
            SyntaxError macroToken (sprintf "Expressions are not identical:\n%s\n%s" (FormatExpression expr1) (FormatExpression expr2))
    | _ -> SyntaxError macroToken (sprintf "%s requires exactly 2 expression arguments." macroToken.Text)

let PowerMacroExpander powerAmount context macroToken argList =
    // sqrt(x) ==> (x)^(1/2)
    // sqrt(x,y,z) ==> prod(x,y,z)^(1/2)
    // cbrt(x) ==> (x)^(1/3)
    // square(x) ==> x^2
    let arg =
        match argList with
        | [] -> SyntaxError macroToken (sprintf "%s requires 1 or more arguments." macroToken.Text)
        | [single] -> single
        | _ -> Product(argList)
    Power(arg, powerAmount)

let ExtractMacroExpander context macroToken argList =
    // extract(root, index)
    // index must be an integer constant
    // Returns the expression from within root at the traversal index,
    // the same way decomp enumerates child expressions.
    match argList with
    | [rootExpr; indexExpr] ->
        let array = DecomposeExpression rootExpr
        let index = EvalIntegerIndex context indexExpr array.Count
        array.[index]

    | _ -> SyntaxError macroToken (sprintf "%s requires parameters (root, index)." macroToken.Text)

let InjectMacroExpander context macroToken argList =
    // inject(root, index, funcname, extra_args...)
    // Create a clone of the expression, only with the substitution
    // root[index] := funcname(root[index], extra_args...)

    match argList with 
    | rawRootExpr :: rawIndexExpr :: functorNameExpr :: rawExtraArgsList ->
        // Note that this macro is special: it uses RawArgs option to avoid pre-expanding
        // the arguments passed to it, because of the unusual passing of a function name as a solitaire.
        // If arguments were pre-expanded, that would cause a syntax error.
        // So we need to prepare everything here except functorNameExpr.
        let rootExpr = PrepareExpression context rawRootExpr
        let indexExpr = PrepareExpression context rawIndexExpr
        let extraArgsList = List.map (PrepareExpression context) rawExtraArgsList

        match functorNameExpr with
        | Solitaire(functorNameToken) ->
            let array = DecomposeExpression rootExpr
            let index = EvalIntegerIndex context indexExpr array.Count
            let replacementRawExpr = Functor(functorNameToken, array.[index] :: extraArgsList)
            let replacementExpr = PrepareExpression context replacementRawExpr
            let expr, _ = ReplaceExpressionNode replacementExpr rootExpr index 0
            expr

        | _ -> ExpressionError functorNameExpr "Expected function or macro name."

    | _ -> SyntaxError macroToken (sprintf "%s requires parameters (root, index, funcname, ...)" macroToken.Text)

let SubstMacroExpander context macroToken argList =
    // subst(root, index, repl)
    // Similar to inject, only with a replacement expression instead of a functor name.
    // Create a clone of the root expression, with a particular node replaced with repl expression.
    match argList with

    | [rootExpr; indexExpr; replExpr] ->
        let array = DecomposeExpression rootExpr
        let index = EvalIntegerIndex context indexExpr array.Count
        let expr, _ = ReplaceExpressionNode replExpr rootExpr index 0
        expr

    | _ -> SyntaxError macroToken (sprintf "%s requires parameters (root, index, repl)" macroToken.Text)

//-------------------------------------------------------------------------------------------------
// Factoring expressions

// expr      = -3.79*(x+y)^3
// Coeff     = -3.79
// VarPart   =  (x+y)
// Exponent  =  3

type Triplet = {
    Coeff: PhysicalQuantity
    VarPart: Expression
    Exponent: Expression
}

let TermList expr =
    match expr with
    | Sum(termlist) -> termlist
    | _ -> [expr]

let TermListLength expr = TermList expr |> List.length

let FactorList expr =
    match expr with
    | Product(factorlist) -> factorlist
    | _ -> [expr]

let FactorListLength expr = FactorList expr |> List.length

let FlatSum termlist =
    match termlist with
    | [] -> AmountZero
    | [single] -> single
    | _ -> Sum(termlist)

let AllPossibleTermListPartitions context expr = 
    seq {
        for exprlist in Partitions (TermList expr) do
            if not ((List.length exprlist) = 1 && (List.length (List.head exprlist)) > 1) then      // ignore sum(sum())
                yield FlatSum (List.map FlatSum exprlist)
    }

let MakeTriplet expr =
    // We assume caller has already simplified the expression 
    // so that constant factors have been moved to the front of all products.
    let coeff, varpart, exponent =
        match expr with
        | Amount(c) -> c, AmountOne, AmountOne

        | Power(x,y) -> QuantityOne, x, y

        | Product([Amount(c); Power(x, y)]) -> c, x, y
        | Product([Amount(c); x]) -> c, x, AmountOne
        | Product(Amount(c) :: rest) -> c, Product(rest), AmountOne

        | Product(_)
        | Del(_,_)
        | Functor(_)
        | Sum(_)
        | Solitaire(_) -> 
            QuantityOne, expr, AmountOne

        | NumExprRef(token,_)
        | PrevExprRef(token) -> 
            FailLingeringMacro token

        | Equals(_,_)
        | DoesNotEqual(_,_)
            -> ExpressionError expr "Cannot make factor pattern out of a relational expression."
    {Coeff=coeff; VarPart=varpart; Exponent=exponent}

let rec CancelFactor context factorList commonFactor commonExponent =
    //printfn "!!! CancelFactor: factorList=%s, commonFactor=%s, commonExponent=%s" (FormatExpressionList factorList) (FormatExpression commonFactor) (FormatExpression commonExponent)

    match factorList with
    | [] -> failwith (sprintf "Cannot cancel factor=%s, exponent=%s from factor list." (FormatExpression commonFactor) (FormatExpression commonExponent))   // should never happen
    | factor :: restFactorList ->
        let {Coeff=coeff; VarPart=powbase; Exponent=powexp} = MakeTriplet factor
        //printfn "!!! CancelFactor triplet : powbase=%s, powexp=%s" (FormatExpression powbase) (FormatExpression powexp)
        if AreIdentical context powbase commonFactor then
            // We found where we can cancel the commonFactor.
            // This is a recursion limit; we can't cancel again.

            // If there is a non-unity coefficient here, it means there was a problem in pre-simplification.
            if not (IsQuantityOne coeff) then
                failwith "Found unexpected non-unity coefficient in CancelFactor."

            if AreIdentical context powexp commonExponent then
                // The non-coefficient parts cancel completely.
                restFactorList
            else
                // Subtract exponents to find the residue.
                // Simplifier will de-uglify the exponent difference later.
                (Power(commonFactor, Sum [powexp; Product[AmountNegOne; commonExponent]])) :: restFactorList
        else
            // Cannot cancel first factor, so it is kept verbatim and we recurse to cancel from the remaining factors.
            factor :: (CancelFactor context restFactorList commonFactor commonExponent)

let rec CancelFactorFromAllTerms context commonFactor termlist commonExponent : list<Expression> =
    // Do cancellation by dividing by commonFactor^commonExponent on every term.
    // This must be possible in every case or there is a bug in the calling code!
    match termlist with
    | [] -> []
    | term :: restTermList -> 
        let canceledFirstTerm = Product (CancelFactor context (FactorList term) commonFactor commonExponent)
        let restCanceledTerms = CancelFactorFromAllTerms context commonFactor restTermList commonExponent
        canceledFirstTerm :: restCanceledTerms

let FactorAppearsInAllTerms context possibleCommonFactor termlist : option<Expression> =
    // If the factor appears in all terms in termlist, we return its common exponent.
    // Otherwise we return None.
    // We have to expand each term in the termlist to its constituent factors,
    // each with its own exponent, and look at just the base part.
    // If we can find only variable exponents, we choose the first one we see.
    // We prefer to extract a factor with a rational exponent if possible.
    // In that case, we will only factor if all rational exponents are positive or
    // all rational exponents are negative.  This prevents factoring something
    // like (x + 1/x).
    // So we remember the largest rational exponent and the smallest rational exponent.
    let mutable minNumer = 0I
    let mutable minDenom = 1I
    let mutable maxNumer = 0I
    let mutable maxDenom = 1I

    //FormatExpressionList termlist |> printfn "!!! FactorAppearsInAllTerms: termlist = %s"

    // We will store the first non-rational exponent we see in the output parameter commonExponent.
    // Later we will overwrite it if rational exponents warrant such.
    let mutable (commonExponent:option<Expression>) = None

    let mutable foundFactorInAllTerms = true
    for term in termlist do
        let mutable foundFactorInThisTerm = false
        for factor in FactorList term do
            let {Coeff=coeff; VarPart=powbase; Exponent=exponent} = MakeTriplet factor
            if AreIdentical context powbase possibleCommonFactor then
                foundFactorInThisTerm <- true
                match exponent with
                | Amount(PhysicalQuantity(Rational(numer,denom) as rational, concept)) when (numer <> 0I) && (concept = Dimensionless) ->
                    if minNumer = 0I then
                        // This is the first rational exponent we have seen, so start out with it.
                        minNumer <- numer
                        minDenom <- denom
                        maxNumer <- numer
                        maxDenom <- denom
                    else
                        if -1 = CompareRationals numer denom minNumer minDenom then
                            minNumer <- numer
                            minDenom <- denom

                        if +1 = CompareRationals numer denom maxNumer maxDenom then
                            maxNumer <- numer
                            maxDenom <- denom

                | _ -> 
                    if commonExponent = None then
                        commonExponent <- Some(exponent)

        foundFactorInAllTerms <- foundFactorInAllTerms && foundFactorInThisTerm

    if foundFactorInAllTerms then
        // If rational exponents are all the same polarity, choose whichever exponent has 
        // the smallest absolute value (is the closest to zero).            
        if (minNumer < 0I) && (maxNumer > 0I) then
            None    // cannot factor because of mixed-polarity rational exponents.
        elif minNumer > 0I then
            // All rational exponents are positive, so choose the smallest one as the common exponent.
            Some(Amount(PhysicalQuantity(MakeRational minNumer minDenom, Dimensionless)))
        elif maxNumer < 0I then
            // All rational exponents are negative, so choose the largest one (the one closest to zero) as the common exponent.
            Some(Amount(PhysicalQuantity(MakeRational maxNumer maxDenom, Dimensionless)))
        else
            // We did not find any rational exponents, so leave 
            // commonExponent set to the first non-rational exponent (if any),
            // or None, if there not found.
            commonExponent
    else
        None    // Cannot factor because desired factor did not appear in all terms.

let FindUniqueFactors context termlist =
    let mutable uniqueFactorList = []
    for term in termlist do
        for factor in FactorList term do
            // Ignore constant coefficients and exponents.
            // For example, if factor = 3.7*(x+y)^3, then let vpart = x+y
            let {VarPart=vpart} = MakeTriplet factor
            if not (IsExpressionOne vpart) then
                // Prepend vpart if unique
                if None = List.tryFind (fun existing -> AreIdentical context existing vpart) uniqueFactorList then
                    uniqueFactorList <- vpart :: uniqueFactorList
    uniqueFactorList

let PerfectSquareRoot context expr =
    match expr with
    | Amount(PhysicalQuantity(Rational(numer,denom), concept)) when (concept = Dimensionless) && (numer > 0I) ->
        let rootNumer = IntegerSquareRoot numer
        let rootDenom = IntegerSquareRoot denom
        if (rootNumer*rootNumer = numer) && (rootDenom*rootDenom = denom) then
            Some(Amount(PhysicalQuantity((MakeRational rootNumer rootDenom), Dimensionless)))
        else
            None

    | Power(x, Amount(PhysicalQuantity(Rational(numer, denom), concept))) when (concept = Dimensionless) && (denom = 1I) && (bigint.Abs(numer) % 2I = 0I) ->
        // We can take a perfect square root of anything with an even integer exponent.
        // sqrt(x^42) = x^21
        // sqrt(x^2) = x
        // sqrt(x^(-8)) = x^(-4)
        if numer = 2I then
            Some(x)       // x^2  ==>  x
        else
            Some(Power(x, Amount(PhysicalQuantity(Rational(numer/2I, denom), Dimensionless))))

    | _ -> 
        None

let FactorDifferenceOfSquares aIndex bIndex context expr =
    let termlist = TermList expr
    if List.length termlist = 2 then
        // a^2 - b^2 ==> (a+b) * (a-b)
        let aSquared = List.nth termlist aIndex
        let neg_bSquared = List.nth termlist bIndex
        let bSquared = MakeNegative neg_bSquared
        match PerfectSquareRoot context aSquared, PerfectSquareRoot context bSquared with
        | Some(a), Some(b) ->
            Product[Sum[a; b]; Sum[a; MakeNegative b]]
        | _, _ ->
            expr
    else
        expr

let FactorSquaredBinomial middleIndex leftIndex rightIndex context expr =
    let termlist = TermList expr
    if List.length termlist = 3 then
        let left   = List.nth termlist leftIndex
        let right  = List.nth termlist rightIndex
        let middle = List.nth termlist middleIndex

        match PerfectSquareRoot context left, PerfectSquareRoot context right with
        | Some(leftRoot), Some(rightRoot) ->
            let checkMiddlePos = Product[AmountTwo; leftRoot; rightRoot] |> Simplify context
            let checkMiddleNeg = Product[AmountNegTwo; leftRoot; rightRoot] |> Simplify context
            //printfn "middle=%s , checkMiddlePos=%s" (FormatExpression middle) (FormatExpression checkMiddlePos)
            if AreIdentical context middle checkMiddlePos then
                // x^2 + 2*x*y + y^2 ==> (x+y)^2
                Power(Sum[leftRoot; rightRoot], AmountTwo)
            elif AreIdentical context middle checkMiddleNeg then
                // x^2 - 2*x*y + y^2 ==> (x-y)^2
                Power(Sum[leftRoot; (OptimizeMultiply AmountNegOne rightRoot)], AmountTwo)
            else
                expr
        | _, _ -> expr
    else
        expr

let rec FactorRationalCoeff termlist : option<bigint * bigint> =
    // Pull out as much of a constant rational factor as possible from all the terms.
    // Only do this if all denominators are the same (including 1, i.e. all integer).
    // Make the pulled-out rational factor positive unless all terms look negative,
    // in which case we negate all the terms.
    match termlist with
    | [] -> 
        None        // Recursion should stop with other cases - getting here is weird.

    | [term] -> 
        let {Coeff=coeff} = MakeTriplet term
        match coeff with
        | PhysicalQuantity(Rational(numer,denom), _) -> Some(numer, denom)
        | _ -> None

    | term :: rest ->
        let {Coeff=coeff} = MakeTriplet term
        match coeff with
        | PhysicalQuantity(Rational(numer,denom), _) -> 
            match FactorRationalCoeff rest with
            | None -> None
            | Some(rnumer, rdenom) ->
                if (denom = rdenom) then 
                    let a = bigint.Abs(numer)
                    let b = bigint.Abs(rnumer)
                    let gcdNumer = GreatestCommonDivisor a b
                    if (rnumer < 0I) && (numer < 0I) then
                        // All are negative (so far), so hand back a negative numerator again.
                        Some(-gcdNumer, denom)
                    else
                        // At least one positive, so hand back positive.
                        if (gcdNumer = 1I) && (denom = 1I) then
                            None    // no point factoring out 1, and will cause infinite recursion!
                        else
                            Some(gcdNumer, denom)
                else
                    None    // Denominators do not match, so cannot factor constant out.
        | _ -> None


let rec Factor depth context expr =
    // Factoring makes sense on sums.
    // For example, factor(sum(x^2, x^3, x^4)) ==> prod(x^2, sum(1,x,x^2)).
    // Pre-simplify the expression so that we can rely on constant factors coming first in products.
    let simp = Simplify context expr
    let mutable best = None
    let mutable bestFactorCount = 0
    for partition in AllPossibleTermListPartitions context simp do
        if depth = 0 || TermListLength partition > 1 then
            match FactorTermList (1+depth) context partition with
            | Some(attempt) -> 
                let factored = Simplify context attempt
                let factorCount = FactorListLength factored
                if factorCount > bestFactorCount then
                    best <- Some(factored)
                    bestFactorCount <- factorCount
            | None -> ()
    match best with
    | Some(bestFactoring) -> bestFactoring
    | None -> simp

and FactorTermList depth context expr : option<Expression> =
    let rawTermList = TermList expr
    let rawTermListLength = List.length rawTermList
    if rawTermListLength > 1 then
        // There are multiple terms. Factor each term in the term list to
        // give us a better chance at finding even more common factors over the entire sum.
        // For example:  (a + a*x) + (a + a*y) --> a*(1+x) + a*(1+y) -->  a*((1+x) + (1+y)).
        let termlist = List.map (Factor 0 context) rawTermList

        // Create a list of all distinct factors from all terms.
        let uniqueFactors = FindUniqueFactors context termlist
        let mutable improvedTermList = termlist
        let factorsPulledOut = ResizeArray<Expression>()

        // Determine whether each factor appears in *all* the terms (not just one or two).
        // If so, put it aside, and create a new termList
        // with that factor removed from all terms.
        for factor in uniqueFactors do
            match FactorAppearsInAllTerms context factor improvedTermList with
            | None -> ()
            | Some(exponent) -> 
                //FormatExpression exponent |> printfn "FactorAppearsInAllTerms: exponent=%s"
                improvedTermList <- CancelFactorFromAllTerms context factor improvedTermList exponent
                if IsExpressionOne exponent then
                    factorsPulledOut.Add(factor)
                else
                    factorsPulledOut.Add(Power(factor, exponent))

        // Pull out as much of a constant rational factor as possible from all the terms.
        match FactorRationalCoeff improvedTermList with
        | None -> ()
        | Some(numer,denom) ->
            let constToPullOut = Amount(PhysicalQuantity(Rational(numer, denom), Dimensionless))

            // The constant coefficient we factored out goes at the front of the product list.
            factorsPulledOut.Insert(0, constToPullOut)

            // Divide through by rational constant.  There is no need to simplify here, because we will do that below.
            improvedTermList <- List.map (fun t -> Divide t constToPullOut) improvedTermList

        if factorsPulledOut.Count > 0 then
            // We were able to do some factoring after all.
            // The residue may still be factorable using special purpose rules (e.g. difference of squares).
            let residue = Sum(improvedTermList) |> Factor 0 context
            factorsPulledOut.Add(residue)
            Some(Product (List.ofSeq factorsPulledOut) |> Simplify context)
        else
            // Check special case rules, e.g. difference-of-squares.
            let special =
                expr
                |> FactorSquaredBinomial 0 1 2 context
                |> FactorSquaredBinomial 1 0 2 context
                |> FactorSquaredBinomial 2 0 1 context
                |> FactorDifferenceOfSquares 0 1 context
                |> FactorDifferenceOfSquares 1 0 context
            //printfn "special = %s" (FormatExpression special)
            Some(special)

    elif rawTermListLength = 1 then
        // There is a single term.  See if its factors can be recursively broken down into more factors.
        let factorlist = FactorList expr
        if List.length factorlist > 1 then
            let resultlist = List.map (Factor 0 context) factorlist
            Some(Product(resultlist) |> Simplify context)
        else
            None
    else
        None

let FactorMacroExpander context macroToken argList = 
    // factor(expr)
    match argList with
    | [expr] -> Factor 0 context expr
    | _ -> SyntaxError macroToken (sprintf "%s requires a single expression argument" macroToken.Text)

//-------------------------------------------------------------------------------------------------

let IntrinsicMacros =
    [
        ("asserti", PreExpandArgs,  AssertIdenticalMacroExpander)
        ("cbrt",    PreExpandArgs,  PowerMacroExpander AmountOneThird)
        ("deriv",   PreExpandArgs,  DiffDerivMacroExpander Derivative)
        ("diff",    PreExpandArgs,  DiffDerivMacroExpander Differential)
        ("eval",    PreExpandArgs,  EvalMacroExpander)
        ("extract", PreExpandArgs,  ExtractMacroExpander)
        ("factor",  PreExpandArgs,  FactorMacroExpander)
        ("float",   PreExpandArgs,  FloatMacroExpander)
        ("inject",  RawArgs,        InjectMacroExpander)
        ("simp",    PreExpandArgs,  SimplifyMacroExpander)
        ("sqrt",    PreExpandArgs,  PowerMacroExpander AmountOneHalf)
        ("square",  PreExpandArgs,  PowerMacroExpander AmountTwo)
        ("subst",   PreExpandArgs,  SubstMacroExpander)
    ]

//-------------------------------------------------------------------------------------------------
// Intrinsic functions

let SimpleEquationDistributor funcToken leftList rightList =
    Equals(Functor(funcToken,leftList), Functor(funcToken,rightList))

let Function_Exp = { new IFunctionHandler with
    member this.EvalRange funcToken rangelist =
        match rangelist with
        | [range] ->
            match range with
            | IntegerRange(FiniteLimit(lo), FiniteLimit(hi)) when lo.IsZero && hi.IsZero -> 
                IntegerRange(FiniteLimit(1I), FiniteLimit(1I))
            | IntegerRange(_,_) -> RealRange
            | RationalRange -> RealRange
            | RealRange -> RealRange
            | ComplexRange -> ComplexRange
        | _ -> FailExactArgCount "Function" 1 rangelist.Length funcToken

    member this.EvalConcept context funcToken argList =
        match argList with
        | [arg] -> 
            ExpressionConcept context arg |> VerifyDimensionlessArgument funcToken
            Dimensionless
        | _ -> FailExactArgCount "Function" 1 argList.Length funcToken

    member this.EvalNumeric context funcToken qlist =
        match qlist with
            | [PhysicalQuantity(number,concept) as quantity] -> 
                VerifyDimensionlessArgument funcToken concept
                if IsQuantityZero quantity then
                    QuantityOne
                else
                    match number with
                    | Rational(a,b) -> 
                        let x = (float a) / (float b)
                        PhysicalQuantity(MakeReal(System.Math.Exp(x)), Dimensionless)

                    | Real(x) -> 
                        PhysicalQuantity(MakeReal(System.Math.Exp(x)), Dimensionless)

                    | Complex(z) ->
                        PhysicalQuantity(MakeComplex(complex.Exp(z)), Dimensionless)
            | _ -> FailExactArgCount "Function" 1 qlist.Length funcToken

    member this.SimplifyStep context funcToken argList =
        match argList with
        | [arg] -> 
            if IsExpressionZero arg then
                AmountOne
            else 
                Functor(funcToken, [arg])
        | _ -> FailExactArgCount "Function" 1 argList.Length funcToken

    member this.Differential derivKind context varNameList funcToken argList =
        // d(exp(z)) = exp(z) dz
        match argList with
        | [arg] ->
            let dz = TakeDifferential derivKind context varNameList arg
            let exp_z = Functor(funcToken, argList)
            Product[exp_z; dz]
        | _ -> FailExactArgCount "Function" 1 argList.Length funcToken
            
    member this.DistributeAcrossEquation context funcToken leftList rightList =
        SimpleEquationDistributor funcToken leftList rightList

    member this.LatexName = @"\exp"
}

let LnReal x =
    if x < 0.0 then
        PhysicalQuantity(MakeComplex(complex.Log(complex(x, 0.0))), Dimensionless)
    else
        PhysicalQuantity(MakeReal(System.Math.Log(x)), Dimensionless)

let Function_Ln = { new IFunctionHandler with

    member this.EvalRange funcToken rangelist =
        match rangelist with
        | [range] -> ComplexRange       // ln(-1) is complex
        | _ -> FailExactArgCount "Function" 1 rangelist.Length funcToken

    member this.EvalConcept context funcToken argList =
        match argList with
        | [arg] -> 
            ExpressionConcept context arg |> VerifyDimensionlessArgument funcToken
            Dimensionless
        | _ -> FailExactArgCount "Function" 1 argList.Length funcToken

    member this.EvalNumeric context funcToken qlist =
        match qlist with
            | [PhysicalQuantity(number,concept) as quantity] -> 
                if IsQuantityZero quantity then
                    SyntaxError funcToken "Cannot evaluate ln(0)."
                else
                    VerifyDimensionlessArgument funcToken concept
                    match number with
                    | Rational(a,b) -> LnReal ((float a) / (float b))
                    | Real(x) -> LnReal x
                    | Complex(z) -> PhysicalQuantity(MakeComplex(complex.Log(z)), Dimensionless)
            | _ -> FailExactArgCount "Function" 1 qlist.Length funcToken

    member this.SimplifyStep context funcToken argList =
        match argList with
        | [arg] -> 
            if IsExpressionOne arg then
                AmountZero      // ln(1) = 0
            else 
                match arg with
                | Functor({Text="exp"}, [z]) when IsRealValuedExpression context z -> z   // ln(exp(z)) ==> z, but only for real z
                | _ -> Functor(funcToken, [arg])
        | _ -> FailExactArgCount "Function" 1 argList.Length funcToken

    member this.Differential derivKind context varNameList funcToken argList =
        // d(ln(z)) = dz/z
        match argList with
        | [z] ->
            let dz = TakeDifferential derivKind context varNameList z
            Divide dz z
        | _ -> FailExactArgCount "Function" 1 argList.Length funcToken
            
    member this.DistributeAcrossEquation context funcToken leftList rightList =
        SimpleEquationDistributor funcToken leftList rightList

    member this.LatexName = @"\ln"
}

let Function_Cos = { new IFunctionHandler with

    member this.EvalRange funcToken rangelist =
        match rangelist with
        | [range] ->
            match range with
            | IntegerRange(_,_) -> RealRange
            | RationalRange -> RealRange
            | RealRange -> RealRange
            | ComplexRange -> ComplexRange
        | _ -> FailExactArgCount "Function" 1 rangelist.Length funcToken

    member this.EvalConcept context funcToken argList =
        match argList with
        | [arg] -> 
            ExpressionConcept context arg |> VerifyDimensionlessArgument funcToken
            Dimensionless
        | _ -> FailExactArgCount "Function" 1 argList.Length funcToken

    member this.EvalNumeric context funcToken qlist =
        match qlist with
            | [PhysicalQuantity(number,concept) as quantity] -> 
                VerifyDimensionlessArgument funcToken concept
                if IsQuantityZero quantity then
                    QuantityOne
                else
                    match number with
                    | Rational(a,b) -> 
                        let x = (float a) / (float b)
                        PhysicalQuantity(MakeReal(System.Math.Cos(x)), Dimensionless)
                    | Real(x) -> 
                        PhysicalQuantity(MakeReal(System.Math.Cos(x)), Dimensionless)
                    | Complex(z) -> 
                        PhysicalQuantity(MakeComplex(complex.Cos(z)), Dimensionless)
            | _ -> FailExactArgCount "Function" 1 qlist.Length funcToken

    member this.SimplifyStep context funcToken argList =
        match argList with
        | [arg] -> 
            if IsExpressionZero arg then
                AmountOne      // cos(0) = 1
            else 
                Functor(funcToken, [arg])
        | _ -> FailExactArgCount "Function" 1 argList.Length funcToken

    member this.Differential derivKind context varNameList funcToken argList =
        // d(cos(z)) = -sin(z)dz
        match argList with
        | [z] ->
            let sin_z = MakeFunction "sin" [z]
            let dz = TakeDifferential derivKind context varNameList z
            Product[MakeNegative sin_z; dz]
        | _ -> FailExactArgCount "Function" 1 argList.Length funcToken
            
    member this.DistributeAcrossEquation context funcToken leftList rightList =
        SimpleEquationDistributor funcToken leftList rightList

    member this.LatexName = @"\cos"
}

let Function_Sin = { new IFunctionHandler with

    member this.EvalRange funcToken rangelist =
        match rangelist with
        | [range] ->
            match range with
            | IntegerRange(_,_) -> RealRange
            | RationalRange -> RealRange
            | RealRange -> RealRange
            | ComplexRange -> ComplexRange
        | _ -> FailExactArgCount "Function" 1 rangelist.Length funcToken

    member this.EvalConcept context funcToken argList =
        match argList with
        | [arg] -> 
            ExpressionConcept context arg |> VerifyDimensionlessArgument funcToken
            Dimensionless
        | _ -> FailExactArgCount "Function" 1 argList.Length funcToken

    member this.EvalNumeric context funcToken qlist =
        match qlist with
            | [PhysicalQuantity(number,concept) as quantity] -> 
                VerifyDimensionlessArgument funcToken concept
                if IsQuantityZero quantity then
                    QuantityZero
                else
                    match number with
                    | Rational(a,b) -> 
                        let x = (float a) / (float b)
                        PhysicalQuantity(MakeReal(System.Math.Sin(x)), Dimensionless)
                    | Real(x) -> 
                        PhysicalQuantity(MakeReal(System.Math.Sin(x)), Dimensionless)
                    | Complex(z) -> 
                        PhysicalQuantity(MakeComplex(complex.Sin(z)), Dimensionless)
            | _ -> FailExactArgCount "Function" 1 qlist.Length funcToken

    member this.SimplifyStep context funcToken argList =
        match argList with
        | [arg] -> 
            if IsExpressionZero arg then
                AmountZero      // sin(0) = 0
            else 
                Functor(funcToken, [arg])
        | _ -> FailExactArgCount "Function" 1 argList.Length funcToken

    member this.Differential derivKind context varNameList funcToken argList =
        // d(sin(z)) = cos(z)dz
        match argList with
        | [z] ->
            let cos_z = MakeFunction "cos" [z]
            let dz = TakeDifferential derivKind context varNameList z
            Product[cos_z; dz]
        | _ -> FailExactArgCount "Function" 1 argList.Length funcToken
            
    member this.DistributeAcrossEquation context funcToken leftList rightList =
        SimpleEquationDistributor funcToken leftList rightList

    member this.LatexName = @"\sin"
}

let Function_Uroot = { new IFunctionHandler with        // uroot(n) = exp((2*pi*i) / n), where n = 1, 2, 3, ...
    member this.EvalRange funcToken rangelist =
        // uroot argument must be a specific positive integer.
        // That is, the range include a single positive integer value.
        match rangelist with
        | [range] ->
            match range with
            | IntegerRange(FiniteLimit(lo), FiniteLimit(hi)) ->
                if (lo <> hi) || (lo.Sign <= 0) then
                    SyntaxError funcToken "Argument to uroot have a single positive integer value."
                elif lo.IsOne then
                    // uroot(1) = 1
                    IntegerRange(FiniteLimit(1I), FiniteLimit(1I))
                elif lo = 2I then
                    // uroot(2) = -1
                    IntegerRange(FiniteLimit(-1I), FiniteLimit(-1I))
                else
                    // uroot(3), uroot(4), uroot(5) are all complex
                    ComplexRange

            | _ -> SyntaxError funcToken "Argument to uroot must be a positive integer."
        | _ -> FailExactArgCount "Function" 1 rangelist.Length funcToken

    member this.EvalConcept context funcToken argList =
        match argList with
        | [arg] -> 
            ExpressionConcept context arg |> VerifyDimensionlessArgument funcToken
            Dimensionless
        | _ -> FailExactArgCount "Function" 1 argList.Length funcToken

    member this.EvalNumeric context funcToken qlist =
        match qlist with
            | [PhysicalQuantity(number,concept) as quantity] -> 
                VerifyDimensionlessArgument funcToken concept
                if IsQuantityZero quantity then
                    SyntaxError funcToken "uroot(0) is not defined."
                else
                    match number with
                    | Rational(a,b) -> 
                        if (not b.IsOne) || (a.Sign <= 0) then
                            SyntaxError funcToken "uroot must have a positive integer argument."
                        elif a = 1I then
                            QuantityOne
                        elif a = 2I then
                            QuantityNegOne
                        elif a = 4I then
                            // Not strictly necessary, but without this special case we get "sloppy" result:
                            //    Freefall:3> eval(uroot(4));
                            //    Statement: eval(uroot(4));
                            //    #2 := (6.12303176911189e-17+1.0i)
                            PhysicalQuantity(Complex(complex.ImaginaryOne), Dimensionless)
                        else
                            // uroot(n) = exp((2*pi*i) / n)
                            let z = complex(0.0, 2.0 * System.Math.PI / (float a))
                            PhysicalQuantity(MakeComplex(complex.Exp(z)), Dimensionless)
                    | _ ->
                        SyntaxError funcToken "uroot must have a positive integer argument."
            | _ -> FailExactArgCount "Function" 1 qlist.Length funcToken

    member this.SimplifyStep context funcToken argList =
        match argList with
        | [Amount(PhysicalQuantity(number, concept) as quantity) as arg] ->
            VerifyDimensionlessArgument funcToken concept
            if IsQuantityZero quantity then
                SyntaxError funcToken "uroot(0) is not defined."
            else
                match number with
                | Rational(a,b) -> 
                    if (b <> 1I) || (a.Sign <= 0) then
                        SyntaxError funcToken "uroot must have a positive integer argument."
                    elif a = 1I then
                        AmountOne
                    elif a = 2I then
                        AmountNegOne
                    else                        
                        Functor(funcToken, [arg])   // uroot(n) = exp((2*pi*i) / n), so do not simplify
                | _ ->
                    SyntaxError funcToken "uroot must have a positive integer argument."
        | _ -> FailExactArgCount "Function" 1 argList.Length funcToken

    member this.Differential derivKind context varNameList funcToken argList =
        // uroot(n) is a constant, so the derivative is always 0.
        match argList with
        | [_] -> AmountZero
        | _ -> FailExactArgCount "Function" 1 argList.Length funcToken
            
    member this.DistributeAcrossEquation context funcToken leftList rightList =
        SyntaxError funcToken "uroot does not distribute across equations."

    member this.LatexName = @"\mathrm{uroot}"
}

(*
let Function_Template = { new IFunctionHandler with
    member this.EvalRange funcToken rangelist = failwith "not implemented"
    member this.EvalConcept context funcToken argList = failwith "not implemented"
    member this.EvalNumeric context funcToken qlist = failwith "not implemented"
    member this.SimplifyStep context funcToken argList = failwith "not implemented"
    member this.Differential derivKind context varNameList funcToken argList = failwith "not implemented"
    member this.DistributeAcrossEquation context funcToken leftList rightList = failwith "not implemented"
    member this.LatexName = @"\name"
}
*)

let AcosReal x =
    if -1.0 <= x && x <= +1.0 then
        PhysicalQuantity(MakeReal(System.Math.Acos(x)), Dimensionless)
    else
        PhysicalQuantity(MakeComplex(complex.Acos(complex(x,0.0))), Dimensionless)

let Function_Acos = { new IFunctionHandler with
    member this.EvalRange funcToken rangelist = 
        match rangelist with
        | [argRange] ->
            match argRange with
            | IntegerRange(FiniteLimit(lo), FiniteLimit(hi)) when lo = 1I && hi = 1I -> 
                IntegerRange(FiniteLimit(0I), FiniteLimit(0I))      // acos(1) = 0

            | IntegerRange(FiniteLimit(lo), FiniteLimit(hi)) when -1I <= lo && lo <= hi && hi <= 1I -> 
                RealRange       // acos(x) is real when x is real and -1 <= x <= +1

            | IntegerRange(_, _)
            | RationalRange
            | RealRange
            | ComplexRange ->
                ComplexRange
        | _ -> FailExactArgCount "Function" 1 rangelist.Length funcToken

    member this.EvalConcept context funcToken argList =
        match argList with
        | [arg] -> 
            ExpressionConcept context arg |> VerifyDimensionlessArgument funcToken
            Dimensionless
        | _ -> FailExactArgCount "Function" 1 argList.Length funcToken

    member this.EvalNumeric context funcToken qlist =
        match qlist with
        | [PhysicalQuantity(number,concept)] ->
            VerifyDimensionlessArgument funcToken concept
            match number with
            | Rational(a,b) -> AcosReal ((float a) / (float b))
            | Real(x) -> AcosReal x
            | Complex(z) -> PhysicalQuantity(MakeComplex(complex.Acos(z)), Dimensionless)
        | _ -> FailExactArgCount "Function" 1 qlist.Length funcToken

    member this.SimplifyStep context funcToken argList = 
        match argList with
        | [Amount(PhysicalQuantity(number,concept))] ->
            VerifyDimensionlessArgument funcToken concept
            if IsNumberEqualToInteger -1I number then
                SymbolPi                                // acos(-1) = pi
            elif IsNumberZero number then
                Product [AmountOneHalf; SymbolPi]       // acos(0)  = pi/2
            elif IsNumberEqualToInteger 1I number then
                AmountZero                              // acos(+1) = 0
            else
                Functor(funcToken, argList)

        | [arg] ->
            Functor(funcToken, argList)

        | _ -> FailExactArgCount "Function" 1 argList.Length funcToken

    member this.Differential derivKind context varNameList funcToken argList =
        match argList with
        | [z] ->
            // d acos(z) = -dz / sqrt(1 - z^2)
            let dz = TakeDifferential derivKind context varNameList z
            Product [MakeNegative dz; RecipSqrt (Sum[AmountOne; MakeNegative (Square z)])]

        | _ -> FailExactArgCount "Function" 1 argList.Length funcToken

    member this.DistributeAcrossEquation context funcToken leftList rightList =
        SimpleEquationDistributor funcToken leftList rightList

    member this.LatexName = @"\cos^{-1}"
}

let AsinReal x =
    if -1.0 <= x && x <= +1.0 then
        PhysicalQuantity(MakeReal(System.Math.Asin(x)), Dimensionless)
    else
        PhysicalQuantity(MakeComplex(complex.Asin(complex(x,0.0))), Dimensionless)

let Function_Asin = { new IFunctionHandler with
    member this.EvalRange funcToken rangelist = 
        match rangelist with
        | [argRange] ->
            match argRange with
            | IntegerRange(FiniteLimit(lo), FiniteLimit(hi)) when lo = 0I && hi = 0I -> 
                IntegerRange(FiniteLimit(0I), FiniteLimit(0I))      // asin(0) = 0

            | IntegerRange(FiniteLimit(lo), FiniteLimit(hi)) when -1I <= lo && lo <= hi && hi <= 1I -> 
                RealRange       // asin(x) is real when x is real and -1 <= x <= +1

            | IntegerRange(_, _)
            | RationalRange
            | RealRange
            | ComplexRange ->
                ComplexRange
        | _ -> FailExactArgCount "Function" 1 rangelist.Length funcToken

    member this.EvalConcept context funcToken argList =
        match argList with
        | [arg] -> 
            ExpressionConcept context arg |> VerifyDimensionlessArgument funcToken
            Dimensionless
        | _ -> FailExactArgCount "Function" 1 argList.Length funcToken

    member this.EvalNumeric context funcToken qlist =
        match qlist with
        | [PhysicalQuantity(number,concept)] ->
            VerifyDimensionlessArgument funcToken concept
            match number with
            | Rational(a,b) -> AsinReal ((float a) / (float b))
            | Real(x) -> AsinReal x
            | Complex(z) -> PhysicalQuantity(MakeComplex(complex.Asin(z)), Dimensionless)
        | _ -> FailExactArgCount "Function" 1 qlist.Length funcToken

    member this.SimplifyStep context funcToken argList = 
        match argList with
        | [Amount(PhysicalQuantity(number,concept))] ->
            VerifyDimensionlessArgument funcToken concept
            if IsNumberEqualToInteger -1I number then
                Product [AmountNegOneHalf; SymbolPi]    // asin(-1) = -pi/2
            elif IsNumberZero number then
                AmountZero                              // asin(0)  = 0
            elif IsNumberEqualToInteger 1I number then
                Product [AmountOneHalf; SymbolPi]       // asin(+1) = pi/2
            else
                Functor(funcToken, argList)

        | [arg] ->
            Functor(funcToken, argList)

        | _ -> FailExactArgCount "Function" 1 argList.Length funcToken

    member this.Differential derivKind context varNameList funcToken argList =
        match argList with
        | [z] ->
            // d asin(z) = dz / sqrt(1 - z^2)
            let dz = TakeDifferential derivKind context varNameList z
            Product [dz; RecipSqrt (Sum[AmountOne; MakeNegative (Square z)])]

        | _ -> FailExactArgCount "Function" 1 argList.Length funcToken

    member this.DistributeAcrossEquation context funcToken leftList rightList =
        SimpleEquationDistributor funcToken leftList rightList

    member this.LatexName = @"\sin^{-1}"
}

let IntrinsicFunctions = 
    [
        ("acos",    Function_Acos)
        ("asin",    Function_Asin)
        ("cos",     Function_Cos)
        ("exp",     Function_Exp)
        ("ln",      Function_Ln)
        ("sin",     Function_Sin)
        ("uroot",   Function_Uroot)
    ]

//-------------------------------------------------------------------------------------------------
// Parse a string and evaluate it as a concept.

let EvaluateConceptDefinition context definition =
    // Split the definition string into tokens
    let expr, emptyScan = TokenizeLine definition |> ParseExpression
    match emptyScan with
    | badtoken :: _ -> SyntaxError badtoken (sprintf "Syntax error in definition '%s'" definition)
    | [] -> EvalConcept context expr

//-------------------------------------------------------------------------------------------------

let RunStandardScript context filename =
    let envvar = "FREEFALL_STANDARD_PATH"
    match System.Environment.GetEnvironmentVariable(envvar) with
    | null -> 
        failwith (sprintf "Must set environment variable %s to path of Freefall standard files like %s" envvar filename)
    | path ->
        let filepath = System.IO.Path.Combine(path, filename)
        let mutable scan = TokenizeFile filepath
        while MoreTokensIn scan do
            let firstTokenInStatement, statement, scan2 = ParseStatement scan
            ExecuteStatement context firstTokenInStatement statement false
            scan <- scan2

//-------------------------------------------------------------------------------------------------
// Create a context with intrinsic symbols built it.
// Execute initialization script to define certain units, concepts, etc.

let MakeContext assignmentHook probeHook saveHook decompHook = 
    let context = {
        SymbolTable = new Dictionary<string, SymbolEntry>()
        NumberedExpressionList = new ResizeArray<Expression>()
        AssignmentHook = assignmentHook
        ProbeHook = probeHook
        SaveToFile = saveHook
        DecomposeHook = decompHook
        NextConstantSubscript = ref 0
        FirstTokenInExecutingStatement = ref (EndOfFileToken None)
    }

    // e and pi must be built-in because they are needed for certain built-in simplifiers.
    DefineIntrinsicSymbol context "pi" (UnitEntry(PhysicalQuantity(Real(System.Math.PI), Dimensionless)))
    DefineIntrinsicSymbol context "e"  (UnitEntry(PhysicalQuantity(Real(System.Math.E),  Dimensionless)))

    for {ConceptName=conceptName; BaseUnitName=baseUnitName; ConceptValue=concept} in BaseConcepts do
        DefineIntrinsicSymbol context conceptName (ConceptEntry(concept))
        DefineIntrinsicSymbol context baseUnitName (UnitEntry(PhysicalQuantity(Rational(R1), concept)))

    for macroName, argBehavior, macroFunc in IntrinsicMacros do
        DefineIntrinsicSymbol context macroName (MacroEntry({Expander=(macroFunc context); ArgBehavior=argBehavior}))

    for funcName, handler in IntrinsicFunctions do
        DefineIntrinsicSymbol context funcName (FunctionEntry(handler))

    context

let InitContext context =
    // Execute standard library's initialization script init.ff.
    // Use environment variable to figure out where the standard scripts are.
    RunStandardScript context "init.ff"
