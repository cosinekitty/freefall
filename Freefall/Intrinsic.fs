﻿module Freefall.Intrinsic

open System.Collections.Generic

open Freefall.Scanner
open Freefall.Expr
open Freefall.Calculus
open Freefall.Stmt
open Freefall.Parser

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

let IntrinsicMacros =
    [
        ("asserti", AssertIdenticalMacroExpander)
        ("cbrt",    PowerMacroExpander AmountOneThird)
        ("deriv",   DiffDerivMacroExpander Derivative)
        ("diff",    DiffDerivMacroExpander Differential)
        ("eval",    EvalMacroExpander)
        ("float",   FloatMacroExpander)
        ("simp",    SimplifyMacroExpander)
        ("sqrt",    PowerMacroExpander AmountOneHalf)
        ("square",  PowerMacroExpander AmountTwo)
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

    member this.LatexName = "\\exp"
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
                | Functor({Text="exp"}, [z]) -> z     // ln(exp(z)) ==> z
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

    member this.LatexName = "\\ln"
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

    member this.LatexName = "\\cos"
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

    member this.LatexName = "\\sin"
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

    member this.LatexName = "\\mathrm{uroot}"
}

let IntrinsicFunctions = 
    [
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
            let statement, scan2 = ParseStatement scan
            ExecuteStatement context statement false
            scan <- scan2

//-------------------------------------------------------------------------------------------------
// Create a context with intrinsic symbols built it.
// Execute initialization script to define certain units, concepts, etc.

let MakeContext assignmentHook probeHook saveHook = 
    let context = {
        SymbolTable = new Dictionary<string, SymbolEntry>()
        NumberedExpressionList = new ResizeArray<Expression>()
        AssignmentHook = assignmentHook
        ProbeHook = probeHook
        SaveToFile = saveHook
        NextConstantSubscript = ref 0
    }

    for {ConceptName=conceptName; BaseUnitName=baseUnitName; ConceptValue=concept} in BaseConcepts do
        DefineIntrinsicSymbol context conceptName (ConceptEntry(concept))
        DefineIntrinsicSymbol context baseUnitName (UnitEntry(PhysicalQuantity(Rational(R1), concept)))

    for macroName, macroFunc in IntrinsicMacros do
        DefineIntrinsicSymbol context macroName (MacroEntry({Expander=(macroFunc context);}))

    for funcName, handler in IntrinsicFunctions do
        DefineIntrinsicSymbol context funcName (FunctionEntry(handler))

    // Execute standard library's initialization script init.ff.
    // Use environment variable to figure out where the standard scripts are.
    RunStandardScript context "init.ff"

    context

