module Freefall.Intrinsic

open System.Collections.Generic
open System.Numerics

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

let SimplifyMacroExpander context macroToken argList =
    match argList with
    | [arg] -> Simplify context arg
    | _ -> FailSingleArgMacro macroToken argList

let EvalMacroExpander context macroToken argList =
    match argList with
    | [arg] -> Amount(EvalQuantity context arg)
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

let DerivMacroExpander context macroToken argList =
    // deriv(expr, var1, ...)
    // First variable is required, as it is the "primary" variable.
    // Any others are treated as functions of the first variable.
    match argList with
    | expr :: var1expr :: rest ->
        let var1token = DiffVariableToken context var1expr
        let restnames = List.map (DiffVariableName context) rest
        let diff = TakeDifferential context (var1token.Text :: restnames) expr
        match diff with
        | Equals(ldiff,rdiff) ->
            // Taking the derivative of an equation requires both sides to be handled separately.
            let lderiv = Product([ldiff; Reciprocal(Del(var1token,1))])
            let rderiv = Product([rdiff; Reciprocal(Del(var1token,1))])
            let lsimp = Simplify context lderiv
            let rsimp = Simplify context rderiv
            Equals(lsimp,rsimp)
        | _ ->
            let deriv = Product([diff; Reciprocal(Del(var1token,1))])
            Simplify context deriv
    | _ -> SyntaxError macroToken (sprintf "Expected '%s(expr, var {, ...})'" macroToken.Text)

let DifferentialMacroExpander context macroToken argList =
    // diff(expr, vars...)
    match argList with
    | [] -> SyntaxError macroToken (sprintf "Expected %s(expr, vars...)" macroToken.Text)
    | [expr] -> SyntaxError macroToken "Must have at least one variable after 'diff(expr,'"
    | expr :: varlist ->
        let varnames = List.map (DiffVariableName context) varlist
        TakeDifferential context varnames expr |> Simplify context

let AssertIdenticalMacroExpander context macroToken argList =
    // asserti(expr1,expr2)
    match argList with
    | [expr1; expr2] ->
        if AreIdentical context expr1 expr2 then
            expr1       // All macros have to return some expression, so we choose the left expression.
        else
            SyntaxError macroToken (sprintf "Expressions are not identical:\n%s\n%s" (FormatExpression expr1) (FormatExpression expr2))
    | _ -> SyntaxError macroToken (sprintf "%s requires exactly 2 expression arguments." macroToken.Text)

let IntrinsicMacros =
    [
        ("asserti", AssertIdenticalMacroExpander);
        ("deriv",   DerivMacroExpander);
        ("diff",    DifferentialMacroExpander);
        ("eval",    EvalMacroExpander);
        ("simp",    SimplifyMacroExpander);
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
            | IntegerRange -> RealRange
            | RationalRange -> RealRange
            | RealRange -> RealRange
            | ComplexRange -> ComplexRange
        | _ -> FailExactArgCount "Function" 1 rangelist.Length funcToken

    member this.EvalConcept context funcToken argList =
        match argList with
        | [arg] -> 
            let argConcept = ExpressionConcept context arg
            if IsConceptDimensionless argConcept then
                Dimensionless
            else
                SyntaxError funcToken ("exp() requires a dimensionless argument, but found " + FormatConcept argConcept)
        | _ -> FailExactArgCount "Function" 1 argList.Length funcToken

    member this.EvalNumeric context funcToken qlist =
        match qlist with
            | [PhysicalQuantity(number,concept)] -> 
                if (IsNumberZero number) || (concept = Zero) then
                    Unity
                elif concept <> Dimensionless then
                    SyntaxError funcToken ("exp() requires a dimensionless argument, but found " + FormatConcept concept)
                else
                    match number with
                    | Rational(a,b) -> 
                        let expx = (System.Math.Exp((float a)/(float b)))
                        PhysicalQuantity(Real(expx), Dimensionless)

                    | Real(x) -> 
                        let expx = System.Math.Exp(x)
                        PhysicalQuantity(Real(expx), Dimensionless)

                    | Complex(z) ->
                        PhysicalQuantity(Complex(Complex.Exp(z)), Dimensionless)
            | _ -> FailExactArgCount "Function" 1 qlist.Length funcToken

    member this.SimplifyStep context funcToken argList =
        match argList with
        | [arg] -> 
            if IsZeroExpression arg then
                UnityAmount
            else 
                Functor(funcToken, [arg])
        | _ -> FailExactArgCount "Function" 1 argList.Length funcToken

    member this.Differential context varNameList funcToken argList =
        // d(exp(z)) = exp(z) dz
        match argList with
        | [arg] ->
            let dz = TakeDifferential context varNameList arg
            let exp_z = Functor(funcToken, argList)
            Product[exp_z; dz]
        | _ -> FailExactArgCount "Function" 1 argList.Length funcToken
            
    member this.DistributeAcrossEquation context funcToken leftList rightList =
        SimpleEquationDistributor funcToken leftList rightList
}

let LnReal x =
    if x < 0.0 then
        PhysicalQuantity(Complex(Complex.Log(new Complex(x, 0.0))), Dimensionless)
    else
        PhysicalQuantity(Real(System.Math.Log(x)), Dimensionless)

let Function_Ln = { new IFunctionHandler with

    member this.EvalRange funcToken rangelist =
        match rangelist with
        | [range] -> ComplexRange       // ln(-1) is complex
        | _ -> FailExactArgCount "Function" 1 rangelist.Length funcToken

    member this.EvalConcept context funcToken argList =
        match argList with
        | [arg] -> 
            let argConcept = ExpressionConcept context arg
            if IsConceptDimensionless argConcept then
                Dimensionless
            else
                SyntaxError funcToken ("ln() requires a dimensionless argument, but found " + FormatConcept argConcept)
        | _ -> FailExactArgCount "Function" 1 argList.Length funcToken

    member this.EvalNumeric context funcToken qlist =
        match qlist with
            | [PhysicalQuantity(number,concept)] -> 
                if (IsNumberZero number) || (concept = Zero) then
                    SyntaxError funcToken "Cannot evaluate ln(0)."
                elif concept <> Dimensionless then
                    SyntaxError funcToken ("ln() requires a dimensionless argument, but found " + FormatConcept concept)
                else
                    match number with
                    | Rational(a,b) -> LnReal ((float a) / (float b))
                    | Real(x) -> LnReal x
                    | Complex(z) -> PhysicalQuantity(Complex(Complex.Log(z)), Dimensionless)
            | _ -> FailExactArgCount "Function" 1 qlist.Length funcToken

    member this.SimplifyStep context funcToken argList =
        match argList with
        | [arg] -> 
            if IsUnityExpression arg then
                ZeroAmount      // ln(1) = 0
            else 
                match arg with
                | Functor({Text="exp"}, [z]) -> z     // ln(exp(z)) ==> z
                | _ -> Functor(funcToken, [arg])
        | _ -> FailExactArgCount "Function" 1 argList.Length funcToken

    member this.Differential context varNameList funcToken argList =
        // d(ln(z)) = dz/z
        match argList with
        | [z] ->
            let dz = TakeDifferential context varNameList z
            Product[dz; Reciprocal(z)]
        | _ -> FailExactArgCount "Function" 1 argList.Length funcToken
            
    member this.DistributeAcrossEquation context funcToken leftList rightList =
        SimpleEquationDistributor funcToken leftList rightList
}

let Function_Cos = { new IFunctionHandler with

    member this.EvalRange funcToken rangelist =
        match rangelist with
        | [range] ->
            match range with
            | IntegerRange -> RealRange
            | RationalRange -> RealRange
            | RealRange -> RealRange
            | ComplexRange -> ComplexRange
        | _ -> FailExactArgCount "Function" 1 rangelist.Length funcToken

    member this.EvalConcept context funcToken argList =
        match argList with
        | [arg] -> 
            let argConcept = ExpressionConcept context arg
            if IsConceptDimensionless argConcept then
                Dimensionless
            else
                SyntaxError funcToken ("cos() requires a dimensionless argument, but found " + FormatConcept argConcept)
        | _ -> FailExactArgCount "Function" 1 argList.Length funcToken

    member this.EvalNumeric context funcToken qlist =
        match qlist with
            | [PhysicalQuantity(number,concept)] -> 
                if (IsNumberZero number) || (concept = Zero) then
                    Unity
                elif concept <> Dimensionless then
                    SyntaxError funcToken ("cos() requires a dimensionless argument, but found " + FormatConcept concept)
                else
                    match number with
                    | Rational(a,b) -> 
                        let x = (float a) / (float b)
                        PhysicalQuantity(Real(System.Math.Cos(x)), Dimensionless)
                    | Real(x) -> 
                        PhysicalQuantity(Real(System.Math.Cos(x)), Dimensionless)
                    | Complex(z) -> 
                        PhysicalQuantity(Complex(Complex.Cos(z)), Dimensionless)
            | _ -> FailExactArgCount "Function" 1 qlist.Length funcToken

    member this.SimplifyStep context funcToken argList =
        match argList with
        | [arg] -> 
            if IsZeroExpression arg then
                UnityAmount      // cos(0) = 1
            else 
                Functor(funcToken, [arg])
        | _ -> FailExactArgCount "Function" 1 argList.Length funcToken

    member this.Differential context varNameList funcToken argList =
        // d(cos(z)) = -sin(z)dz
        match argList with
        | [z] ->
            let sin_z = MakeFunction "sin" [z]
            let dz = TakeDifferential context varNameList z
            Product[Negative(sin_z); dz]
        | _ -> FailExactArgCount "Function" 1 argList.Length funcToken
            
    member this.DistributeAcrossEquation context funcToken leftList rightList =
        SimpleEquationDistributor funcToken leftList rightList
}

let Function_Sin = { new IFunctionHandler with

    member this.EvalRange funcToken rangelist =
        match rangelist with
        | [range] ->
            match range with
            | IntegerRange -> RealRange
            | RationalRange -> RealRange
            | RealRange -> RealRange
            | ComplexRange -> ComplexRange
        | _ -> FailExactArgCount "Function" 1 rangelist.Length funcToken

    member this.EvalConcept context funcToken argList =
        match argList with
        | [arg] -> 
            let argConcept = ExpressionConcept context arg
            if IsConceptDimensionless argConcept then
                Dimensionless
            else
                SyntaxError funcToken ("sin() requires a dimensionless argument, but found " + FormatConcept argConcept)
        | _ -> FailExactArgCount "Function" 1 argList.Length funcToken

    member this.EvalNumeric context funcToken qlist =
        match qlist with
            | [PhysicalQuantity(number,concept)] -> 
                if (IsNumberZero number) || (concept = Zero) then
                    ZeroQuantity
                elif concept <> Dimensionless then
                    SyntaxError funcToken ("sin() requires a dimensionless argument, but found " + FormatConcept concept)
                else
                    match number with
                    | Rational(a,b) -> 
                        let x = (float a) / (float b)
                        PhysicalQuantity(Real(System.Math.Sin(x)), Dimensionless)
                    | Real(x) -> 
                        PhysicalQuantity(Real(System.Math.Sin(x)), Dimensionless)
                    | Complex(z) -> 
                        PhysicalQuantity(Complex(Complex.Sin(z)), Dimensionless)
            | _ -> FailExactArgCount "Function" 1 qlist.Length funcToken

    member this.SimplifyStep context funcToken argList =
        match argList with
        | [arg] -> 
            if IsZeroExpression arg then
                ZeroAmount      // sin(0) = 0
            else 
                Functor(funcToken, [arg])
        | _ -> FailExactArgCount "Function" 1 argList.Length funcToken

    member this.Differential context varNameList funcToken argList =
        // d(sin(z)) = cos(z)dz
        match argList with
        | [z] ->
            let cos_z = MakeFunction "cos" [z]
            let dz = TakeDifferential context varNameList z
            Product[cos_z; dz]
        | _ -> FailExactArgCount "Function" 1 argList.Length funcToken
            
    member this.DistributeAcrossEquation context funcToken leftList rightList =
        SimpleEquationDistributor funcToken leftList rightList
}

let IntrinsicFunctions = 
    [
        ("cos", Function_Cos);
        ("exp", Function_Exp);
        ("ln",  Function_Ln);
        ("sin", Function_Sin);
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

let MakeContext assignmentHook probeHook = 
    let context = {
        SymbolTable = new Dictionary<string, SymbolEntry>()
        NumberedExpressionList = new ResizeArray<Expression>()
        AssignmentHook = assignmentHook
        ProbeHook = probeHook
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

