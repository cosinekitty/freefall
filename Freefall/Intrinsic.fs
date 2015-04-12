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
        let deriv = Product([diff; Reciprocal(Del(var1token,1))])
        Simplify context deriv
    | _ -> SyntaxError macroToken "Expected 'deriv(expr, var {, ...})'"

let DifferentialMacroExpander context macroToken argList =
    // diff(expr, vars...)
    match argList with
    | [] -> SyntaxError macroToken "Expected diff(expr, vars...)"
    | [expr] -> SyntaxError macroToken "Must have at least one variable after 'diff(expr,'"
    | expr :: varlist ->
        let varnames = List.map (DiffVariableName context) varlist
        TakeDifferential context varnames expr |> Simplify context

let IntrinsicMacros =
    [
        ("deriv", DerivMacroExpander);
        ("diff", DifferentialMacroExpander);
        ("eval", EvalMacroExpander);
        ("simp", SimplifyMacroExpander);
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

let IntrinsicFunctions = 
    [
        ("exp", Function_Exp);
    ]

//-------------------------------------------------------------------------------------------------

type DerivedConceptEntry = {
    ConceptName: string;
    Definition: string;         // for convenience, a parsed string defined in terms of any previous concepts, whether base or derived.
}

let DerivedConcepts = [
    {ConceptName="speed";           Definition="distance/time"};
    {ConceptName="acceleration";    Definition="speed/time"};
    {ConceptName="force";           Definition="mass*acceleration"};
    {ConceptName="energy";          Definition="force*distance"};
    {ConceptName="frequency";       Definition="1/time"};
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
// Create a context with intrinsic symbols built it.

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

    for {ConceptName=conceptName; Definition=definition} in DerivedConcepts do
        DefineIntrinsicSymbol context conceptName (ConceptEntry(EvaluateConceptDefinition context definition))

    for macroName, macroFunc in IntrinsicMacros do
        DefineIntrinsicSymbol context macroName (MacroEntry({Expander=(macroFunc context);}))

    for funcName, handler in IntrinsicFunctions do
        DefineIntrinsicSymbol context funcName (FunctionEntry(handler))

    context

