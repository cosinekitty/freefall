module Freefall.Intrinsic

open System.Collections.Generic

open Freefall.Scanner
open Freefall.Expr
open Freefall.Stmt
open Freefall.Parser

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

type DerivedConceptEntry = {
    ConceptName: string;
    Definition: string;         // for convenience, a parsed string defined in terms of any previous concepts, whether base or derived.
}

let DerivedConcepts = [
    {ConceptName="speed"; Definition="distance/time"};
]

//-------------------------------------------------------------------------------------------------
// Create a context with intrinsic symbols built it.

let EvaluateDefinition context definition =
    // Split the definition string into tokens
    let expr, emptyScan = TokenizeLine definition |> ParseExpression
    match emptyScan with
    | badtoken :: _ -> failwith (sprintf "Syntax error in definition '%s'" definition)
    | [] -> EvalConcept context expr

let MakeContext assignmentHook = 
    let context = {
        SymbolTable = new Dictionary<string, SymbolEntry>();
        NumberedExpressionList = new ResizeArray<Expression>();
        AssignmentHook = assignmentHook;
    }

    for {ConceptName=conceptName; BaseUnitName=baseUnitName; ConceptValue=concept} in BaseConcepts do
        DefineIntrinsicSymbol context conceptName (ConceptEntry(concept))
        DefineIntrinsicSymbol context baseUnitName (UnitEntry(PhysicalQuantity(Rational(1L,1L), concept)))

    for {ConceptName=conceptName; Definition=definition} in DerivedConcepts do
        DefineIntrinsicSymbol context conceptName (ConceptEntry(EvaluateDefinition context definition))

    for macroName, macroFunc in IntrinsicMacros do
        DefineIntrinsicSymbol context macroName (MacroEntry({Expander=(macroFunc context);}))

    for funcName, concepter, stepSimplifier in IntrinsicFunctions do
        DefineIntrinsicSymbol context funcName (FunctionEntry{Concepter=(concepter context); StepSimplifier=(stepSimplifier context);})

    context

