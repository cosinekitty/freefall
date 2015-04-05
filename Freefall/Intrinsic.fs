﻿module Freefall.Intrinsic

open System.Collections.Generic

open Freefall.Scanner
open Freefall.Expr
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

let IntrinsicMacros =
    [
        ("eval", EvalMacroExpander);
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
            SyntaxError funcToken ("exp() requires a dimensionless argument, but found " + FormatConcept argConcept)
    | _ -> FailExactArgCount "Function" 1 argList.Length funcToken

let SimplifyStep_Exp context funcToken argList =        // caller will step-simplify argList for us.
    match argList with
    | [arg] -> 
        if IsZeroExpression arg then
            UnityAmount
        else 
            Functor(funcToken, [arg])
    | _ -> FailExactArgCount "Function" 1 argList.Length funcToken

let Evaluate_Exp context funcToken qlist =
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

            | Complex(x,y) ->
                // exp(x + iy) = exp(x)*exp(iy) = exp(x)*(cos(y) + i*sin(y))
                let expx = System.Math.Exp(x)
                let cosy = System.Math.Cos(y)
                let siny = System.Math.Sin(y)
                PhysicalQuantity(Complex(expx*cosy, expx*siny), Dimensionless)
    | _ -> FailExactArgCount "Function" 1 qlist.Length funcToken

let IntrinsicFunctions = 
    [
        ("exp", Concept_Exp, SimplifyStep_Exp, Evaluate_Exp);
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
        DefineIntrinsicSymbol context conceptName (ConceptEntry(EvaluateConceptDefinition context definition))

    for macroName, macroFunc in IntrinsicMacros do
        DefineIntrinsicSymbol context macroName (MacroEntry({Expander=(macroFunc context);}))

    for funcName, concepter, stepSimplifier, evaluator in IntrinsicFunctions do
        DefineIntrinsicSymbol context funcName 
            (FunctionEntry {
                Concepter=(concepter context); 
                StepSimplifier=(stepSimplifier context);
                Evaluator=(evaluator context);
            })

    context

