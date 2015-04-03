﻿module Freefall.Stmt
open Scanner
open Expr

//--------------------------------------------------------------------------------------------------

type MultiVariableDeclaration = {
    VarNameList : Token list;
    Range : NumericRange;
    ConceptExpr : Expression;
}

type AssignmentStatement = {
    TargetName : Token option;      // the optional user-specified name by which the entire expression should be known later
    Expr : Expression;
}

type Statement =
    | VarDecl of MultiVariableDeclaration
    | Assignment of AssignmentStatement
    | DoNothing

//--------------------------------------------------------------------------------------------------

let VarNameFolder accum vartoken =
    if accum = "" then
        vartoken.Text
    else
        accum + ", " + vartoken.Text


let FormatStatement statement =
    match statement with

    | VarDecl {VarNameList=vlist; Range=range; ConceptExpr=conceptExpr;} ->
        let varNamesText = List.fold VarNameFolder "" vlist
        let rangeText = RangeName range
        let conceptText = FormatExpression conceptExpr
        let typeText =
            if conceptText = "1" then
                rangeText
            else
                rangeText + " " + conceptText
        "var " + varNamesText + ": " + typeText + ";"

    | Assignment {TargetName=None; Expr=expr;} ->
        (FormatExpression expr) + ";"

    | Assignment {TargetName=Some(target); Expr=expr;} ->
        target.Text + " := " + (FormatExpression expr) + ";"

    | DoNothing ->
        ";"

//--------------------------------------------------------------------------------------------------

let rec ExpandMacros context rawexpr =
    match rawexpr with
    | Amount(_) -> rawexpr
    | Solitaire(nameToken) -> 
        match FindSymbolEntry context nameToken with
        | VariableEntry(_) -> rawexpr
        | ConceptEntry(_) -> rawexpr
        | UnitEntry(_) -> rawexpr
        | AssignmentEntry(expr) -> expr
    | FunctionCall(funcName,argList) -> rawexpr     // FIXFIXFIX - check for macros when we start implementing them
    | Negative(arg) -> Negative(ExpandMacros context arg)
    | Reciprocal(arg) -> Reciprocal(ExpandMacros context arg)
    | Sum(terms) -> Sum(List.map (ExpandMacros context) terms)
    | Product(factors) -> Product(List.map (ExpandMacros context) factors)
    | Power(a,b) -> Power((ExpandMacros context a), (ExpandMacros context b))
    | Equals(a,b) -> Equals((ExpandMacros context a), (ExpandMacros context b))
    | NumExprRef(index) -> FindNumberedExpression context index
    | PrevExprRef -> FindPreviousExpression context

//--------------------------------------------------------------------------------------------------

let ExecuteStatement context statement =
    match statement with

    | VarDecl {VarNameList=vlist; Range=range; ConceptExpr=conceptExpr;} ->
        let concept = ExpressionConcept context conceptExpr
        for vname in vlist do
            DefineSymbol context vname (VariableEntry(range,concept))
    
    | Assignment {TargetName=None; Expr=rawexpr;} ->
        let expr = ExpandMacros context rawexpr
        printfn "ExpandMacros (1) ==> %s" (FormatExpression expr)       //!!!!!!!!!!!!!!!
        ValidateExpressionConcept context expr
        AppendNumberedExpression context expr

    | Assignment {TargetName=Some(assignToken); Expr=rawexpr;} ->
        let expr = ExpandMacros context rawexpr
        printfn "ExpandMacros (2) ==> %s" (FormatExpression expr)       //!!!!!!!!!!!!!!!
        ValidateExpressionConcept context expr
        DefineSymbol context assignToken (AssignmentEntry(expr))
        AppendNumberedExpression context expr

    | DoNothing ->
        ()