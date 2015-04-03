module Freefall.Stmt
open Scanner
open Expr

//--------------------------------------------------------------------------------------------------

type MultiVariableDeclaration = {
    VarNameList : list<Token>;
    Range : NumericRange;
    ConceptExpr : Expression;
}

type AssignmentStatement = {
    TargetName : option<Token>;      // the optional user-specified name by which the entire expression should be known later
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

let FailNonFuncMacro token expected =
    raise (SyntaxException((sprintf "This symbol is %s, but is being as if it were a function or macro." expected), token))

let rec ExpandMacros context rawexpr =
    match rawexpr with
    | Amount(_) -> rawexpr
    | Solitaire(nameToken) -> 
        match FindSymbolEntry context nameToken with
        | VariableEntry(_) -> rawexpr
        | ConceptEntry(_) -> rawexpr
        | UnitEntry(_) -> rawexpr
        | AssignmentEntry(expr) -> expr
        | MacroEntry(_) -> raise (SyntaxException("Cannot use macro name as solitary symbol.", nameToken))
    | FunctionCall(funcName,argList) -> 
        // Look up function name in the context to see if it is actually a macro name.
        match FindSymbolEntry context funcName with
        | MacroEntry({Expander=expander;}) -> expander funcName (List.map (ExpandMacros context) argList)
        | VariableEntry(_) -> FailNonFuncMacro funcName "a variable"
        | ConceptEntry(_) -> FailNonFuncMacro funcName "a concept"
        | UnitEntry(_) -> FailNonFuncMacro funcName "a unit"
        | AssignmentEntry(_) -> FailNonFuncMacro funcName "an assignment target"
    | Negative(arg) -> Negative(ExpandMacros context arg)
    | Reciprocal(arg) -> Reciprocal(ExpandMacros context arg)
    | Sum(terms) -> Sum(List.map (ExpandMacros context) terms)
    | Product(factors) -> Product(List.map (ExpandMacros context) factors)
    | Power(a,b) -> Power((ExpandMacros context a), (ExpandMacros context b))
    | Equals(a,b) -> Equals((ExpandMacros context a), (ExpandMacros context b))
    | NumExprRef(token,index) -> FindNumberedExpression context token index
    | PrevExprRef(token) -> FindPreviousExpression context token

//--------------------------------------------------------------------------------------------------

let ExecuteStatement context statement =
    match statement with

    | VarDecl {VarNameList=vlist; Range=range; ConceptExpr=conceptExpr;} ->
        let concept = ExpressionConcept context conceptExpr
        for vname in vlist do
            DefineSymbol context vname (VariableEntry(range,concept))
    
    | Assignment {TargetName=target; Expr=rawexpr;} ->
        let expr = ExpandMacros context rawexpr
        ValidateExpressionConcept context expr
        let refIndex = context.NumberedExpressionList.Count
        match target with
        | Some(assignToken) -> 
            DefineSymbol context assignToken (AssignmentEntry(expr))
            context.AssignmentHook (Some(assignToken.Text)) refIndex expr
        | None ->
            context.AssignmentHook None refIndex expr
        AppendNumberedExpression context expr

    | DoNothing ->
        ()
