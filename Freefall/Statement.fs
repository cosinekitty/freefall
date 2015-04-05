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

type ConceptDefinition = {
    ConceptName : Token;
    Expr : Expression;
}

type Statement =
    | VarDecl of MultiVariableDeclaration
    | ConceptDef of ConceptDefinition
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

    | ConceptDef {ConceptName=idtoken; Expr=expr;} ->
        sprintf "concept %s = %s;" idtoken.Text (FormatExpression expr)

    | Assignment {TargetName=None; Expr=expr;} ->
        (FormatExpression expr) + ";"

    | Assignment {TargetName=Some(target); Expr=expr;} ->
        target.Text + " := " + (FormatExpression expr) + ";"

    | DoNothing ->
        ";"

//--------------------------------------------------------------------------------------------------

let FailNonFuncMacro token expected =
    SyntaxError token (sprintf "This symbol is %s, but is used as if it were a function or macro." expected)

let rec ExpandMacros context rawexpr =
    match rawexpr with
    | Amount(_) -> rawexpr
    | Solitaire(nameToken) -> 
        match FindSymbolEntry context nameToken with
        | VariableEntry(_) -> rawexpr
        | ConceptEntry(_) -> rawexpr
        | UnitEntry(_) -> rawexpr
        | AssignmentEntry(expr) -> expr
        | MacroEntry(_) -> SyntaxError nameToken "Cannot use macro name as solitary symbol."
        | FunctionEntry(_) -> SyntaxError nameToken "Cannot use function name as solitary symbol."
    | Functor(funcName,argList) -> 
        match FindSymbolEntry context funcName with
        | MacroEntry({Expander=expander;}) -> expander funcName (List.map (ExpandMacros context) argList)
        | FunctionEntry(_) -> Functor(funcName, (List.map (ExpandMacros context) argList))
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
        let concept = EvalConcept context conceptExpr
        for vname in vlist do
            DefineSymbol context vname (VariableEntry(range,concept))

    | ConceptDef {ConceptName=idtoken; Expr=expr;} ->
        let concept = EvalConcept context expr
        DefineSymbol context idtoken (ConceptEntry(concept))
    
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
