module Freefall.Stmt
open Scanner
open Expr

//--------------------------------------------------------------------------------------------------

type MultiVariableDeclaration = {
    VarNameList : list<Token>
    Range : NumericRange
    ConceptExpr : Expression
}

type AssignmentStatement = {
    TargetName : option<Token>       // the optional user-specified name by which the entire expression should be known later
    Expr : Expression
}

type ConceptDefinition = {
    ConceptName : Token
    Expr : Expression
}

type UnitDefinition = {
    UnitName : Token
    Expr : Expression
}

type FormatAssertion = {
    AssertToken : Token
    ExpectedFormat : string
    Expr : Expression
}

type Statement =
    | AssertFormat of FormatAssertion
    | Assignment of AssignmentStatement
    | ConceptDef of ConceptDefinition
    | DoNothing
    | ForgetAllNumberedExpressions
    | ForgetNamedExpressions of list<Token>
    | Probe of Expression
    | Save of string
    | UnitDef of UnitDefinition
    | VarDecl of MultiVariableDeclaration

//--------------------------------------------------------------------------------------------------

let VarNameFolder accum vartoken =
    if accum = "" then
        vartoken.Text
    else
        accum + ", " + vartoken.Text

let JoinTokenList = List.fold VarNameFolder ""

let FormatStatement statement =
    match statement with

    | AssertFormat {AssertToken=token; ExpectedFormat=expected; Expr=expr} ->
        token.Text + "(\"" + expected + "\"," + (FormatExpression expr) + ");"

    | Assignment {TargetName=None; Expr=expr;} ->
        (FormatExpression expr) + ";"

    | Assignment {TargetName=Some(target); Expr=expr;} ->
        target.Text + " := " + (FormatExpression expr) + ";"

    | ConceptDef {ConceptName=idtoken; Expr=expr;} ->
        sprintf "concept %s = %s;" idtoken.Text (FormatExpression expr)

    | DoNothing ->
        ";"

    | ForgetAllNumberedExpressions ->
        "forget *;"

    | ForgetNamedExpressions(idlist) ->
        sprintf "forget %s;" (JoinTokenList idlist)

    | Save(filename) ->
        sprintf "save \"%s\";" filename

    | Probe(expr) ->
        sprintf "probe %s;" (FormatExpression expr)

    | UnitDef {UnitName=idtoken; Expr=expr;} ->
        sprintf "unit %s = %s;" idtoken.Text (FormatExpression expr)

    | VarDecl {VarNameList=vlist; Range=range; ConceptExpr=conceptExpr;} ->
        let varNamesText = JoinTokenList vlist
        let rangeText = FormatRange range
        let conceptText = FormatExpression conceptExpr
        let typeText =
            if conceptText = "1" then
                rangeText
            else
                rangeText + " " + conceptText
        "var " + varNamesText + ": " + typeText + ";"

//--------------------------------------------------------------------------------------------------

let FailNonFuncMacro token expected =
    SyntaxError token (sprintf "This symbol is %s, but is used as if it were a function or macro." expected)

let rec ExpandMacros context rawexpr =
    match rawexpr with
    | Amount(_) -> rawexpr
    | Del(_,_) -> rawexpr
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
    | Sum(terms) -> Sum(List.map (ExpandMacros context) terms)
    | Product(factors) -> Product(List.map (ExpandMacros context) factors)
    | Power(a,b) -> Power((ExpandMacros context a), (ExpandMacros context b))
    | Equals(a,b) -> Equals((ExpandMacros context a), (ExpandMacros context b))
    | NumExprRef(token,index) -> FindNumberedExpression context token index
    | PrevExprRef(token) -> FindPreviousExpression context token

//--------------------------------------------------------------------------------------------------
// Equation transformer: this is an important part of Freefall as an algebra helper.
//
// We allow equations to be added to other equations to produce equations:
//     (a=b) + (c=d) + (e=f)   ==>  a+c+e = b+d+f
//     sum(a=b, c=d, e=f)      ==> sum(a,c,e) = sum(b,d,f)
//
// Likewise, an equation can be added to a value:
//     (a=b) + x   ==> a+x = b+x
//     sum(a=b, x) ==> sum(a,x) = sum(b,x)
//
// Arbitrary mixtures of equations and values are allowed in sums:
//     (a=b) + x + (u=v) + y  ==>  a+x+u+y = b+x+v+y
//     sum(a=b, x, u=v, y)    ==>  sum(a,x,u,y) = sum(b,x,v,y)
//
// Subtracting a value from both sides of an equation:
//     (a=b) - x        ==> a-x = b-x
//     sum(a=b, neg(x)) ==> sum(a,neg(x)) = sum(b,neg(x))
//
// The same applies to multiplication, and with care, division as well.
//
// Unary operator support:
//     neg(a=b)  ==>  neg(a) = neg(b)
//
// We need to be able to apply safe, single-valued functions like this:
//     exp(a=b)  ==>   exp(a) = exp(b)
//
// FIXFIXFIX - handle the more complicated cases like taking square root of both sides, etc.

let rec PartitionEquationsAndValues exprlist =
    match exprlist with
    | [] -> 0, [], []
    | first :: rest ->
        let restNumEquations, restLeft, restRight = PartitionEquationsAndValues rest
        match first with
        | Equals(a,b) -> (1+restNumEquations), (a :: restLeft), (b :: restRight)
        | _ -> restNumEquations, (first :: restLeft), (first :: restRight)

let rec TransformAndPartition context exprlist =
    List.map (TransformEquations context) exprlist
    |> PartitionEquationsAndValues

and TransformEquations context expr =
    match expr with
    | Amount(_) -> expr
    | Solitaire(_) -> expr
    | Del(_,_) -> expr
    | Functor(name,argList) -> 
        let numEquations, leftList, rightList = TransformAndPartition context argList
        if numEquations = 0 then
            Functor(name,leftList)
        else
            let handler = FindFunctionEntry context name
            handler.DistributeAcrossEquation context name leftList rightList
    | Sum(terms) -> 
        let numEquations, leftList, rightList = TransformAndPartition context terms
        if numEquations = 0 then        // It is tempting to check for leftList=rightList, but that can happen even when there are equations!
            // There were no equations to bubble up above the sum, and we know leftList = rightList.
            Sum(leftList)
        else
            // Flip the sum(a=b, u, c=d, v) ==> sum(a+u+c+v) = Sum(b,u,d,v).
            Equals(Sum(leftList), Sum(rightList))
    | Product(factors) ->
        let numEquations, leftList, rightList = TransformAndPartition context factors
        if numEquations = 0 then
            Product(leftList)
        else
            // Flip the prod(a=b, u, c=d, v) ==> prod(a+u+c+v) = prod(b,u,d,v).
            Equals(Product(leftList), Product(rightList))
    | Power(a,b) -> Power((TransformEquations context a), (TransformEquations context b))
    | Equals(a,b) -> Equals((TransformEquations context a), (TransformEquations context b))
    | NumExprRef(token,index) -> FailLingeringMacro token
    | PrevExprRef(token) -> FailLingeringMacro token

//--------------------------------------------------------------------------------------------------

let PrepareExpression context rawexpr = rawexpr |> ExpandMacros context |> TransformEquations context

let ExecuteStatement context statement shouldReportAssignments =
    match statement with

    | AssertFormat {AssertToken=token; ExpectedFormat=expected; Expr=rawexpr} ->
        let expr = PrepareExpression context rawexpr
        let actual = FormatExpression expr
        if expected <> actual then
            SyntaxError token ("Format assertion failure:\nexpected = '" + expected + "'\nactual   = '" + actual + "'")

    | Assignment {TargetName=target; Expr=rawexpr;} ->
        let expr = PrepareExpression context rawexpr
        ValidateExpressionConcept context expr
        let range = ExpressionNumericRange context expr
        if IsEmptyRange range then
            ExpressionError rawexpr "Range of expression values is an empty set. This indicates it is impossible or solutionless."
        let refIndex = context.NumberedExpressionList.Count + 1
        match target with
        | Some(assignToken) -> 
            DefineSymbol context assignToken (AssignmentEntry(expr))
            if shouldReportAssignments then context.AssignmentHook (Some(assignToken.Text)) refIndex expr
        | None ->
            if shouldReportAssignments then context.AssignmentHook None refIndex expr
        AppendNumberedExpression context expr

    | ConceptDef {ConceptName=idtoken; Expr=expr;} ->
        let concept = EvalConcept context expr
        DefineSymbol context idtoken (ConceptEntry(concept))

    | DoNothing ->
        ()

    | ForgetAllNumberedExpressions ->
        DeletedNumberedExpressions context

    | ForgetNamedExpressions(idlist) ->
        List.iter (DeleteNamedExpression context) idlist

    | Save(filename) ->
        context.SaveToFile context filename

    | Probe(rawexpr) ->
        let expr = PrepareExpression context rawexpr
        let range = ExpressionNumericRange context expr
        let concept = ExpressionConcept context expr
        context.ProbeHook context expr range concept

    | UnitDef {UnitName=idtoken; Expr=expr;} ->
        let quantity = EvalQuantity context expr
        DefineSymbol context idtoken (UnitEntry(quantity))
    
    | VarDecl {VarNameList=vlist; Range=range; ConceptExpr=conceptExpr;} ->
        let concept = EvalConcept context conceptExpr
        for vname in vlist do
            DefineSymbol context vname (VariableEntry(range,concept))
