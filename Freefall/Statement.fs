﻿module Freefall.Stmt
open Freefall.Scanner
open Freefall.Expr

//--------------------------------------------------------------------------------------------------

type AssignmentStatement = {
    TargetName : option<Token>       // the optional user-specified name by which the entire expression should be known later
    Expr : Expression
}

type ConceptDefinition = {
    ConceptName : Token
    Expr : Expression
}

type DecomposeStatement = {
    DecompToken : Token
    Expr : Expression
}

type FormatAssertion = {
    AssertToken : Token
    ExpectedFormat : string
    Expr : Expression
}

type MultiVariableDeclaration = {
    VarNameList : list<Token>
    Range : NumericRange
    ConceptExpr : Expression
}

type UnitDefinition = {
    UnitName : Token
    Expr : Expression
}

type Statement =
    | AssertFormat of FormatAssertion
    | Assignment of AssignmentStatement
    | ConceptDef of ConceptDefinition
    | Decomp of DecomposeStatement
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

    | Decomp {Expr=expr} ->
        sprintf "decomp %s;" (FormatExpression expr)

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
// We need to be able to apply safe, single-valued functions like this:
//     exp(a=b)  ==>   exp(a) = exp(b)

let rec NaivePowerSimp context a b =      // returns "naive" simplification of a^b
    // This is a so-called "naive" simplification rule that does things like:
    // sqrt(x^2) ==> x
    // Or in general, (x^y)^b ==> x^(y*b)
    // This is safe in cases where uroot is already in use to represent 
    // the multiplicity of solutions in a transformed equation.
    match a with
    | Amount(PhysicalQuantity(anumber, concept)) when concept = Dimensionless ->
        match PerfectRationalPower anumber b with
        | None -> Power(a, Amount(PhysicalQuantity(b, Dimensionless)))
        | Some(c) -> Amount(PhysicalQuantity(c, Dimensionless))

    | Power(x, Amount(PhysicalQuantity(y, concept))) when concept = Dimensionless ->
        let c = MultiplyNumbers y b
        if IsNumberEqualToInteger 1I c then
            x
        else
            Power(x, Amount(PhysicalQuantity(c, Dimensionless)))

    | Product(factorlist) ->
        // Distribute the power simplification across the terms of the product.
        Product(List.map (fun f -> NaivePowerSimp context f b) factorlist)

    | _ -> 
        Power(a, Amount(PhysicalQuantity(b, Dimensionless)))

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

and TransformEquations context expr =       // expands macros, equation references and transforms equations
    let xform =
        match expr with
        | Amount(_) -> expr
        | Solitaire(_) -> expr
        | Del(_,_) -> expr
        | Functor(name,argList) -> 
            match FindSymbolEntry context name with
            | MacroEntry({Expander=expander; ArgBehavior=argBehavior}) -> 
                let expanded =
                    match argBehavior with
                    | RawArgs       -> expander name argList
                    | PreExpandArgs -> expander name (List.map (TransformEquations context) argList)
                TransformEquations context expanded

            | FunctionEntry(_) -> 
                let numEquations, leftList, rightList = TransformAndPartition context argList
                if numEquations = 0 then
                    Functor(name,leftList)
                else
                    let handler = FindFunctionEntry context name
                    handler.DistributeAcrossEquation context name leftList rightList

            | VariableEntry(_) -> FailNonFuncMacro name "a variable"
            | ConceptEntry(_) -> FailNonFuncMacro name "a concept"
            | UnitEntry(_) -> FailNonFuncMacro name "a unit"
            | AssignmentEntry(_) -> FailNonFuncMacro name "an assignment target"

        | Sum(terms) -> 
            let numEquations, leftList, rightList = TransformAndPartition context terms
            if numEquations = 0 then
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

        | Power(a,b) -> 
            let aTrans = TransformEquations context a
            let bTrans = TransformEquations context b

            match aTrans, bTrans with
            | DoesNotEqual(_,_), _
            | _, DoesNotEqual(_,_)
                -> ExpressionError expr "Unsupported inequality transformation"

            | Equals(_,_), Equals(_,_) ->
                ExpressionError expr "Unsupported equation transformation"

            | Equals(ax,ay), bRaw ->
                let bSimp = Simplify context bRaw       // boil down to a rational number if possible
                match bSimp with
                | Amount(PhysicalQuantity(bNumber,bConcept)) ->
                    if bConcept = Dimensionless then
                        match bNumber with
                        | Rational(bNum,bDen) ->
                            if bDen = 1I then
                                // (ax=ay)^b ==> (ax^b) = (ay^b) if b is a dimensionless integer.
                                Equals(Power(ax,bSimp), Power(ay,bSimp))
                            else
                                // (ax=ay)^(bn/bd) ==> ax^b = pow(uroot(bd), [0..(bd-1)]) * ay^b  where b = bn/bd
                                // This requires a scary side-effect!
                                // We create a brand new variable K_n: integer[0, bd-1].
                                let varExpr = Solitaire(CreateVariable context "K" (IntegerRange(FiniteLimit(0I), FiniteLimit(bDen-1I))) Dimensionless)
                                let uroot = 
                                    if bDen = 2I then
                                        AmountNegOne    // pre-simplify uroot(2) ==> -1
                                    else
                                        Functor(SynthToken "uroot", [Amount(PhysicalQuantity(Rational(bDen,1I),Dimensionless))])
                                let axPower = NaivePowerSimp context ax bNumber
                                let ayPower = NaivePowerSimp context ay bNumber
                                Equals(axPower, (OptimizeMultiply (Power(uroot, varExpr)) ayPower))
                        | _ ->
                            ExpressionError expr "Cannot raise both sides of an equation to a non-rational power."
                    else
                        ExpressionError expr "Cannot raise both sides of an equation to a dimensional power."
                | _ ->
                    ExpressionError expr "Unsupported equation transformation."

            | _, Equals(bx,by) ->
                Equals(Power(aTrans,bx), Power(aTrans,by))      // FIXFIXFIX - is this correct?
                
            | _ -> Power(aTrans, bTrans)

        | Equals(a,b) -> Equals((TransformEquations context a), (TransformEquations context b))
        | DoesNotEqual(a,b) -> DoesNotEqual((TransformEquations context a), (TransformEquations context b))
        | LessThan(a,b) -> LessThan((TransformEquations context a), (TransformEquations context b))
        | LessThanOrEqual(a,b) -> LessThanOrEqual((TransformEquations context a), (TransformEquations context b))
        | GreaterThan(a,b) -> GreaterThan((TransformEquations context a), (TransformEquations context b))
        | GreaterThanOrEqual(a,b) -> GreaterThanOrEqual((TransformEquations context a), (TransformEquations context b))
        | NumExprRef(token,index) -> FindNumberedExpression context token index
        | PrevExprRef(token) -> FindPreviousExpression context token

    // Make sure units are OK at each recursive level of transformation.
    // This takes the burden off each of the transformation rules and helps prevent bugs from creeping in.
    ValidateExpressionConcept context xform

    xform

//--------------------------------------------------------------------------------------------------

let ExecuteStatement context firstTokenInStatement statement shouldReportAssignments =
    // Before excecuting the statement, record the first token in that statement.
    // This is our last line of defense for diagnosing exceptions.
    context.FirstTokenInExecutingStatement := firstTokenInStatement

    match statement with

    | AssertFormat {AssertToken=token; ExpectedFormat=expected; Expr=rawexpr} ->
        let expr = TransformEquations context rawexpr
        let actual = FormatExpression expr
        if expected <> actual then
            SyntaxError token ("Format assertion failure:\nexpected = '" + expected + "'\nactual   = '" + actual + "'")

    | Assignment {TargetName=target; Expr=rawexpr;} ->
        let expr = TransformEquations context rawexpr
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

    | Decomp {DecompToken=decompToken; Expr=rawexpr} ->
        TransformEquations context rawexpr 
        |> DecomposeExpression
        |> context.DecomposeHook context

    | DoNothing ->
        ()

    | ForgetAllNumberedExpressions ->
        DeletedNumberedExpressions context

    | ForgetNamedExpressions(idlist) ->
        List.iter (DeleteNamedExpression context) idlist

    | Save(filename) ->
        context.SaveToFile context filename

    | Probe(rawexpr) ->
        let expr = TransformEquations context rawexpr
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

    // Getting here means we did not encounter any exceptions executing this statement.
    // Erase the error tracking token.
    // NOTE: Will have to rework this if we allow nested statement exeuction
    // (statements that execute other statements, e.g. blocks or running a file).
    context.FirstTokenInExecutingStatement := EndOfFileToken None
