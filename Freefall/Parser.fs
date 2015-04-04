// Parser.fs  -  Don Cross  -  http://cosinekitty.com
// Symbolic algebra/physics helper.

module Freefall.Parser
open Freefall.Scanner
open Freefall.Expr
open Freefall.Stmt

//---------------------------------------------------------------------------------------
// Parser utility functions

let FileNameFromOrigin origin =
    match origin with
    | None -> None
    | Some {Filename=filename;} -> Some(filename)

let RequireToken scan =
    match scan with
    | [] -> raise (UnexpectedEndException None)
    | {Kind=TokenKind.EndOfFile; Origin=origin} :: _ -> raise (UnexpectedEndException (FileNameFromOrigin origin))
    | _::_ -> scan

let Impossible () = failwith "Internal error - this should not be possible!"

let ExpectToken text scan =
    match RequireToken scan with
    | {Text=actual;} :: scan2 as token when actual=text -> scan2
    | token :: _ -> raise (SyntaxException((sprintf "Expected '%s'" text), token))
    | _ -> Impossible ()

let ExpectSemicolon = ExpectToken ";"

let RequireExactlyOneArg funcName argList =
    match argList with
    | [arg] -> arg
    | _ -> raise (SyntaxException("Function requires exactly 1 argument.", funcName))

let RequireExactlyTwoArgs funcName argList =
    match argList with
    | [a; b;] -> (a, b)
    | _ -> raise (SyntaxException("Function requires exactly 2 arguments.", funcName))

//---------------------------------------------------------------------------------------
// Expression parser

let rec ParseExpression scan =
    let expr, scan2 = ParseAddSub scan
    match scan2 with
    | {Text="=";} :: scan3 ->
        let right, scan4 = ParseAddSub scan3
        (Equals(expr,right)), scan4
    | _ ->
        expr, scan2

and ParseAddSub scan =
    let mutable expr, xscan = ParseDivMul scan
    let termlist = new System.Collections.Generic.List<Expression>()
    termlist.Add(expr)

    while NextTokenHasPrecedence Precedence_Add xscan do
        let op = List.head xscan
        let right, yscan = ParseDivMul (List.tail xscan)
        xscan <- yscan
        if op.Text = "+" then
            termlist.Add(right)
        elif op.Text = "-" then
            termlist.Add(Negative(right))
        else
            raise (SyntaxException("Unsupported addop", op))

    if termlist.Count = 1 then
        expr, xscan
    else
        Sum(List.ofSeq termlist), xscan

and ParseDivMul scan =
    let mutable expr, xscan = ParseNegPow scan
    let factorlist = new System.Collections.Generic.List<Expression>()
    factorlist.Add(expr)

    while NextTokenHasPrecedence Precedence_Mul xscan do
        let op = List.head xscan
        let right, yscan = ParseDivMul (List.tail xscan)
        xscan <- yscan
        if op.Text = "*" then 
            factorlist.Add(right)
        elif op.Text = "/" then
            factorlist.Add(Reciprocal(right))
        else
            raise (SyntaxException("Unsupported multop", op))

    if factorlist.Count = 1 then
        expr, xscan
    else
        Product(List.ofSeq factorlist), xscan

and ParseNegPow scan =
    match RequireToken scan with

    | ({Text="-"} as negop) :: rscan ->
        let right, xscan = ParseNegPow rscan
        Negative(right), xscan

    | _ ->
        let atom, xscan = ParseAtom scan
        match xscan with
        | ({Text="^"} as powtoken) :: yscan ->
            let right, zscan = ParseNegPow yscan
            Power(atom, right), zscan
        | _ ->
            atom, xscan

and ParseArgList scan =
    // Open parenthesis has already been scanned.
    // arglist ::= [ expr { "," expr } ] ")"
    match RequireToken scan with

    | {Text=")";} :: scan2 -> 
        [], scan2

    | _ ->
        let expr, scan2 = ParseExpression scan
        match scan2 with
        | {Text=",";} :: scan3 ->
            let restArgs, scan4 = ParseArgList scan3
            (expr :: restArgs), scan4
        
        | {Text=")";} :: scan3 ->
            [expr], scan3

        | badtoken :: _ ->
            raise (SyntaxException("Expected ',' or ')' after function argument expression.", badtoken))

        | [] ->
            raise (UnexpectedEndException None)

and ParseAtom scan =
    match RequireToken scan with

    | [] -> failwith "Impossible."    // RequireToken already checks this case, but I want to eliminate warning here.

    | ({Kind=TokenKind.Identifier;} as funcName) :: {Text="(";} :: scan2 ->
        let argList, scan3 = ParseArgList scan2
        let expr = 
            match funcName.Text with
            | "neg"   -> Negative(RequireExactlyOneArg funcName argList)
            | "recip" -> Reciprocal(RequireExactlyOneArg funcName argList)
            | "sum"   -> Sum(argList)
            | "prod"  -> Product(argList)
            | "pow"   -> 
                let a, b = RequireExactlyTwoArgs funcName argList
                Power(a,b)
            | _       -> Functor(funcName,argList)
        expr, scan3

    | ({Kind=TokenKind.Identifier;} as token) :: rscan ->
        (Solitaire(token)), rscan     // "solitaire" is a word for a lone symbol that only context can distinguish between variable, unit, or concept.

    | ({Kind=TokenKind.ImagFloatLiteral; Text=text;} as imagtoken) :: rscan ->
        if not (text.EndsWith("i")) then
            raise (SyntaxException("Internal error - imaginary literal should have ended with 'i'", imagtoken))
        else
            let isValid, imagvalue = System.Double.TryParse(text.Substring(0, text.Length-1))
            if isValid then
                (Amount(PhysicalQuantity(Complex(0.0, imagvalue), Dimensionless))), rscan
            else
                raise (SyntaxException("Imaginary literal is not valid.", imagtoken))

    | ({Kind=TokenKind.RealFloatLiteral; Text=text;} as realtoken) :: rscan ->
        let isValid, realvalue = System.Double.TryParse(text)
        if isValid then
            (Amount(PhysicalQuantity(Real(realvalue), Dimensionless))), rscan
        else
            raise (SyntaxException("Real literal is not valid.", realtoken))

    | ({Kind=TokenKind.IntegerLiteral; Text=text;} as inttoken) :: rscan ->
        let isValid, intvalue = System.Int64.TryParse(text)
        if isValid then
            (Amount(PhysicalQuantity(Rational(intvalue,1L), Dimensionless))), rscan
        else
            raise (SyntaxException("Integer literal is not valid.", inttoken))

    | {Kind=TokenKind.Punctuation; Text="(";} :: xscan ->
        let expr, yscan = ParseExpression xscan
        match yscan with
        | {Text=")";} :: zscan -> expr, zscan
        | [] -> raise (UnexpectedEndException None)
        | badtoken :: zscan -> raise (SyntaxException("Expected ')'", badtoken))

    | ({Kind=TokenKind.ExpressionReference; Text=reftext;} as reftoken) :: xscan ->
        if reftext = "#" then
            // A reference to the previous expression statement.
            PrevExprRef(reftoken), xscan
        elif reftext.StartsWith("#") then
            // A reference to a particular expression statement.
            let isValid, index = System.Int32.TryParse(reftext.Substring(1))
            if isValid && (index >= 0) then
                NumExprRef(reftoken,index), xscan
            else
                raise (SyntaxException("Internal error - invalid integer after '#'", reftoken))
        else
            raise (SyntaxException("Internal error - parsed invalid expression reference", reftoken))

    // FIXFIXFIX - support the following constructs
    // "@" ident    ==>  derivative operator

    | badtoken :: _ -> 
        raise (SyntaxException("Syntax error.", badtoken))    

//---------------------------------------------------------------------------------------
// Statement parser

let rec ParseIdentList scan =
    match RequireToken scan with

    | [] -> failwith "Impossible."    // RequireToken already checks this case, but I want to eliminate warning here.

    | ({Kind=TokenKind.Identifier} as vartoken) :: punc :: xscan ->
        match punc.Text with

        | "," ->
            let restlist, yscan = ParseIdentList xscan
            (vartoken::restlist), yscan

        | ":" ->
            [vartoken], xscan

        | _ ->
            raise (SyntaxException("Expected ',' or ':' after variable name", punc))

    | token :: _ ->
        raise (SyntaxException("Expected variable name identifier", token))

let ParseTypeAndSemicolon scan =
    // type ::= typename [expr] | expr 
    //
    //      In the above rule, expr is a concept expression, e.g., distance/time
    //
    // typename ::= "complex" | "real" | "rational" | "integer" [intrange]
    // intrange ::= "(" numexpr "," numexpr ")"       // both numexpr must evaluate to integers
    //
    //      FIXFIXFIX - intrange not yet implemented
    match RequireToken scan with 

    | {Kind=TokenKind.NumericRangeName; Text=text;} :: {Text=";";} :: scan2 ->
        RangeNameTable.[text], UnityAmount, scan2   // range present but concept absent means concept defaults to dimensionless unity

    | {Kind=TokenKind.NumericRangeName; Text=text} :: scan2 ->
        let conceptExpr, scan3 = ParseExpression scan2
        RangeNameTable.[text], conceptExpr, (ExpectSemicolon scan3)

    | _ ->
        let conceptExpr, scan2 = ParseExpression scan
        RealRange, conceptExpr, (ExpectSemicolon scan2)       // variables declared without range, e.g. "var t : time;" default to real.


let ParseStatement scan =
    match RequireToken scan with 

    | {Text="var";} :: scan2 ->
        // vardecl ::= "var" ident { "," ident } ":" type ";"
        let identList, scan3 = ParseIdentList scan2
        let range, conceptExpr, scan4 = ParseTypeAndSemicolon scan3
        VarDecl{VarNameList=identList; Range=range; ConceptExpr=conceptExpr;}, scan4

    | {Text=";";} :: rscan -> 
        (DoNothing, rscan)

    | ({Kind=TokenKind.Identifier} as target) :: {Text=":=";} :: rscan ->
        let expr, xscan = ParseExpression rscan
        Assignment{TargetName=Some(target); Expr=expr}, (ExpectSemicolon xscan)

    | _ ->
        let expr, xscan = ParseExpression scan
        Assignment{TargetName=None; Expr=expr}, (ExpectSemicolon xscan)
