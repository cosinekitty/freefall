﻿// Parser.fs  -  Don Cross  -  http://cosinekitty.com
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

let ExpectToken text scan =
    match scan with
    | [] -> raise (UnexpectedEndException None)
    | {Kind=TokenKind.EndOfFile; Origin=origin} :: _ -> raise (UnexpectedEndException (FileNameFromOrigin origin))
    | {Text=actual;} :: scan2 as token when actual=text -> scan2
    | token :: _ -> raise (SyntaxException((sprintf "Expected '%s'" text), token))

let ExpectSemicolon = ExpectToken ";"

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
    while NextTokenHasPrecedence Precedence_Add xscan do
        let op = List.head xscan
        let right, yscan = ParseDivMul (List.tail xscan)
        xscan <- yscan
        expr <- (Sum([expr ; right]))
    expr, xscan

and ParseDivMul scan =
    let mutable expr, xscan = ParseNegPow scan
    while NextTokenHasPrecedence Precedence_Mul xscan do
        let op = List.head xscan
        let right, yscan = ParseDivMul (List.tail xscan)
        xscan <- yscan
        if op.Text = "*" then 
            expr <- Product([expr ; right])
        elif op.Text = "/" then
            expr <- Product([expr; Reciprocal(right)])
        else
            raise (SyntaxException("Unsupported multop", op))
    expr, xscan

and ParseNegPow scan =
    match scan with
    | [] -> 
        raise (UnexpectedEndException None)

    | {Kind=TokenKind.EndOfFile; Origin=origin} :: _ -> 
        raise (UnexpectedEndException (FileNameFromOrigin origin))

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

and ParseAtom scan =
    match scan with
    | [] -> 
        raise (UnexpectedEndException None)

    | {Kind=TokenKind.EndOfFile; Origin=origin} :: _ -> 
        raise (UnexpectedEndException (FileNameFromOrigin origin))

    | ({Kind=TokenKind.Identifier;} as vartoken) :: rscan ->
        (Variable(vartoken)), rscan     // FIXFIXFIX - need to handle non-variable identifiers, e.g. function calls, macro expansions

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

    // FIXFIXFIX - support the following constructs
    // "@" ident    ==>  derivative operator
    // "#" [0-9]*   ==>  expression reference
    // ident "(" arglist ")"   ==> function call or macro expansion

    | badtoken :: _ -> 
        raise (SyntaxException("Syntax error.", badtoken))

//---------------------------------------------------------------------------------------
// Statement parser

let rec ParseIdentList scan =
    match scan with

    | [] ->
        raise (UnexpectedEndException None)

    | {Kind=TokenKind.EndOfFile; Origin=origin} :: _ ->
        raise (UnexpectedEndException (FileNameFromOrigin origin))

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
    match scan with 

    | [] ->
        raise (UnexpectedEndException None)

    | {Kind=TokenKind.EndOfFile; Origin=origin} :: _ ->
        raise (UnexpectedEndException (FileNameFromOrigin origin))

    | {Kind=TokenKind.NumericRangeName; Text=text;} :: {Text=";";} :: scan2 ->
        RangeNameTable.[text], UnityAmount, scan2   // range present but concept absent means concept defaults to dimensionless unity

    | {Kind=TokenKind.NumericRangeName; Text=text} :: scan2 ->
        let conceptExpr, scan3 = ParseExpression scan2
        RangeNameTable.[text], conceptExpr, (ExpectSemicolon scan3)

    | _ ->
        let conceptExpr, scan2 = ParseExpression scan
        RealRange, conceptExpr, (ExpectSemicolon scan2)       // variables declared without range, e.g. "var t : time;" default to real.


let ParseStatement scan =
    match scan with 

    | [] -> 
        raise (UnexpectedEndException None)

    | {Kind=TokenKind.EndOfFile; Origin=origin} :: _ ->
        raise (UnexpectedEndException (FileNameFromOrigin origin))

    | {Text="var";} :: scan2 ->
        // vardecl ::= "var" ident { "," ident } ":" type ";"
        let identList, scan3 = ParseIdentList scan2
        let range, conceptExpr, scan4 = ParseTypeAndSemicolon scan3
        VarDecl{VarNameList=identList; Range=range; ConceptExpr=conceptExpr;}, scan4

    | {Text=";";} :: rscan -> 
        (DoNothing, rscan)

    | ({Kind=TokenKind.Identifier} as target) :: {Text=":=";} :: rscan ->
        let expr, xscan = ParseExpression rscan
        Assignment{TargetName=Some(target); Expr=expr}, xscan

    | _ ->
        let expr, xscan = ParseExpression scan
        Assignment{TargetName=None; Expr=expr}, (ExpectSemicolon xscan)
