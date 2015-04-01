// Parser.fs  -  Don Cross  -  http://cosinekitty.com
// Symbolic algebra/physics helper.

module Freefall.Parser
open Freefall.Scanner
open Freefall.Expr

let rec ParseExpression scan =
    ParseAddSub scan
    // FIXFIXFIX - need to decide how to implement relational expressions

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
        expr <- (Sum([expr ; right]))
    expr, xscan

and ParseNegPow scan =
    match scan with
    | [] -> raise UnexpectedEndException
    | ({Text="-"} as negop) :: rscan ->
        let right, xscan = ParseNegPow rscan
        Negative(right), xscan
    | _ ->
        let atom, xscan = ParseAtom scan
        match xscan with
        | ({Text=powtext} as powtoken) :: yscan ->
            if powtext <> "^" then
                raise (SyntaxException("Expected '^'", powtoken))
            else
                let right, zscan = ParseNegPow yscan
                Power(atom, right), zscan
        | [] -> raise UnexpectedEndException

and ParseAtom scan =
    match scan with
    | [] -> raise UnexpectedEndException

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
