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
    | [] -> failwith "Expected '-' or <atom>'"  // FIXFIXFIX - token exception here
    | ({Text="-"} as negop) :: rscan ->
        let right, xscan = ParseNegPow rscan
        Negative(right), xscan
    | _ ->
        let atom, xscan = ParseAtom scan
        match xscan with
        | {Text="^"} :: yscan ->
            let right, zscan = ParseNegPow yscan
            Power(atom, right), zscan
        | _ -> failwith "Expected '^'"      // FIXFIXFIX - token exception here

and ParseAtom scan =
    match scan with
    | [] -> failwith "Expected <atom>"  // FIXFIXFIX - need "unexpected end of input" error
    | ({Kind=TokenKind.Identifier} as vartoken) :: rscan ->
        (Variable(vartoken)), rscan
