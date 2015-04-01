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
    | {Text="-"} :: rscan as negop ->
        let right, xscan = ParseNegPow rscan
        Negative(right), xscan
    // !!!!! Finish this scanner function !!!!!