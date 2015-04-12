// Calculus.fs  -  Don Cross  -  http://cosinekitty.com
// Symbolic algebra/physics helper.

module Freefall.Calculus
open System.Numerics
open Freefall.Expr
open Freefall.Scanner

let IsInVariableList token varNameList =
    List.exists (fun v -> v = token.Text) varNameList

let rec TakeDifferential context varNameList expr =
    match expr with
    | Amount(_) -> ZeroAmount       // diff(constant) = 0
    | Solitaire(token) ->
        match FindSymbolEntry context token with
        | VariableEntry(range,concept) ->
            if IsInVariableList token varNameList then
                Del(token, 1)
            else
                ZeroAmount
        | ConceptEntry(concept) -> SyntaxError token "Concept not allowed in differential expression."
        | UnitEntry(quantity) -> ZeroAmount
        | AssignmentEntry(_) -> SyntaxError token "Lingering assignment entry in differential."
        | MacroEntry(_) -> SyntaxError token "Lingering macro in differential."
        | FunctionEntry(_) -> SyntaxError token "Function name cannot be used as a variable."
    | Functor(funcNameToken,argList) ->
        SyntaxError funcNameToken "Derivative of function not yet implemented."     // FIXFIXFIX
    | Negative(arg) -> 
        // d(-x) = -(dx)
        Negative(TakeDifferential context varNameList arg)
    | Reciprocal(arg) ->
        // d(1/x) = d(x^(-1)) = -x^(-2)dx
        let dx = TakeDifferential context varNameList arg
        let neg2 = IntegerAmount -2
        Product[Negative(Power(arg,neg2)); dx]
    | Sum(termlist) ->
        // d(a + b + c + ...) = da + db + dc + ...
        Sum(List.map (TakeDifferential context varNameList) termlist)
    | Product(factorlist) ->
        Sum(ProductDifferentialTerms context varNameList factorlist)
    | Power(a,b) ->
        ExpressionError expr "Differential of power expressions not yet implemented."   // FIXFIXFIX
    | Equals(a,b) ->
        // d(a=b) ==> da = db
        let da = TakeDifferential context varNameList a
        let db = TakeDifferential context varNameList b
        Equals(da,db)
    | NumExprRef(badtoken,_) -> FailLingeringMacro badtoken
    | PrevExprRef(badtoken) -> FailLingeringMacro badtoken
    | Del(vartoken,order) ->
        // If vartoken is supposed to be treated as a variable, then increment order.
        // Otherwise, replace with zero.
        if IsInVariableList vartoken varNameList then
            Del(vartoken,1+order)
        else
            ZeroAmount

and ProductDifferentialTerms context varNameList factorList =
    // Given the list of N factors in a product, we return a list of
    // N terms, each having N factors, where the Ith factor is differentiated:
    // d(u*v*w*...) = du*v*w*... + u*dv*w*... + u*v*dw*... + ...
    let termIndex = ref 0
    let diffTermList = new ResizeArray<Expression>()
    for _ in factorList do
        diffTermList.Add(Product(List.mapi (fun factorIndex factor -> if factorIndex = !termIndex then (TakeDifferential context varNameList factor) else factor) factorList))
        termIndex := 1 + !termIndex
    List.ofSeq diffTermList