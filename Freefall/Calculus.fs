﻿// Calculus.fs  -  Don Cross  -  http://cosinekitty.com
// Symbolic algebra/physics helper.

module Freefall.Calculus
open Freefall.Expr
open Freefall.Scanner

let MakeFunction name arglist =
    Functor(SynthToken name, arglist)

let IsInVariableList token varNameList =
    List.exists (fun v -> v = token.Text) varNameList

let rec TakeDifferential derivKind context varNameList expr =
    let primaryVarName = List.head varNameList
    match expr with
    | Amount(_) -> AmountZero       // diff(constant) = 0
    | Solitaire(token) ->
        match FindSymbolEntry context token with
        | VariableEntry(range,concept) ->
            if IsInVariableList token varNameList then
                match derivKind with
                | Differential -> Del(token, 1)
                | Derivative -> 
                    if token.Text = (List.head varNameList) then
                        AmountOne     // d/dx (x) = 1
                    else
                        // d/dx (y) = dy / dx
                        Divide (Del(token,1)) (Del(SynthToken primaryVarName,1))
            else
                AmountZero
        | ConceptEntry(concept) -> SyntaxError token "Concept not allowed in differential expression."
        | UnitEntry(quantity) -> AmountZero
        | AssignmentEntry(_) -> SyntaxError token "Lingering assignment entry in differential."
        | MacroEntry(_) -> SyntaxError token "Lingering macro in differential."
        | FunctionEntry(_) -> SyntaxError token "Function name cannot be used as a variable."
    | Functor(funcNameToken,argList) ->
        let handler = FindFunctionEntry context funcNameToken
        handler.Differential derivKind context varNameList funcNameToken argList
    | Sum(termlist) ->
        // d(a + b + c + ...) = da + db + dc + ...
        Sum(List.map (TakeDifferential derivKind context varNameList) termlist)
    | Product(factorlist) ->
        Sum(ProductDifferentialTerms derivKind context varNameList factorlist)
    | Power(v,w) ->
        // d(v^w) = (v^w) * ((w/v)*dv + ln(v)*dw)
        let dv = TakeDifferential derivKind context varNameList v
        let dw = TakeDifferential derivKind context varNameList w
        let ln_v = MakeFunction "ln" [v]
        Product[expr; Sum[Product[w;MakeReciprocal v;dv]; Product[ln_v;dw]]]
    | Equals(a,b) ->
        // d(a=b) ==> da = db
        let da = TakeDifferential derivKind context varNameList a
        let db = TakeDifferential derivKind context varNameList b
        Equals(da,db)
    | DoesNotEqual(_,_)
    | LessThan(_,_)
    | LessThanOrEqual(_,_)
    | GreaterThan(_,_)
    | GreaterThanOrEqual(_,_)
        // It is not correct to take the derivative of an inequality.
        // Two unequal expressions may have derivatives that are unequal or equal.
        // For example:  cos(x) + 3 != cos(x) + 7 is always true, but their derivatives are the same.
        -> ExpressionError expr "Cannot take derivative of an inequality."
    | NumExprRef(badtoken,_) -> FailLingeringMacro badtoken
    | PrevExprRef(badtoken) -> FailLingeringMacro badtoken
    | Del(vartoken,order) ->
        if IsInVariableList vartoken varNameList then
            match derivKind with
            | Differential -> Del(vartoken,1+order)
            | Derivative -> Product[Del(vartoken,1+order); MakeReciprocal (Del(SynthToken primaryVarName,1))]
        else
            AmountZero

and ProductDifferentialTerms derivKind context varNameList factorList =
    // Given the list of N factors in a product, we return a list of
    // N terms, each having N factors, where the Ith factor is differentiated:
    // d(u*v*w*...) = du*v*w*
    let termIndex = ref 0
    let diffTermList = new ResizeArray<Expression>()
    for _ in factorList do  // quirky way of iterating factorList.Length times, without redundant traversal implied by .Length 
        diffTermList.Add(Product(List.mapi (fun factorIndex factor -> if factorIndex = !termIndex then (TakeDifferential derivKind context varNameList factor) else factor) factorList))
        incr termIndex
    List.ofSeq diffTermList