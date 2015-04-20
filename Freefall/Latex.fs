module Freefall.Latex
open System.Numerics
open Freefall.Scanner
open Freefall.Expr
open Freefall.Calculus
open Freefall.Stmt
open Freefall.Parser

let LatexRealString (x:float) =
    let text = RealString x
    let eIndex = text.IndexOf("e")
    if eIndex < 0 then
        text
    else
        // "1.23e-5" ==> "1.23x10^(-5)"  (only in Latex format, of course)
        let mantissa = text.Substring(0, eIndex)
        let exponent = System.Int32.Parse(text.Substring(eIndex+1)).ToString()
        mantissa + " \\times 10^{" + exponent + "}"

let LatexFormatNumber x =
    match x with
    | Rational(numer,denom) ->
        if denom.IsZero then
            raise (FreefallRuntimeException("Rational number had zero denominator."))
        elif denom.IsOne then
            numer.ToString()
        else
            "\\frac{" + numer.ToString() + "}{" + denom.ToString() + "}"
    | Real(x) -> LatexRealString x
    | Complex(c) -> 
        // (-3.4-5.6i)
        // (-3.4+5.6i)
        let rtext = LatexRealString c.Real
        let itext = 
            if c.Imaginary >= 0.0 then
                "+" + (LatexRealString c.Imaginary)
            else
                LatexRealString c.Imaginary
        "(" + rtext + itext + " i)"

let LatexFormatDimension name (numer:BigInteger,denom:BigInteger) =
    if numer.IsZero then
        ""      // this dimension does not contribute to formatting, e.g. meter^0
    elif numer.IsOne && denom.IsOne then
        name    // meter^(1/1) is written as "meter"
    elif denom.IsOne then
        name + "^{" + numer.ToString() + "}"
    else
        name + "^{\\frac{" + numer.ToString() + "}{" + denom.ToString() + "}"

let LatexAccumDimension prefix name (numer,denom) =
    let text = LatexFormatDimension name (numer,denom)
    match (prefix,text) with
    | ("","") -> ""
    | ("",_)  -> text
    | (_,"")  -> prefix
    | (_,_)   -> prefix + " \\cdot " + text

let LatexFormatDimensions namelist concept =
    match concept with
    | Zero -> "0"
    | Concept(powlist) -> List.fold2 LatexAccumDimension "" namelist powlist

let LatexFormatQuantity context (PhysicalQuantity(scalar,concept)) =
    if IsNumberZero scalar then
        "0"     // special case because zero makes all units irrelevant
    else
        let scalarText = LatexFormatNumber scalar
        let conceptText = LatexFormatDimensions BaseUnitNames concept
        if conceptText = "" then
            scalarText
        elif conceptText = "0" then
            "0"
        elif scalarText = "1" then
            conceptText
        else
            scalarText + " " + conceptText

let LatexExpressionPrecedence expr =
    // Special case: numbers are formatted with scientific notation as multiplication.
    match expr with
    | Amount(PhysicalQuantity(Real(x),_)) when (RealString x).Contains("e") -> Precedence_Mul
    | _ -> ExpressionPrecedence expr

let rec SplitNumerDenom factorList =
    match factorList with
    | [] -> [], []
    | first::rest ->
        let rNumerList, rDenomList = SplitNumerDenom rest
        match first with
        | Amount(PhysicalQuantity(Rational(a,b),concept)) when concept = Dimensionless && a.IsOne && (not b.IsOne) ->
            rNumerList, (Amount(PhysicalQuantity(Rational(b,a),concept)) :: rDenomList)
        | Power(x, Amount(PhysicalQuantity(Rational(a,b),concept))) when concept = Dimensionless && a.Sign < 0 ->
            rNumerList, (Power(x, Amount(PhysicalQuantity(Rational((BigInteger.Negate a),b), concept))) :: rDenomList)
        | _ -> (first :: rNumerList), rDenomList

// Some Latex Greek letters are written using Latin letters.
// For example, capital chi is written using X.
// Because there is no way to tell Latin X from Greek X,
// it is considered undesirable to even refer to them as distinct
// math symbols, since the reader can't tell them apart.
// Just like Latex, we don't support such capital Greek letters here.
let GreekLetterSet = 
    Set.ofList 
        [ "alpha"; "beta"; "gamma"; "Gamma"; "delta"; "Delta"; "epsilon"; "varepsilon"; "zeta"; "eta"; "theta"; "Theta"; 
          "vartheta"; "iota"; "kappa"; "lambda"; "Lambda"; "mu"; "nu"; "xi"; "Xi"; "omicron"; "pi"; "Pi"; "varpi"; "rho"; 
          "varrho"; "sigma"; "varsigma"; "Sigma"; "tau"; "upsilon"; "Upsilon"; "phi"; "Phi"; "varphi"; "chi"; "psi"; 
          "Psi"; "omega"; "Omega" ]


let LatexFixName (name:string) =
    if Set.contains name GreekLetterSet then
        @"\" + name
    else
        name

let rec FormatLatex context expr =
    FormatLatexPrec context expr Precedence_Or

and ListFormatLatex context argList =
    match argList with
    | [] -> ""
    | [single] -> FormatLatex context single
    | first::rest -> (FormatLatex context first) + ", " + (ListFormatLatex context rest)

and FormatLatexPrec context expr parentPrecedence =
    let innerText =
        match expr with
        | Amount(quantity) -> LatexFormatQuantity context quantity
        | Solitaire(nameToken) -> 
            // FIXFIXFIX - convert underscores to subscripts?
            let text = LatexFixName nameToken.Text
            match FindSymbolEntry context nameToken with
            | VariableEntry(_,_) ->
                // FIXFIXFIX - We prefer variables to be italicized, except it is weird when they are multi-character.
                text
            | ConceptEntry(_) -> Impossible ()
            | UnitEntry(PhysicalQuantity(number,concept)) ->
                if concept <> Dimensionless then
                    "\\mathrm{" + text + "}"
                else
                    text
            | AssignmentEntry(_) -> Impossible ()
            | MacroEntry(_) -> Impossible()
            | FunctionEntry(_) -> SyntaxError nameToken "Attempt to use a function name as a variable."
        | Functor(nameToken,argList) ->
            let func = FindFunctionEntry context nameToken
            func.LatexName + "\\left(" + ListFormatLatex context argList + "\\right)"
        | Sum(termList) ->
            match termList with
            | [] -> "0"
            | [single] -> FormatLatex context single
            | first::rest -> FormatLatexPrec context first Precedence_Add + LatexJoinRemainingTerms context rest
        | Product(factorList) ->
            // Split the factor list into numerator factors and denominator factors.
            // For example: prod(pow(x,-2), y, pow(z,-1))
            // numerator list = [y]
            // denominator list = [pow(x,2); z]
            // Gets rendered as y / (x^2 * z).
            match SplitNumerDenom factorList with
            | [], [] -> "1"
            | numerList, [] -> LatexFormatFactorList context numerList
            | numerList, denomList -> 
                let numerText = LatexFormatFactorList context numerList
                let denomText = LatexFormatFactorList context denomList
                "\\frac{" + numerText + "}{" + denomText + "}"

        | Power(a,b) ->
            let atext = FormatLatexPrec context a Precedence_Pow
            let btext = FormatLatexPrec context b Precedence_Pow
            atext + "^{" + btext + "}"
        | Equals(a,b) ->
            let atext = FormatLatexPrec context a Precedence_Rel
            let btext = FormatLatexPrec context b Precedence_Rel
            atext + " = " + btext
        | NumExprRef(hashToken,listIndex) -> FailLingeringMacro hashToken
        | PrevExprRef(hashToken) -> FailLingeringMacro hashToken
        | Del(opToken,order) ->
            let vtext = FormatLatex context (Solitaire(opToken))
            if order > 1 then
                "\\partial^{" + order.ToString() + "}" + vtext
            else
                "\\partial " + vtext

    if parentPrecedence < LatexExpressionPrecedence expr then
        innerText
    else
        "\\left(" + innerText + "\\right)"

and LatexJoinRemainingTerms context termList =
    match termList with
    | [] -> ""
    | first::rest ->
        let rtext = LatexJoinRemainingTerms context rest

        // check for anything that looks "negative" so we can turn it into subtraction
        let ftext = FormatLatexPrec context first Precedence_Add

        if ftext.StartsWith("-") then
            ftext + rtext
        else
            "+" + ftext + rtext

and LatexFormatFactorList context factorList =
    match factorList with
    | [] -> "1"
    | [single] -> FormatLatex context single
    | first :: rest ->
        let ftext = FormatLatexPrec context first Precedence_Mul
        let rtext = LatexFormatFactorList context rest
        ftext + " " + rtext     // FIXFIXFIX - does not handle things like 3*4 ("3 4" renders like "34" in LaTeX).  Also "kilogram*meter/second^2".
