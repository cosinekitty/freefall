module Freefall.Latex
open System.Text.RegularExpressions
open Freefall.Scanner
open Freefall.Expr
open Freefall.Calculus
open Freefall.Stmt
open Freefall.Parser

type LatexFactorSeparator = Empty | Space | LeftDot | SurroundDots

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

let LatexFormatDimension name (numer:bigint, denom:bigint) =
    if numer.IsZero then
        ""      // this dimension does not contribute to formatting, e.g. meter^0
    else
        "\\mathrm{" + name + "}" +
            if numer.IsOne && denom.IsOne then
                ""    // meter^(1/1) is written as "meter"
            elif denom.IsOne then
                "^{" + numer.ToString() + "}"
            else
                "^{\\frac{" + numer.ToString() + "}{" + denom.ToString() + "}"

let LatexAccumDimension prefix name (numer,denom) =
    let text = LatexFormatDimension name (numer,denom)
    match (prefix,text) with
    | ("","") -> ""
    | ("",_)  -> text
    | (_,"")  -> prefix
    | (_,_)   -> prefix + " \\cdot " + text

let LatexFormatDimensions namelist concept =
    match concept with
    | ConceptZero -> "0"
    | Concept(powlist) -> List.fold2 LatexAccumDimension "" namelist powlist

let LatexFormatQuantity context (PhysicalQuantity(scalar,concept)) =
    let text =
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
    text, LatexFactorSeparator.LeftDot

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
            rNumerList, (Amount(PhysicalQuantity((MakeRational b a),concept)) :: rDenomList)

        | Power(x, Amount(PhysicalQuantity(Rational(a,b),concept) as quantity)) when concept = Dimensionless && a.Sign < 0 ->
            let recip =
                if IsQuantityNegOne quantity then
                    x
                else
                    Power(x, Amount(PhysicalQuantity((MakeRational -a b), Dimensionless)))
            rNumerList, (recip :: rDenomList)

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

let LatexFixNamePart (name:string) =
    if Set.contains name GreekLetterSet then
        @"\" + name, LatexFactorSeparator.Space
    elif name.Length > 1 then
        @"\mathrm{" + name + "}", LatexFactorSeparator.SurroundDots
    else
        name, LatexFactorSeparator.Space

let rec UFixName (name:string) =
    let underscoreIndex = name.IndexOf('_')
    if underscoreIndex < 0 then
        LatexFixNamePart name
    else
        let prefix, sep = LatexFixNamePart (name.Substring(0, underscoreIndex))
        let rest, _ = UFixName (name.Substring(underscoreIndex+1))
        prefix + "_{" + rest + "}", sep

let LatexFixName (name:string) =
    // Must protect ourselves from underscores at front of name, or multiple consecutive underscores.
    UFixName (Regex.Replace(Regex.Replace(name, @"^_*", ""), @"_+", "_"))

let rec FormatLatex context expr =
    let text, sep = FormatLatexPrec context expr Precedence_Or
    text

and ListFormatLatex context argList =
    match argList with
    | [] -> ""
    | [single] -> FormatLatex context single
    | first::rest -> (FormatLatex context first) + ", " + (ListFormatLatex context rest)

and FormatLatexPrec context expr parentPrecedence : (string * LatexFactorSeparator) =
    let innerText, separator =
        match expr with
        | Amount(quantity) -> 
            LatexFormatQuantity context quantity

        | Solitaire(nameToken) -> 
            LatexFixName nameToken.Text

        | Functor(nameToken,argList) ->
            let func = FindFunctionEntry context nameToken
            func.LatexName + "\\left(" + ListFormatLatex context argList + "\\right)", LatexFactorSeparator.Space

        | Sum(termList) ->
            match termList with
            | [] -> "0", LatexFactorSeparator.LeftDot
            | [single] -> FormatLatexPrec context single Precedence_Or
            | first::rest -> 
                let t, s = FormatLatexPrec context first Precedence_Add
                t + (LatexJoinRemainingTerms context rest), s

        | Product(factorList) ->
            // Split the factor list into numerator factors and denominator factors.
            // For example: prod(pow(x,-2), y, pow(z,-1))
            // numerator list = [y]
            // denominator list = [pow(x,2); z]
            // Gets rendered as y / (x^2 * z).
            match SplitNumerDenom factorList with
            | [], [] -> "1", LatexFactorSeparator.LeftDot
            | numerList, [] -> LatexFormatFactorList context numerList 0
            | numerList, denomList -> 
                let numerText, sep = LatexFormatFactorList context numerList 0
                let denomText, _ = LatexFormatFactorList context denomList 0
                "\\frac{" + numerText + "}{" + denomText + "}", sep

        | Power(a,b) ->
            if IsExpressionEqualToRational b 1I 2I then
                let atext = FormatLatex context a
                "\\sqrt{" + atext + "}", LatexFactorSeparator.Space
            else
                let atext, sep = FormatLatexPrec context a Precedence_Pow
                let btext, _ = FormatLatexPrec context b Precedence_Pow
                atext + "^{" + btext + "}", sep

        | Equals(a,b) ->
            let atext, _ = FormatLatexPrec context a Precedence_Rel
            let btext, _ = FormatLatexPrec context b Precedence_Rel
            atext + " = " + btext, LatexFactorSeparator.Space

        | NumExprRef(hashToken,listIndex) -> FailLingeringMacro hashToken
        | PrevExprRef(hashToken) -> FailLingeringMacro hashToken

        | Del(opToken,order) ->
            let vtext = FormatLatex context (Solitaire(opToken))
            if order > 1 then
                "\\partial^{" + order.ToString() + "}" + vtext, LatexFactorSeparator.Space
            else
                "\\partial " + vtext, LatexFactorSeparator.Space

    if parentPrecedence < LatexExpressionPrecedence expr then
        innerText, separator
    else
        "\\left(" + innerText + "\\right)", LatexFactorSeparator.Space

and LatexJoinRemainingTerms context termList =
    match termList with
    | [] -> ""
    | first::rest ->
        let rtext = LatexJoinRemainingTerms context rest

        // check for anything that looks "negative" so we can turn it into subtraction
        let ftext, separator = FormatLatexPrec context first Precedence_Add

        if ftext.StartsWith("-") then
            ftext + rtext
        else
            "+" + ftext + rtext

and LatexFormatFactorList context factorList index =
    match factorList with
    | [] -> 
        if index = 0 then 
            "1", LatexFactorSeparator.LeftDot 
        else 
            "", LatexFactorSeparator.Empty

    | first :: rest ->
        // There are a lot of special cases with representation of product lists.
        // prod(3,4,5) ==>  3 \cdot 4 \cdot 5
        // prod(-5,foot,-6,10) ==> -5 \cdot foot \cdot -6 \cdot 10
        // prod(-5,x) ==> -5 x
        // prod(-1,x) ==> -x
        // prod(kilogram,meter,second^2) ==> kilogram \cdot meter \cdot second^{2}
        // prod(longname,x,y) ==> longname \cdot x y
        // prod(alpha,beta) ==> \alpha \beta

        if (index = 0) && (IsExpressionNegOne first) then
            // Format prod(-1, ...) as -(...)
            let rtext, rsep = LatexFormatFactorList context rest index
            "-" + rtext, LatexFactorSeparator.Space
        else
            let ftext, fsep = FormatLatexPrec context first Precedence_Mul
            let rtext, rsep = LatexFormatFactorList context rest (1+index)
            let septext =
                match fsep, rsep with
                | _, LatexFactorSeparator.Empty -> ""
                | LatexFactorSeparator.SurroundDots, _ -> " \\cdot "
                | _, LatexFactorSeparator.LeftDot -> " \\cdot "
                | _, LatexFactorSeparator.SurroundDots -> " \\cdot "
                | _, LatexFactorSeparator.Space -> " "

            ftext + septext + rtext, fsep
