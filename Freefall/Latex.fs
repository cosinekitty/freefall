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
    let prec = if x < 0.0 then Precedence_Neg else Precedence_Atom
    if eIndex < 0 then
        text, prec
    else
        // "1.23e-5" ==> "1.23x10^(-5)"  (only in Latex format, of course)
        let mantissa = text.Substring(0, eIndex)
        let exponent = System.Int32.Parse(text.Substring(eIndex+1))
        sprintf @"%s\times 10^{%d}" mantissa exponent, Precedence_Mul

let LatexFormatNumber x =
    match x with
    | Rational(numer,denom) ->
        if denom.IsZero then
            raise (FreefallRuntimeException("Rational number had zero denominator."))
        elif denom.IsOne then
            numer.ToString(), if numer.Sign < 0 then Precedence_Neg else Precedence_Atom
        else
            sprintf @"\frac{%O}{%O}" numer denom, Precedence_Atom

    | Real(x) -> 
        LatexRealString x

    | Complex(c) -> 
        // (-3.4-5.6i)
        // (-3.4+5.6i)
        let rtext, _ = LatexRealString c.Real
        let itextRaw, _ = LatexRealString c.Imaginary
        let itext =
            if c.Imaginary >= 0.0 then
                "+" + itextRaw
            else
                itextRaw
        sprintf @"\left(%s%si\right)" rtext itext, Precedence_Atom


let LatexFormatDimension name (numer:bigint, denom:bigint) =
    if numer.IsZero then
        ""      // this dimension does not contribute to formatting, e.g. meter^0
    else
        sprintf @"\mathrm{%s}" name +
            if numer.IsOne && denom.IsOne then
                ""    // meter^(1/1) is written as "meter"
            elif denom.IsOne then
                sprintf "^{%O}" numer
            else
                sprintf @"^{\frac{%O}{%O}}" numer denom

let LatexAccumDimension prefix name (numer,denom) =
    let text = LatexFormatDimension name (numer,denom)
    match (prefix,text) with
    | ("","") -> ""
    | ("",_)  -> text
    | (_,"")  -> prefix
    | (_,_)   -> prefix + @" \cdot " + text

let LatexFormatDimensions namelist concept =
    match concept with
    | ConceptZero -> "0"
    | Concept(powlist) -> List.fold2 LatexAccumDimension "" namelist powlist

let LatexFormatUnits concept =
    let text = LatexFormatDimensions BaseUnitNames concept
    if text.Contains(@" \cdot ") then
        text, Precedence_Mul
    elif text.Contains("^") then
        text, Precedence_Pow
    else
        text, Precedence_Atom

let LatexFormatQuantity context (PhysicalQuantity(scalar,concept)) =
    let text, precedence =
        if IsNumberZero scalar then
            "0", Precedence_Atom     // special case because zero makes all units irrelevant
        else
            let scalarText, scalarPrec = LatexFormatNumber scalar
            let unitsText, unitsPrec = LatexFormatUnits concept
            if unitsText = "" then
                scalarText, scalarPrec
            elif unitsText = "0" then
                "0", Precedence_Atom
            elif scalarText = "1" then
                unitsText, unitsPrec
            else
                let stext = if scalarPrec < Precedence_Mul then sprintf @"\left(%s)\right)" scalarText else scalarText
                let utext = if unitsPrec  < Precedence_Mul then sprintf @"\left(%s)\right)" unitsText  else unitsText
                sprintf @"%s \cdot %s" stext utext, Precedence_Mul
    text, LatexFactorSeparator.LeftDot, precedence

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
        let prefix, sep = LatexFixNamePart name
        prefix, sep, Precedence_Atom
    else
        let prefix, sep = LatexFixNamePart (name.Substring(0, underscoreIndex))
        let rest, _, _ = UFixName (name.Substring(underscoreIndex+1))
        prefix + "_{" + rest + "}", sep, Precedence_Atom

let LatexFixName (name:string) =
    // Must protect ourselves from underscores at front of name, or multiple consecutive underscores.
    UFixName (Regex.Replace(Regex.Replace(name, @"^_*", ""), @"_+", "_"))

let rec FormatLatex context expr =
    let text, sep, prec = FormatLatexPrec context expr Precedence_Lowest
    text

and ListFormatLatex context argList =
    match argList with
    | [] -> ""
    | [single] -> FormatLatex context single
    | first::rest -> (FormatLatex context first) + ", " + (ListFormatLatex context rest)

and FormatLatexPrec context expr parentPrecedence : (string * LatexFactorSeparator * int) =
    let innerText, separator, precedence =
        match expr with
        | Amount(quantity) -> 
            LatexFormatQuantity context quantity

        | Solitaire(nameToken) -> 
            LatexFixName nameToken.Text

        | Functor(nameToken,argList) ->
            let func = FindFunctionEntry context nameToken
            func.LatexName + @"\left(" + ListFormatLatex context argList + @"\right)", LatexFactorSeparator.Space, Precedence_Atom

        | Sum(termList) ->
            match termList with
            | [] -> "0", LatexFactorSeparator.LeftDot, Precedence_Atom
            | [single] -> FormatLatexPrec context single Precedence_Lowest
            | first::rest -> 
                let t, s, p = FormatLatexPrec context first Precedence_Add
                t + (LatexJoinRemainingTerms context rest), s, Precedence_Add

        | Product(factorList) ->
            // Split the factor list into numerator factors and denominator factors.
            // For example: prod(pow(x,-2), y, pow(z,-1))
            // numerator list = [y]
            // denominator list = [pow(x,2); z]
            // Gets rendered as y / (x^2 * z).
            match SplitNumerDenom factorList with
            | [], [] -> "1", LatexFactorSeparator.LeftDot, Precedence_Atom
            | numerList, [] -> LatexFormatFactorList context numerList 0 parentPrecedence
            | numerList, denomList -> 
                let numerText, sep, _ = LatexFormatFactorList context numerList 0 Precedence_Lowest
                let denomText, _, _ = LatexFormatFactorList context denomList 0 Precedence_Lowest
                sprintf @"\frac{%s}{%s}" numerText denomText, sep, Precedence_Atom

        | Power(a,b) ->
            if IsExpressionEqualToRational b 1I 2I then
                let atext = FormatLatex context a
                sprintf @"\sqrt{%s}" atext, LatexFactorSeparator.Space, Precedence_Atom
            else
                let atext, sep, _ = FormatLatexPrec context a Precedence_Pow
                let btext, _, _ = FormatLatexPrec context b Precedence_Lowest
                sprintf "%s^{%s}" atext btext, sep, Precedence_Pow

        | Equals(a,b) ->
            let atext, _, _ = FormatLatexPrec context a Precedence_Rel
            let btext, _, _ = FormatLatexPrec context b Precedence_Rel
            atext + " = " + btext, LatexFactorSeparator.Space, Precedence_Rel

        | NumExprRef(hashToken,listIndex) -> FailLingeringMacro hashToken
        | PrevExprRef(hashToken) -> FailLingeringMacro hashToken

        | Del(opToken,order) ->
            let vtext = FormatLatex context (Solitaire(opToken))
            if order > 1 then
                sprintf @"\partial^{%d}%s " order vtext, LatexFactorSeparator.Space, Precedence_Atom
            else
                sprintf @"\partial %s " vtext, LatexFactorSeparator.Space, Precedence_Atom

    if parentPrecedence < precedence then
        innerText, separator, precedence
    else
        sprintf @"\left(%s\right)" innerText, LatexFactorSeparator.Space, Precedence_Atom

and LatexJoinRemainingTerms context termList =
    match termList with
    | [] -> ""
    | first::rest ->
        let rtext = LatexJoinRemainingTerms context rest

        // check for anything that looks "negative" so we can turn it into subtraction
        let ftext, separator, _ = FormatLatexPrec context first Precedence_Add

        if ftext.StartsWith("-") then
            ftext + rtext
        else
            "+" + ftext + rtext

and LatexFormatFactorList context factorList index parentPrecedence =
    match factorList with
    | [] -> 
        if index = 0 then 
            "1", LatexFactorSeparator.LeftDot, Precedence_Atom
        else 
            "", LatexFactorSeparator.Empty, Precedence_Atom

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
            let rtext, rsep, rprec = LatexFormatFactorList context rest index parentPrecedence
            if rprec < Precedence_Neg then
                sprintf @"-\left(%s\right)" rtext, LatexFactorSeparator.LeftDot, Precedence_Neg
            else
                sprintf @"-%s" rtext, LatexFactorSeparator.LeftDot, Precedence_Neg
        else
            let ftext, fsep, fprec = FormatLatexPrec context first Precedence_Lowest
            let rtext, rsep, _ = LatexFormatFactorList context rest (1+index) Precedence_Mul
            if rsep = LatexFactorSeparator.Empty then
                if fprec < parentPrecedence then
                    sprintf @"\left(%s\right)" ftext, LatexFactorSeparator.Space, Precedence_Atom
                else
                    ftext, fsep, fprec
            else
                let septext =
                    match fsep, rsep with
                    | _, LatexFactorSeparator.Empty -> failwith "Impossible rsep"
                    | LatexFactorSeparator.SurroundDots, _ -> @" \cdot "
                    | _, LatexFactorSeparator.LeftDot -> @" \cdot "
                    | _, LatexFactorSeparator.SurroundDots -> @" \cdot "
                    | _, LatexFactorSeparator.Space -> " "

                if fprec < Precedence_Mul then
                    sprintf @"\left(%s\right)%s%s" ftext septext rtext, fsep, Precedence_Mul
                else
                    ftext + septext + rtext, fsep, Precedence_Mul
