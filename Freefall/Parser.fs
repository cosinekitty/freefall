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
    | Some {Filename=filename} -> Some(filename)

let RequireToken scan =
    match scan with
    | [] -> raise (UnexpectedEndException None)
    | {Kind=TokenKind.EndOfFile; Origin=origin} :: _ -> raise (UnexpectedEndException (FileNameFromOrigin origin))
    | _::_ -> scan

let Impossible () = failwith "Internal error - this should not be possible!"

let ExpectToken text scan =
    match RequireToken scan with
    | {Text=actual} :: scan2 as token when actual=text -> scan2
    | token :: _ -> SyntaxError token (sprintf "Expected '%s'" text)
    | _ -> Impossible ()

let ExpectSemicolon = ExpectToken ";"

let ExtractStringLiteralValue token =
    if token.Kind = TokenKind.StringLiteral then
        if IsStringLiteralText token.Text then
            token.Text.Substring(1, token.Text.Length-2)    // remove surrounding quotes
        else
            SyntaxError token "Internal error - invalid string literal was scanned."
    else
        SyntaxError token "Expected a string literal."

let ExpectStringLiteral scan =
    match RequireToken scan with
    | ltoken :: scan2 -> (ExtractStringLiteralValue ltoken), scan2
    | _ -> Impossible ()

let RequireExactlyOneArg funcName argList =
    match argList with
    | [arg] -> arg
    | _ -> SyntaxError funcName "Function requires exactly 1 argument."

let RequireExactlyTwoArgs funcName argList =
    match argList with
    | [a ; b] -> (a, b)
    | _ -> SyntaxError funcName "Function requires exactly 2 arguments."

//---------------------------------------------------------------------------------------
// Expression parser

let rec ParseExpression scan =
    let expr, scan2 = ParseAddSub scan
    match scan2 with
    | {Text="="} :: scan3 ->
        let right, scan4 = ParseAddSub scan3
        (Equals(expr,right)), scan4
    | _ ->
        expr, scan2

and ParseAddSub scan =
    let mutable expr, xscan = ParseDivMul scan
    let termlist = new ResizeArray<Expression>()
    termlist.Add(expr)

    while NextTokenHasPrecedence Precedence_Add xscan do
        let op = List.head xscan
        let right, yscan = ParseDivMul (List.tail xscan)
        xscan <- yscan
        if op.Text = "+" then
            termlist.Add(right)
        elif op.Text = "-" then
            termlist.Add(MakeNegative right)
        else
            SyntaxError op "Unsupported addop."

    if termlist.Count = 1 then
        expr, xscan
    else
        Sum(List.ofSeq termlist), xscan

and ParseDivMul scan =
    let mutable expr, xscan = ParseNegPow scan
    let factorlist = new ResizeArray<Expression>()
    factorlist.Add(expr)

    while NextTokenHasPrecedence Precedence_Mul xscan do
        let op = List.head xscan
        let right, yscan = ParseNegPow (List.tail xscan)
        xscan <- yscan
        if op.Text = "*" then 
            factorlist.Add(right)
        elif op.Text = "/" then
            // Special case: parser directly converts consecutive integers surrounded by "/"
            // into a single rational number.  That way, "3/4" is Rational(3,4) instead of
            // Rational(3,1) * Rational(1,4).
            match factorlist.[factorlist.Count-1], right with
            | Amount(PhysicalQuantity(Rational(lnumer,ldenom),lconcept)) as left, Amount(PhysicalQuantity(Rational(rnumer,rdenom),rconcept))
                when ldenom = 1I && lconcept = Dimensionless && rdenom = 1I && rconcept = Dimensionless ->
                    factorlist.[factorlist.Count-1] <- Amount(PhysicalQuantity((MakeRational lnumer rnumer), Dimensionless))
            | _, _ -> 
                factorlist.Add(MakeReciprocal right)
        else
            SyntaxError op "Unsupported multop"

    if factorlist.Count = 1 then
        factorlist.[0], xscan
    else
        Product(List.ofSeq factorlist), xscan

and ParseNegPow scan =
    match RequireToken scan with

    | ({Text="-"} as negop) :: rscan ->
        let right, xscan = ParseNegPow rscan
        MakeNegative right, xscan

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

    | {Text=")"} :: scan2 -> 
        [], scan2

    | _ ->
        let expr, scan2 = ParseExpression scan
        match scan2 with
        | {Text=","} :: scan3 ->
            let restArgs, scan4 = ParseArgList scan3
            (expr :: restArgs), scan4
        
        | {Text=")"} :: scan3 ->
            [expr], scan3

        | badtoken :: _ ->
            SyntaxError badtoken "Expected ',' or ')' after function argument expression."

        | [] ->
            raise (UnexpectedEndException None)

and ParseAtom scan =
    match RequireToken scan with

    | [] -> Impossible ()    // RequireToken already checks this case, but I want to eliminate warning here.

    | ({Kind=TokenKind.Identifier} as funcName) :: {Text="("} :: scan2 ->
        let argList, scan3 = ParseArgList scan2
        Functor(funcName,argList), scan3

    | ({Kind=TokenKind.PseudoFunction} as funcName) :: {Text="("} :: scan2 ->
        let argList, scan3 = ParseArgList scan2
        let expr = 
            match funcName.Text with
            | "neg"   -> MakeNegative (RequireExactlyOneArg funcName argList)
            | "pow"   -> 
                let a, b = RequireExactlyTwoArgs funcName argList
                Power(a,b)
            | "prod"  -> Product(argList)
            | "recip" -> MakeReciprocal(RequireExactlyOneArg funcName argList)
            | "sum"   -> Sum(argList)
            | _ -> SyntaxError funcName "Internal error - unsupported pseudo-function."
        expr, scan3

    | ({Kind=TokenKind.Identifier} as token) :: rscan ->
        (Solitaire(token)), rscan     // "solitaire" is a word for a lone symbol that only context can distinguish between variable, unit, or concept.

    | ({Kind=TokenKind.ImagFloatLiteral; Text=text} as imagtoken) :: rscan ->
        if not (text.EndsWith("i")) then
            SyntaxError imagtoken "Internal error - imaginary literal should have ended with 'i'"
        else
            let isValid, imagvalue = System.Double.TryParse(text.Substring(0, text.Length-1))
            if isValid then
                (Amount(PhysicalQuantity(Complex(complex(0.0, imagvalue)), Dimensionless))), rscan
            else
                SyntaxError imagtoken "Imaginary literal is not valid."

    | ({Kind=TokenKind.RealFloatLiteral; Text=text} as realtoken) :: rscan ->
        let isValid, realvalue = System.Double.TryParse(text)
        if isValid then
            (Amount(PhysicalQuantity(Real(realvalue), Dimensionless))), rscan
        else
            SyntaxError realtoken "Real literal is not valid."

    | ({Kind=TokenKind.IntegerLiteral; Text=text} as inttoken) :: rscan ->
        let isValid, intvalue = bigint.TryParse(text)
        if isValid then
            (Amount(PhysicalQuantity(Rational(intvalue,1I), Dimensionless))), rscan
        else
            SyntaxError inttoken "Integer literal is not valid."

    | {Text="("} :: xscan ->
        let expr, yscan = ParseExpression xscan
        match yscan with
        | {Text=")"} :: zscan -> expr, zscan
        | [] -> raise (UnexpectedEndException None)
        | badtoken :: zscan -> SyntaxError badtoken "Expected ')'"

    | ({Kind=TokenKind.ExpressionReference; Text=reftext} as reftoken) :: xscan ->
        if reftext = "#" then
            // A reference to the previous expression statement.
            PrevExprRef(reftoken), xscan
        elif reftext.StartsWith("#") then
            // A reference to a particular expression statement.
            let isValid, index = System.Int32.TryParse(reftext.Substring(1))
            if isValid && (index >= 0) then
                NumExprRef(reftoken,index), xscan
            else
                SyntaxError reftoken "Internal error - invalid integer after '#'"
        else
            SyntaxError reftoken "Internal error - parsed invalid expression reference"

    | ({Text="@"} as deltoken) :: scan2 ->
        // "@" can appear 1 or more times, indicating the order of differentiation.
        let mutable scan3 = scan2
        let mutable order = 1
        while (not (List.isEmpty scan3) && (List.head scan3).Text = "@") do
            scan3 <- List.tail scan3
            order <- 1 + order
        match RequireToken scan3 with
        | [] -> Impossible ()
        | vartoken :: scan4 ->
            if vartoken.Kind = TokenKind.Identifier then
                Del(vartoken,order), scan4
            else
                SyntaxError vartoken "Expected variable after differential operator(s)."

    | badtoken :: _ -> 
        SyntaxError badtoken "Syntax error."

let ParseIntegerValuedExpression scan =
    let expr, scan2 = ParseAddSub scan
    let number = EvalDimensionlessNumber expr
    match number with
    | Rational(a,b) ->
        if b.IsOne then
            a, scan2
        else
            ExpressionError expr "Integer value required, but found non-integer rational."
    | Real(_) -> ExpressionError expr "Integer value required, but found real."
    | Complex(_) -> ExpressionError expr "Integer value required, but found complex."

//---------------------------------------------------------------------------------------
// Statement parser

let rec ParseIdentList scan terminator =
    match RequireToken scan with

    | [] -> Impossible ()   // RequireToken already checks this case, but I want to eliminate warning here.

    | ({Kind=TokenKind.Identifier} as vartoken) :: punc :: xscan ->
        if punc.Text = "," then
            let restlist, yscan = ParseIdentList xscan terminator
            (vartoken::restlist), yscan
        elif punc.Text = terminator then
            [vartoken], xscan
        else
            SyntaxError punc (sprintf "Expected ',' or '%s' after variable name" terminator)

    | token :: _ ->
        SyntaxError token "Expected identifier"

let ValidateRange errorToken range =
    if IsEmptyRange range then
        SyntaxError errorToken "This numeric range is an empty set."
    else
        range

let MakeIntegerRange errorToken lowerBound upperBound =
    ValidateRange errorToken (IntegerRange(lowerBound,upperBound))

let ParseTypeAndSemicolon scan =
    // type ::= typename [expr] | expr 
    //
    //      In the above rule, expr is a concept expression, e.g., distance/time
    //
    // typename ::= "complex" | "real" | "rational" | "integer" [intrange]
    // intrange ::= "[" [numexpr] "," [numexpr] "]"       // numexpr(s) must evaluate to integers
    match RequireToken scan with 

    | {Kind=TokenKind.NumericRangeName; Text=text} :: {Text=";"} :: scan2 ->
        UnboundedRange text, AmountOne, scan2   // range present but concept absent means concept defaults to dimensionless unity

    | {Kind=TokenKind.NumericRangeName; Text=text} :: {Text="["} :: {Text=","} :: {Text="]"} :: scan2 ->
        UnboundedRange text, AmountOne, (ExpectSemicolon scan2)

    | ({Text="integer"} as token) :: {Text="["} :: {Text=","} :: scan2 ->       // omitted lower bound = negative infinity
        let upperLimit, scan3 = ParseIntegerValuedExpression scan2
        let scan4 = scan3 |> ExpectToken "]" |> ExpectSemicolon
        let range = MakeIntegerRange token NegInf (FiniteLimit(upperLimit))
        range, AmountOne, scan4

    | ({Text="integer"} as token) :: {Text="["} :: scan2 ->                     // explicit lower bound
        let lowerLimit, scan3 = ParseIntegerValuedExpression scan2
        let scan4 = ExpectToken "," scan3
        match scan4 with
        | {Text="]"} :: scan5 -> 
            // lower limit only
            let range = MakeIntegerRange token (FiniteLimit(lowerLimit)) PosInf
            range, AmountOne, (ExpectSemicolon scan5)
        | _ ->
            // lower and upper limits must both be there
            let upperLimit, scan5 = ParseIntegerValuedExpression scan4
            let scan6 = scan5 |> ExpectToken "]" |> ExpectSemicolon
            let range = MakeIntegerRange token (FiniteLimit(lowerLimit)) (FiniteLimit(upperLimit))
            range, AmountOne, scan6

    | {Kind=TokenKind.NumericRangeName; Text=text} :: scan2 ->
        let conceptExpr, scan3 = ParseExpression scan2
        UnboundedRange text, conceptExpr, (ExpectSemicolon scan3)

    | _ ->
        let conceptExpr, scan2 = ParseExpression scan
        RealRange, conceptExpr, (ExpectSemicolon scan2)       // variables declared without range, e.g. "var t : time;" default to real.


let ParseStatement scan =
    let firstTokenInStatement = List.head (RequireToken scan)

    match scan with
    | {Text=";"} :: rscan -> 
        firstTokenInStatement, DoNothing, rscan

    | ({Text="assertf"} as atoken) :: scan2 ->
        // assertf ::= "assertf" "(" str "," expr ")" ";"
        let scan3 = ExpectToken "(" scan2
        let literal, scan4 = ExpectStringLiteral scan3
        let scan5 = ExpectToken "," scan4
        let expr, scan6 = ParseExpression scan5
        let scan7 = ExpectToken ")" scan6
        let scan8 = ExpectToken ";" scan7
        firstTokenInStatement, AssertFormat {AssertToken=atoken; ExpectedFormat=literal; Expr=expr}, scan8

    | ({Text="concept"} as conceptKeywordToken) :: scan2 ->
        // concept ::= "concept" ident "=" expr ";"
        match scan2 with
        | ({Kind=TokenKind.Identifier} as idtoken) :: {Text="="} :: scan3 ->
            let expr, scan4 = ParseExpression scan3
            let scan5 = ExpectSemicolon scan4
            firstTokenInStatement, ConceptDef{ConceptName=idtoken; Expr=expr}, scan5
        | _ -> SyntaxError conceptKeywordToken "Expected 'ident = expr;' after 'concept'."

    | ({Text="forget"} as forgetToken) :: scan2 ->
        // forget ::= "forget" idspec ";"
        // idspec ::= "*" | ident { "," ident }
        match RequireToken scan2 with
        | {Text="*"} :: {Text=";"} :: scan3 -> 
            firstTokenInStatement, ForgetAllNumberedExpressions, scan3
        | _ -> 
            let idlist, scan3 = ParseIdentList scan2 ";"
            firstTokenInStatement, ForgetNamedExpressions(idlist), scan3

    | {Text="probe"} :: scan2 ->
        // "probe" expr ";"
        let expr, scan3 = ParseExpression scan2
        let scan4 = ExpectSemicolon scan3
        firstTokenInStatement, Probe(expr), scan4

    | {Text="save"} :: scan2 ->
        let filename, scan3 = ExpectStringLiteral scan2
        let scan4 = ExpectSemicolon scan3
        firstTokenInStatement, Save(filename), scan4

    | ({Text="unit"} as unitKeywordToken) :: scan2 ->
        // unit ::= "unit" ident "=" expr ";"
        match scan2 with
        | ({Kind=TokenKind.Identifier} as idtoken) :: {Text="="} :: scan3 ->
            let expr, scan4 = ParseExpression scan3
            let scan5 = ExpectSemicolon scan4
            firstTokenInStatement, UnitDef{UnitName=idtoken; Expr=expr}, scan5
        | _ -> SyntaxError unitKeywordToken "Expected 'ident = expr;' after 'unit'."

    | {Text="var"} :: scan2 ->
        // vardecl ::= "var" ident { "," ident } ":" type ";"
        let identList, scan3 = ParseIdentList scan2 ":"
        let range, conceptExpr, scan4 = ParseTypeAndSemicolon scan3
        firstTokenInStatement, VarDecl{VarNameList=identList; Range=range; ConceptExpr=conceptExpr}, scan4

    | ({Kind=TokenKind.Identifier} as target) :: {Text=":="} :: rscan ->
        let expr, xscan = ParseExpression rscan
        firstTokenInStatement, Assignment{TargetName=Some(target); Expr=expr}, (ExpectSemicolon xscan)

    | _ ->
        let expr, xscan = ParseExpression scan
        firstTokenInStatement, Assignment{TargetName=None; Expr=expr}, (ExpectSemicolon xscan)
