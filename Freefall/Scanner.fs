module Freefall.Scanner
open System.Text.RegularExpressions
open Microsoft.FSharp.Collections

let TokenRegex = 
    new Regex("""
          [A-Za-z_][A-Za-z_0-9]*                    # identifier or reserved word
        | [0-9]+(\.[0-9]*)?([eE][\+\-]?[0-9]+)?i?   # real or imaginary constant with optional scientific notation
        | \#[0-9]*                                  # eref: reference to prior expression
        | //[^\n]*                                  # comment -- eats the rest of the line
        | "[^"]*"                                   # string literal
        | <= | >= | !=                              # multi-character comparison operators
        | :=                                        # assignment operator
        | \S                                        # all other non-whitespace single chars are tokens
    """ 
    , RegexOptions.IgnorePatternWhitespace)

type TokenKind = 
    | Keyword
    | NumericRangeName
    | Operator
    | Identifier
    | PseudoFunction        // sum, prod, recip, neg, pow: not in symbol table, yet must be prevented from use as identifiers
    | ExpressionReference
    | IntegerLiteral
    | RealFloatLiteral
    | ImagFloatLiteral
    | StringLiteral
    | Punctuation
    | EndOfFile         // sentinel value that lets us report which file we found unexpected EOF in

type TokenOrigin = {
    Filename: string
    LineNumber: int
}

type Token = { 
    Text: string
    Precedence: int
    Kind: TokenKind
    Origin: option<TokenOrigin>
    ColumnNumber: int
}

let EndOfFileToken origin = {
    Text = ""
    Precedence = -1
    Kind = EndOfFile
    Origin = origin
    ColumnNumber = -1
}

exception SyntaxException of Token * string

let SyntaxError token message =
    raise (SyntaxException(token,message))

let Precedence_Lowest = 0
let Precedence_Or   = 2
let Precedence_And  = 3
let Precedence_Rel  = 4
let Precedence_Add  = 5
let Precedence_Mul  = 6
let Precedence_Pow  = 7
let Precedence_Neg  = 7
let Precedence_Atom = 9

let OperatorPrecedence (text:string) =
    match text with 
    | "or" -> Precedence_Or
    | "and" -> Precedence_And
    | "not" | "=" | "!=" | "<" | ">" | "<=" | ">=" -> Precedence_Rel
    | "+" | "-" -> Precedence_Add
    | "*" | "/" -> Precedence_Mul
    | "^" -> Precedence_Pow
    | "(" | ")" | "@" -> Precedence_Neg
    | _ -> Precedence_Atom

let IsIdentifier (text:string) =
    if System.String.IsNullOrEmpty(text) then
        false
    else
        let c = System.Char.ToLower(text.[0])
        ((c >= 'a') && (c <= 'z')) || (c = '_')

let IsNumericLiteral (text:string) =
    if System.String.IsNullOrEmpty(text) then
        false
    else
        let c = text.[0]
        (c >= '0') && (c <= '9')

let KeywordTable = 
    Set.ofList [ 
        "assertf"
        "concept"
        "decomp"
        "forget" 
        "probe" 
        "save"
        "unit" 
        "var" 
    ]

let IsKeyword text = Set.contains text KeywordTable 

let PseudoFunctionTable =
    Set.ofList [
        "neg"
        "pow"
        "prod"
        "recip"
        "sum"
    ]

let IsPseudoFunction text = Set.contains text PseudoFunctionTable

type IntegerLimit =
    | NegInf
    | FiniteLimit of bigint
    | PosInf

type NumericRange =         // the set of values a variable, function, etc, is allowed to range over
    | IntegerRange of IntegerLimit * IntegerLimit
    | RationalRange
    | RealRange
    | ComplexRange

let IsEmptyRange range =    // is this a range that excludes all possible values (it is an empty set)?
    match range with
    | ComplexRange -> false
    | RealRange -> false
    | RationalRange -> false
    | IntegerRange(NegInf, _) -> false
    | IntegerRange(_, PosInf) -> false
    | IntegerRange(PosInf, _) -> true
    | IntegerRange(_, NegInf) -> true
    | IntegerRange(FiniteLimit(a), FiniteLimit(b)) -> (a > b)

let IsZeroRange range =     // is this a range that contains only the value 0?
    match range with
    | ComplexRange -> false
    | RealRange -> false
    | RationalRange -> false
    | IntegerRange(NegInf, _) -> false      // this is an infinite set, not {0}
    | IntegerRange(PosInf, _) -> false      // this is an empty set, not {0}
    | IntegerRange(_, PosInf) -> false      // this is an infinite set, not {0}
    | IntegerRange(_, NegInf) -> false      // this is an empty set, not {0}
    | IntegerRange(FiniteLimit(a), FiniteLimit(b)) -> (a.IsZero && b.IsZero)

let EmptyRange = IntegerRange(PosInf, NegInf)
let ZeroRange  = IntegerRange(FiniteLimit(0I), FiniteLimit(0I))

let IsRangeName text = 
    match text with
    | "integer" -> true
    | "rational" -> true
    | "real" -> true
    | "complex" -> true
    | _ -> false

let UnboundedRange text =
    match text with
    | "integer" -> IntegerRange(NegInf, PosInf)
    | "rational" -> RationalRange
    | "real" -> RealRange
    | "complex" -> ComplexRange
    | _ -> failwith "Invalid range name '%s'" text

let FormatRange r = 
    match r with
    | ComplexRange -> "complex"
    | RealRange -> "real"
    | RationalRange -> "rational"
    | IntegerRange(NegInf,PosInf) -> "integer"
    | IntegerRange(NegInf,FiniteLimit(b)) -> sprintf "integer[,%O]" b
    | IntegerRange(FiniteLimit(a), PosInf) -> sprintf "integer[%O,]" a
    | IntegerRange(FiniteLimit(a),FiniteLimit(b)) -> 
        if a <= b then
            sprintf "integer[%O,%O]" a b
        else
            "empty"
    | IntegerRange(_,NegInf) -> "empty"
    | IntegerRange(PosInf,_) -> "empty"

let IsStringLiteralText (text:string) =
    (text.Length >= 2) && text.StartsWith("\"") && text.EndsWith("\"")

let ClassifyToken text precedence =
    if precedence < Precedence_Atom then
        TokenKind.Operator
    elif IsKeyword text then
        TokenKind.Keyword
    elif IsPseudoFunction text then
        TokenKind.PseudoFunction
    elif IsRangeName text then
        TokenKind.NumericRangeName
    elif IsIdentifier text then
        TokenKind.Identifier
    elif IsNumericLiteral text then
        if (text.EndsWith("i")) then
            TokenKind.ImagFloatLiteral
        elif (text.Contains("e")) || (text.Contains("E")) || (text.Contains(".")) then
            TokenKind.RealFloatLiteral
        else
            TokenKind.IntegerLiteral
    elif text.StartsWith("#") then
        TokenKind.ExpressionReference
    elif IsStringLiteralText text then
        TokenKind.StringLiteral
    else
        TokenKind.Punctuation

let MakeToken origin (m:Match): Token =
    let precedence = OperatorPrecedence m.Value
    let kind = ClassifyToken m.Value precedence
    { Text = m.Value; Precedence = precedence; Kind = kind; Origin = origin; ColumnNumber = 1 + m.Index }

let TokenizeLine lineText =
    let mc = TokenRegex.Matches(lineText)
    [for m in mc do if not (m.Value.StartsWith("//")) then yield MakeToken None m]

let TokenizeFile inFileName =
    let linesInFile = System.IO.File.ReadAllLines(inFileName) |> List.ofArray
    let TokenizeFileLine zeroBasedLineNumber lineText =
        // Use regex to split up the line into lexical units.
        let mc = TokenRegex.Matches(lineText)
        [for m in mc do if not (m.Value.StartsWith("//")) then yield MakeToken (Some({Filename = inFileName; LineNumber = 1+zeroBasedLineNumber;})) m]
    let tokensFromFile = List.mapi TokenizeFileLine linesInFile |> List.concat
    let eofSentinelToken = EndOfFileToken (Some{Filename=inFileName; LineNumber=linesInFile.Length;})
    tokensFromFile @ [eofSentinelToken]

let MoreTokensIn scan =
    match scan with
    | [] -> false
    | {Kind=TokenKind.EndOfFile;} :: _ -> false
    | _ -> true

let NextTokenHasPrecedence (precedence:int) (scan:list<Token>) =
    match scan with
    | {Precedence=p} :: _ -> p = precedence
    | _ -> false

let SynthToken text =
    let precedence = OperatorPrecedence text
    let kind = ClassifyToken text precedence
    { Text = text; Precedence = precedence; Kind = kind; Origin = None; ColumnNumber = -1 }
