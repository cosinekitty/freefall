module Freefall.Stmt
open Scanner
open Expr

type MultiVariableDeclaration = {
    VarNameList : Token list;
    Range : NumericRange;
    ConceptExpr : Expression;
}

type AssignmentStatement = {
    TargetName : Token option;      // the optional user-specified name by which the entire expression should be known later
    Expr : Expression;
}

type Statement =
    | VarDecl of MultiVariableDeclaration
    | Assignment of AssignmentStatement
    | DoNothing

