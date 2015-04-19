module Freefall.Html
open System.IO;
open Freefall.Scanner
open Freefall.Expr
open Freefall.Calculus
open Freefall.Stmt
open Freefall.Parser
open Freefall.Latex

let HtmlSave context filename =
    use output = File.CreateText(filename)
    output.WriteLine("<html>")
    output.WriteLine("</html>")