module Freefall.Html
open System.IO;
open Freefall.Scanner
open Freefall.Expr
open Freefall.Calculus
open Freefall.Stmt
open Freefall.Parser
open Freefall.Latex

let HtmlPrefix = """<!DOCTYPE html>
<html>
<head>
<title>Freefall</title>
<script type="text/x-mathjax-config">
MathJax.Hub.Config({
  TeX: { equationNumbers: { autoNumber: "AMS" } }
});
MathJax.Hub.Config({tex2jax: {inlineMath: [['$','$'], ['\\(','\\)']]}});
</script>
<script src="http://cdn.mathjax.org/mathjax/latest/MathJax.js?config=TeX-AMS_HTML"></script>
</head>
<body>
"""

let HtmlSave (context:Context) filename =
    use output = File.CreateText(filename)
    output.WriteLine(HtmlPrefix)
    for equation in context.NumberedExpressionList do
        output.WriteLine("\\begin{equation}")
        output.WriteLine(FormatLatex context equation)
        output.WriteLine("\\end{equation}")
    output.WriteLine("</body></html>")