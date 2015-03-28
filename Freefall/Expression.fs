module Freefall.Expr

type Number =
    | Rational of int64 * int64     // a perfect ratio of 64-bit signed integers encoded as a tuple (numerator, denominator)
    | Real of float                 // an inexact floating point value

type Expression =
    | Number of Number
    | Unit of string                // a physical unit name like "kilogram" or "mile"
    | Variable of string
