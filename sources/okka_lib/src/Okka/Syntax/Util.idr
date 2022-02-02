module Okka.Syntax.Util


public export
record Loc where
    constructor MkLoc
    line : Int
    col : Int
