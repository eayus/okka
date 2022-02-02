module Okka.Syntax.Terms

%default total


public export
data Ident : Type where
    MkIdent : String -> Ident
    

public export
data SExpr : Type where
    SVar : Ident -> SExpr
    SApp : SExpr -> SExpr -> SExpr
    SLam : Ident -> SExpr -> SExpr
    SPi  : Ident -> SExpr -> SExpr -> SExpr


public export
typeIdent : Ident
typeIdent = MkIdent "Type"


public export
record SFunction where
    constructor MkSFunction
    name : Ident
    type : SExpr
    body : SExpr


public export
SProgram : Type
SProgram = List SFunction
