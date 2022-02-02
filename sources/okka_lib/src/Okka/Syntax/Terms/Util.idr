module Okka.Syntax.Terms.Util

import Okka.Syntax.Terms

%default total


public export
Eq Ident where
    (MkIdent x) == (MkIdent y) = x == y


public export
Show Ident where
    show (MkIdent x) = show x


public export
Show SExpr where
    show (SVar v)        = show v
    show (SApp x y)      = "(App \{show x} \{show y})"
    show (SLam name x)   = "(Lam \{show name} \{show x})"
    show (SPi  name t u) = "(Pi \{show name} \{show t} \{show u})"


public export
Show SFunction where
    show func = "def \{show func.name} : \{show func.type} = \{show func.body};\n"
