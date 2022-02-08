module Okka.Core.Terms.Util

import Okka.Core.Terms
import Okka.Syntax.Terms
import Data.Vect
import Util.Fin


public export
Show CPrimTy where
    show TUni = "Type"
    show TI32 = "Int32"


public export
Eq CPrimTy where
    TUni == TUni = True
    TI32 == TI32 = True
    _    == _    = False


mutual
    public export
    showNF : {scope : Nat} -> Vect scope Ident -> CNf scope -> String
    showNF names (CNfNeu x) = showNE names x
    showNF names (CNfLam x) = "(Lam ...)"
    showNF names (CNfPrim f)  = "(PrimFunc ...)"

    public export
    showNE : {scope : Nat} -> Vect scope Ident -> CNe scope -> String
    showNE names (CNeVar x) with (index (complement x) names)
      _ | (MkIdent name) = name
    showNE names (CNeApp funTy argTy x y) = "(\{showNE names x} \{showNF names y})"
    showNE names (CNePi x y) = "(\{showNF names x} -> ...)"
    showNE names (CNePT x) = show x
    showNE names (CNeLit n) = show n
    showNE names CNeAdd  = "Add"
    showNE names CNeSub  = "Sub"
    showNE names CNeIf0  = "If0"
