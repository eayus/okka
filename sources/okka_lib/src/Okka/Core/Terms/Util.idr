module Okka.Core.Terms.Util

import Okka.Core.Terms
import Okka.Syntax.Terms
import Data.Vect
import Util.Fin


mutual
    public export
    showNF : {scope : Nat} -> Vect scope Ident -> CNf scope -> String
    showNF names (CNfNeu x) = showNE names x
    showNF names (CNfLam x) = "(Lam ...)"

    public export
    showNE : {scope : Nat} -> Vect scope Ident -> CNe scope -> String
    showNE names (CNeVar x) with (index (complement x) names)
      _ | (MkIdent name) = name
    showNE names (CNeApp funTy argTy x y) = "(App \{showNE names x} \{showNF names y})"
    showNE names (CNePi x y) = "(\{showNF names x} -> ...)"
    showNE names CNeUni = "Type"
