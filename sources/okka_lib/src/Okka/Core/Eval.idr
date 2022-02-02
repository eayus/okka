module Okka.Core.Eval

import Data.Fin
import Data.Vect
import Okka.Core.Terms
import Util.Error
import Util.Fin


mutual
    export
    eval : CEnv scope scope' -> CExpr scope' -> CNf scope
    eval env (CVar x) = index x env
    eval env (CApp funTy argTy x y) = apply (eval env funTy) (eval env argTy) (eval env x) (eval env y)
    eval env (CLam x) = CNfLam $ MkCClosure env x
    eval env (CPi x y) = CNfNeu $ CNePi (eval env x) (MkCClosure env y)
    eval env CUni = CNfNeu CNeUni


    export
    apply : CNf scope -> CNf scope -> CNf scope -> CNf scope -> CNf scope
    apply funTy argTy (CNfNeu x) y = CNfNeu (CNeApp funTy argTy x y)
    apply funTy argTy (CNfLam clos) arg = runClosure clos arg


    export
    runClosure : CClosure scope -> (arg : CNf scope) -> CNf scope
    runClosure clos arg = eval (arg :: clos.env) clos.body



export
weakenNf : CNf scope -> CNf (S scope)
weakenNf = believe_me

export
weakenClos : CClosure scope -> CClosure (S scope)
weakenClos = believe_me

export
weakenEnv : Vect len (CNf scope) -> Vect len (CNf (S scope))
weakenEnv = believe_me


mutual
    export
    reifyNf : {scope : Nat} -> (ty : CNf scope) -> (expr : CNf scope) -> CExpr scope

    reifyNf ty@(CNfNeu (CNePi t uClos)) expr =
        let arg = CNfNeu $ CNeVar last in
        CLam $ reifyNf (runClosure (weakenClos uClos) arg) (apply (weakenNf ty) (weakenNf t) (weakenNf expr) arg)

    reifyNf (CNfNeu CNeUni) (CNfNeu CNeUni) = CUni

    reifyNf (CNfNeu CNeUni) (CNfNeu (CNePi t uClos)) =
        CPi (reifyNf (CNfNeu CNeUni) t) (reifyNf (CNfNeu CNeUni)
            (runClosure (weakenClos uClos) (CNfNeu $ CNeVar last)))

    reifyNf ty (CNfNeu x) = reifyNe ty x

    reifyNf (CNfNeu (CNeVar x)) expr =
        -- Not sure this is correct
        error "[Exception]: 'reifyNf' case id=3 unexpected."

    reifyNf (CNfNeu (CNeApp funTy argTy x y)) expr =
        -- Not sure this is correct
        error "[Exception]: 'reifyNf' case id=2 unexpected."

    reifyNf (CNfNeu CNeUni) (CNfLam x) =
        error "[Exception]: 'reifyNf' case id=1 unexpected."

    reifyNf (CNfLam x) expr =
        error "[Exception]: 'reifyNf' case id=0 unexpected."


    export
    reifyNe : {scope : Nat} -> (ty : CNf scope) -> (expr : CNe scope) -> CExpr scope

    reifyNe ty (CNeVar x) = CVar $ complement x

    reifyNe ty (CNeApp funTy argTy x y) =
        let funTy' = reifyNf (CNfNeu CNeUni) funTy
            argTy' = reifyNf (CNfNeu CNeUni) argTy
        in CApp funTy' argTy' (reifyNe funTy x) (reifyNf argTy y)

    reifyNe ty (CNePi x y) = CPi (reifyNf (CNfNeu CNeUni) x) (reifyNf (CNfNeu CNeUni) (runClosure (weakenClos y) (CNfNeu $ CNeVar last)))

    reifyNe ty CNeUni = CUni


mutual
    export
    neEqual : {scope : Nat} -> (x, y : CNe scope) -> Bool

    neEqual (CNeVar v) (CNeVar v') = v == v'

    neEqual (CNeApp _ _ x y) (CNeApp _ _ x' y') = neEqual x x' && nfEqual y y'

    neEqual (CNePi t u) (CNePi t' u') =
         let var = CNfNeu $ CNeVar last
         in nfEqual t t' && nfEqual (runClosure (weakenClos u) var) (runClosure (weakenClos u') var)

    neEqual CNeUni CNeUni = True

    neEqual _ _ = False

    
    export
    nfEqual : {scope : Nat} -> (x, y : CNf scope) -> Bool
    nfEqual (CNfNeu x) (CNfNeu y) = neEqual x y
    nfEqual (CNfLam x) (CNfLam y) = let var = CNfNeu $ CNeVar last in nfEqual (runClosure (weakenClos x) var) (runClosure (weakenClos y) var)
    nfEqual _          _          = False
