module Okka.Core.Eval

import Data.Fin
import Data.Vect
import Okka.Core.Terms
import Okka.Core.Terms.Util
import Util.Error
import Util.Fin
import Data.Nat
import Decidable.Equality


intToInt : CNf scope
intToInt = CNfNeu $ CNePi (CNfNeu $ CNePT TI32) (MkCClosure [] $ CPT TI32)

export
addTy : CNf scope
addTy = CNfNeu $ CNePi (CNfNeu $ CNePT TI32) $ MkCClosure [] $ CPi (CPT TI32) (CPT TI32)

export
int3 : CNf scope
int3 = CNfNeu $ CNePi (CNfNeu $ CNePT TI32) $ MkCClosure [] $ CPi (CPT TI32) (CPi (CPT TI32) (CPT TI32))

addOp : Vect 2 (CNf scope) -> CNf scope
addOp [CNfNeu (CNeLit n), CNfNeu (CNeLit m)] = CNfNeu (CNeLit (m + n))
addOp x with (x)
  _ | [l, r] = CNfNeu (CNeApp intToInt (CNfNeu $ CNePT TI32) (CNeApp addTy (CNfNeu $ CNePT TI32) CNeAdd l) r)

-- CAREFUL! When defining a primitive op, the args are in reverse order. They are pushed on like a stack. So
-- addOp [x, y] would come from "y + x" in code.

subOp : Vect 2 (CNf scope) -> CNf scope
subOp [CNfNeu (CNeLit n), CNfNeu (CNeLit m)] = CNfNeu (CNeLit (m - n))
subOp x with (x)
  _ | [l, r] = CNfNeu (CNeApp intToInt (CNfNeu $ CNePT TI32) (CNeApp addTy (CNfNeu $ CNePT TI32) CNeSub l) r)


if0Op : Vect 3 (CNf scope) -> CNf scope
if0Op [f, t, CNfNeu (CNeLit n)] = if n == 0 then t else f
if0Op [f, t, b] = CNfNeu $ CNeApp intToInt (CNfNeu $ CNePT TI32) (CNeApp addTy (CNfNeu $ CNePT TI32) (CNeApp int3 (CNfNeu $ CNePT TI32) CNeIf0 b) t) f


mutual
    export
    eval : CEnv scope scope' -> CExpr scope' -> CNf scope
    eval env (CVar x) = index x env
    eval env (CApp funTy argTy x y) = apply (eval env funTy) (eval env argTy) (eval env x) (eval env y)
    eval env (CLam x) = CNfLam $ MkCClosure env x
    eval env (CPi x y) = CNfNeu $ CNePi (eval env x) (MkCClosure env y)
    eval env (CPT x) = CNfNeu $ CNePT x
    eval env (CLit n) = CNfNeu $ CNeLit n
    eval env CAdd = CNfPrim $ MkCPrimClosure 2 0 addOp [] --(LTESucc LTEZero)
    eval env CSub = CNfPrim $ MkCPrimClosure 2 0 subOp []
    eval env CIf0 = CNfPrim $ MkCPrimClosure 3 0 if0Op []


    export
    apply : CNf scope -> CNf scope -> CNf scope -> CNf scope -> CNf scope
    apply funTy argTy (CNfNeu x) y = CNfNeu (CNeApp funTy argTy x y)
    apply funTy argTy (CNfLam clos) arg = runClosure clos arg
    apply funTy argTy (CNfPrim f) arg = runPrimClosure f arg


    export
    runClosure : CClosure scope -> (arg : CNf scope) -> CNf scope
    runClosure clos arg = eval (arg :: clos.env) clos.body


    export
    runPrimClosure : CPrimClosure scope -> (arg : CNf scope) -> CNf scope
    runPrimClosure (MkCPrimClosure arity argc runPrim args) arg with (decEq (S argc) arity)
      runPrimClosure (MkCPrimClosure (S argc) argc runPrim args) arg | Yes Refl = runPrim (arg :: args)
      runPrimClosure (MkCPrimClosure arity argc runPrim args) arg | No neq = CNfPrim $ MkCPrimClosure arity (S argc) runPrim (arg :: args)


export
weakenNf : CNf scope -> CNf (S scope)
weakenNf = believe_me

export
weakenClos : CClosure scope -> CClosure (S scope)
weakenClos = believe_me

export
weakenPrimClos : CPrimClosure scope -> CPrimClosure (S scope)
weakenPrimClos = believe_me

export
weakenEnv : Vect len (CNf scope) -> Vect len (CNf (S scope))
weakenEnv = believe_me


mutual
    export
    reifyNf : {scope : Nat} -> (ty : CNf scope) -> (expr : CNf scope) -> CExpr scope

    reifyNf ty@(CNfNeu (CNePi t uClos)) expr =
        let arg = CNfNeu $ CNeVar last in
        CLam $ reifyNf (runClosure (weakenClos uClos) arg) (apply (weakenNf ty) (weakenNf t) (weakenNf expr) arg)

    reifyNf (CNfNeu (CNePT TUni)) (CNfNeu (CNePT x)) = CPT x

    reifyNf (CNfNeu (CNePT TUni)) (CNfNeu (CNePi t uClos)) =
        CPi (reifyNf (CNfNeu $ CNePT TUni) t) (reifyNf (CNfNeu $ CNePT TUni)
            (runClosure (weakenClos uClos) (CNfNeu $ CNeVar last)))

    reifyNf ty (CNfNeu x) = reifyNe ty x


    -- I belive that NfPrim will always have a Pi type, which is already covered.
    reifyNf _ (CNfPrim f) =
        error "[Exception]: 'reifyNf' case id=5 unexpected."

    reifyNf (CNfNeu (CNeLit _)) (CNfLam _) =
        error "[Exception]: 'reifyNf' case id=4 unexpected."

    -- These may not be correct, since when we have abstract types.
    reifyNf (CNfNeu (CNeVar x)) expr =
        -- Not sure this is correct
        error "[Exception]: 'reifyNf' case id=3 unexpected."

    reifyNf (CNfNeu (CNeApp funTy argTy x y)) expr =
        -- Not sure this is correct
        error "[Exception]: 'reifyNf' case id=2 unexpected."

    -- Lambdas always will have a Pi type, which is already covered.
    reifyNf _ (CNfLam x) =
        error "[Exception]: 'reifyNf' case id=1 unexpected."

    reifyNf (CNfLam x) expr =
        error "[Exception]: 'reifyNf' case id=0 unexpected."


    export
    reifyNe : {scope : Nat} -> (ty : CNf scope) -> (expr : CNe scope) -> CExpr scope

    reifyNe ty (CNeVar x) = CVar $ complement x

    reifyNe ty (CNeApp funTy argTy x y) =
        let funTy' = reifyNf (CNfNeu $ CNePT TUni) funTy
            argTy' = reifyNf (CNfNeu $ CNePT TUni) argTy
        in CApp funTy' argTy' (reifyNe funTy x) (reifyNf argTy y)

    reifyNe ty (CNePi x y) = CPi (reifyNf (CNfNeu $ CNePT TUni) x) (reifyNf (CNfNeu $ CNePT TUni) (runClosure (weakenClos y) (CNfNeu $ CNeVar last)))

    reifyNe ty (CNePT x) = CPT x

    reifyNe ty (CNeLit n) = CLit n

    reifyNe ty CNeAdd = CAdd
    reifyNe ty CNeSub = CSub
    reifyNe ty CNeIf0 = CIf0


mutual
    export
    neEqual : {scope : Nat} -> (x, y : CNe scope) -> Bool

    neEqual (CNeVar v) (CNeVar v') = v == v'

    neEqual (CNeApp _ _ x y) (CNeApp _ _ x' y') = neEqual x x' && nfEqual y y'

    neEqual (CNePi t u) (CNePi t' u') =
         let var = CNfNeu $ CNeVar last
         in nfEqual t t' && nfEqual (runClosure (weakenClos u) var) (runClosure (weakenClos u') var)

    neEqual (CNePT x) (CNePT y) = x == y

    neEqual (CNeLit n) (CNeLit m) = n == m

    neEqual CNeAdd CNeAdd = True
    neEqual CNeSub CNeSub = True
    neEqual CNeIf0 CNeIf0 = True

    neEqual _ _ = False

    
    export
    nfEqual : {scope : Nat} -> (x, y : CNf scope) -> Bool
    nfEqual (CNfNeu x) (CNfNeu y) = neEqual x y
    nfEqual (CNfLam x) (CNfLam y) = let var = CNfNeu $ CNeVar last in nfEqual (runClosure (weakenClos x) var) (runClosure (weakenClos y) var)
    nfEqual (CNfPrim x) (CNfPrim y) = let var = CNfNeu $ CNeVar last in nfEqual (runPrimClosure (weakenPrimClos x) var) (runPrimClosure (weakenPrimClos y) var)
    nfEqual _          _          = False
