module Okka.Core.Terms

import Data.Fin
import Data.Vect
import Data.Nat


public export
data CPrimTy : Type where
    TUni : CPrimTy
    TI32 : CPrimTy


mutual
    public export
    data CExpr : (scope : Nat) -> Type where
        CVar : Fin scope -> CExpr scope
        CApp : (funTy : CExpr scope) -> (argTy : CExpr scope) -> CExpr scope -> CExpr scope -> CExpr scope
        CLam : CExpr (S scope) -> CExpr scope
        CPi  : CExpr scope -> CExpr (S scope) -> CExpr scope
        CPT  : CPrimTy -> CExpr scope

        CLit : Int -> CExpr scope
        CAdd : CExpr scope


    public export
    data CProgram : Nat -> Type where
        Nil : CProgram scope
        (::) : Maybe (CExpr scope) -> CProgram (S scope) -> CProgram scope


    public export
    data CNf : (scope : Nat) -> Type where
        CNfNeu : CNe scope -> CNf scope
        CNfLam : CClosure scope -> CNf scope

        CNfPrim : CPrimClosure scope -> CNf scope


    public export
    data CNe : (scope : Nat) -> Type where
        CNeVar : Fin scope -> CNe scope
        CNeApp : (funTy : CNf scope) -> (argTy : CNf scope) -> CNe scope -> CNf scope -> CNe scope
        CNePi  : CNf scope -> CClosure scope -> CNe scope
        CNePT  : CPrimTy -> CNe scope

        CNeLit : Int -> CNe scope
        CNeAdd : CNe scope



    public export
    CEnv : (scope : Nat) -> (len : Nat) -> Type
    CEnv scope len = Vect len (CNf scope)


    public export
    record CClosure (scope : Nat) where
        constructor MkCClosure
        env : CEnv scope scope'
        body : CExpr (S scope')


    public export
    record CPrimClosure (scope : Nat) where
        constructor MkCPrimClosure
        arity : Nat
        argc  : Nat
        runPrim : (Vect arity (CNf scope) -> CNf scope)
        args : Vect argc (CNf scope)
        -- 0 part : argc `LT` arity
