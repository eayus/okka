module Okka.Core.Terms

import Data.Fin
import Data.Vect


mutual
    public export
    data CExpr : (scope : Nat) -> Type where
        CVar : Fin scope -> CExpr scope
        CApp : (funTy : CExpr scope) -> (argTy : CExpr scope) -> CExpr scope -> CExpr scope -> CExpr scope
        CLam : CExpr (S scope) -> CExpr scope
        CPi  : CExpr scope -> CExpr (S scope) -> CExpr scope
        CUni : CExpr scope

        -- TODO: perhaps unify CUni and other prim types under "CPrimTy"
        CI32 : CExpr scope


    public export
    data CProgram : Nat -> Type where
        Nil : CProgram scope
        (::) : CExpr scope -> CProgram (S scope) -> CProgram scope


    public export
    data CNf : (scope : Nat) -> Type where
        CNfNeu : CNe scope -> CNf scope
        CNfLam : CClosure scope -> CNf scope


    public export
    data CNe : (scope : Nat) -> Type where
        CNeVar : Fin scope -> CNe scope
        CNeApp : (funTy : CNf scope) -> (argTy : CNf scope) -> CNe scope -> CNf scope -> CNe scope
        CNePi  : CNf scope -> CClosure scope -> CNe scope
        CNeUni : CNe scope
        CNeI32 : CNe scope


    public export
    CEnv : (scope : Nat) -> (len : Nat) -> Type
    CEnv scope len = Vect len (CNf scope)


    public export
    record CClosure (scope : Nat) where
        constructor MkCClosure
        env : CEnv scope scope'
        body : CExpr (S scope')
