module Okka.Syntax.Check

import Okka.Syntax.Terms
import Okka.Syntax.Terms.Util
import Okka.Core.Terms
import Okka.Core.Terms.Util
import Okka.Core.Eval
import Data.Vect


record Entry (scope : Nat) where
    constructor MkEntry
    name : Ident
    type : CNf scope
    val  : CNf scope


public export
Context : (len : Nat) -> (scope : Nat) -> Type
Context len scope = Vect len (Entry scope)


weakenContext : Context len scope -> Context len (S scope)
weakenContext = believe_me


lookupCtx : Ident -> Context len scope -> Maybe (Fin len, CNf scope)
lookupCtx x [] = Nothing
lookupCtx x (entry :: xs) with (x == entry.name)
  _ | True  = Just (FZ, entry.type)
  _ | False = let rec = lookupCtx x xs in bimap Data.Fin.FS id <$> rec


toEnv : Context len scope -> CEnv scope len
toEnv = map (.val)


mutual
    infer : {scope : Nat} -> (ctx : Context scope scope) -> SExpr -> Either String (CExpr scope, CNf scope)

    infer ctx (SVar x) with (x == typeIdent)
      _ | True = Right (CUni, CNfNeu CNeUni)
      _ | False with (lookupCtx x ctx)
        _ | Nothing = Left "Undefined variable \{show x}"
        _ | Just (i, ty) = Right (CVar i, ty)

    infer ctx (SApp x y) = do
        (lhs, funTy@(CNfNeu (CNePi t uClos))) <- infer ctx x | _ => Left "Applying non pi type"
        rhs <- check ctx y t
        -- Bit messy how we reify the arg type, only to immediately eval it.
        Right (CApp (reifyNf (CNfNeu CNeUni) funTy) (reifyNf (CNfNeu CNeUni) t) lhs rhs, runClosure uClos (eval (toEnv ctx) rhs))

    infer ctx (SLam x y) = Left "Cannot infer type for lambda"

    infer ctx (SPi name t u) = do
        t' <- check ctx t (CNfNeu CNeUni)
        u' <- check (MkEntry name (weakenNf $ eval (toEnv ctx) t') (CNfNeu $ CNeVar last) :: weakenContext ctx) u (CNfNeu CNeUni)
        Right (CPi t' u', CNfNeu CNeUni)


    check : {scope : Nat} -> (ctx : Context scope scope) -> SExpr -> CNf scope -> Either String (CExpr scope)

    check ctx (SLam name body) (CNfNeu (CNePi t u)) = do
        body' <- check (MkEntry name (weakenNf t) (CNfNeu $ CNeVar last) :: weakenContext ctx) body (runClosure (weakenClos u) (CNfNeu $ CNeVar last))
        Right $ CLam body'

    check ctx (SLam name body) t = Left "Expected non-function, but expression is a lambda"

    check ctx x t = do
        (x', t') <- infer ctx x
        case nfEqual t t' of
             False => let names = map (.name) ctx in Left "Type mismatch between:\n\{showNF names t}\n\{showNF names t'}"
             True => pure x'


checkFunction : {scope : Nat} -> (ctx : Context scope scope) -> SFunction -> Either String (CExpr scope, CNf scope)
checkFunction ctx func = do
    ty <- check ctx func.type (CNfNeu CNeUni)
    let ty' = eval (toEnv ctx) ty
    body <- check ctx func.body ty'
    Right (body, ty')


export
checkProgram : {scope : Nat} -> (ctx : Context scope scope) -> SProgram -> Either String (CProgram scope)
checkProgram ctx [] = Right []
checkProgram ctx (x :: xs) = do
    (x', ty) <- checkFunction ctx x
    prog' <- checkProgram (MkEntry x.name (weakenNf ty) (weakenNf $ eval (toEnv ctx) x') :: weakenContext ctx) xs
    Right (x' :: prog')
