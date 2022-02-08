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
      _ | True = Right (CPT TUni, CNfNeu $ CNePT TUni)
      _ | False with (x == MkIdent "Int32")
        _ | True = Right (CPT TI32, CNfNeu $ CNePT TUni)
        _ | False with (x == MkIdent "add")
          _ | True = Right (CAdd, addTy)
          _ | False with (lookupCtx x ctx)
            _ | Nothing = Left "Undefined variable \{show x}"
            _ | Just (i, ty) = Right (CVar i, ty)

    infer ctx (SApp x y) = do
        (lhs, funTy@(CNfNeu (CNePi t uClos))) <- infer ctx x | _ => Left "Applying non pi type"
        rhs <- check ctx y t
        -- Bit messy how we reify the arg type, only to immediately eval it.
        Right (CApp (reifyNf (CNfNeu $ CNePT TUni) funTy) (reifyNf (CNfNeu $ CNePT TUni) t) lhs rhs, runClosure uClos (eval (toEnv ctx) rhs))

    infer ctx (SLam x y) = Left "Cannot infer type for lambda"

    infer ctx (SPi name t u) = do
        t' <- check ctx t (CNfNeu $ CNePT TUni)
        u' <- check (MkEntry name (weakenNf $ eval (toEnv ctx) t') (CNfNeu $ CNeVar last) :: weakenContext ctx) u (CNfNeu $ CNePT TUni)
        Right (CPi t' u', CNfNeu $ CNePT TUni)

    infer ctx (SLit n) = Right (CLit n, CNfNeu $ CNePT TI32)


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


checkFunction : {scope : Nat} -> (ctx : Context scope scope) -> SFunction -> Either String (Maybe (CExpr (S scope)), CNf scope)
checkFunction ctx func = do
    ty <- check ctx func.type (CNfNeu $ CNePT TUni)
    let ty' = eval (toEnv ctx) ty

    case func.body of
         Nothing => Right (Nothing, ty')
         Just body' => do
             body <- check (MkEntry func.name (weakenNf ty') (CNfNeu $ CNeVar last) :: weakenContext ctx) body' (weakenNf ty')
             Right (Just body, ty')


export
checkProgram : {scope : Nat} -> (ctx : Context scope scope) -> SProgram -> Either String (CProgram scope)
checkProgram ctx [] = Right []
checkProgram ctx (x :: xs) = do
    (x', ty) <- checkFunction ctx x

    let entry = case x' of
                     Just body => MkEntry x.name (weakenNf ty) (eval (CNfNeu (CNeVar last) :: weakenEnv (toEnv ctx)) body)
                     Nothing => MkEntry x.name (weakenNf ty) (CNfNeu $ CNeVar last)
    prog' <- checkProgram (entry :: weakenContext ctx) xs
    Right (x' :: prog')
