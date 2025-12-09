{-# options_ghc -Wno-unused-imports #-}

module Elaboration where

import Common hiding (Set)
import Core.Syntax (Tm, Ty, Tm0, LocalsArg, Locals(..))
import Core.Value
import Evaluation
import Elaboration.State
import Errors
import Config

import Presyntax   qualified as P
import Core.Syntax qualified as S
import Unification qualified as U

--------------------------------------------------------------------------------

type PTmArg = (?ptm :: P.Tm)

type Elab a = LvlArg => EnvArg => LocalsArg => SrcArg => PTmArg => a

{-# inline forceElab #-}
forceElab :: Elab a -> Elab a
forceElab act = seq ?lvl (seq ?env (seq ?locals (seq ?src act)))

-- | Add a local definition.
{-# inline define #-}
define :: Name -> Ty -> VTy -> Tm -> Val -> Elab (Val -> IO a) -> Elab (IO a)
define x a va t vt act =
  let val     = LocalDef ?lvl va vt in
  let ?lvl    = ?lvl + 1
      ?env    = EDef ?env val
      ?locals = LDef ?locals x t a in
  forceElab $ localDefineIS x va (act val)

-- | Add a bound variable.
{-# inline bind #-}
bind :: Name -> Ty -> VTy -> Elab (Val -> IO a) -> Elab (IO a)
bind x a va act =
  let val     = LocalVar ?lvl va in
  let ?lvl    = ?lvl + 1
      ?env    = EDef ?env val
      ?locals = LBind ?locals x a in
  forceElab $ localDefineIS x va (act val)

-- | Insert a new binder (don't update the identifier scope since
--   the new binder doesn't exist in presyntax).
{-# inline insertBind #-}
insertBind :: Name -> Ty -> VTy -> Elab (Val -> IO a) -> Elab (IO a)
insertBind x a va act =
  let val     = LocalVar ?lvl va in
  let ?lvl    = ?lvl + 1
      ?env    = EDef ?env val
      ?locals = LBind ?locals x a in
  forceElab $ act val

{-# inline forcePTm #-}
forcePTm :: P.Tm -> (PTmArg => P.Tm -> a) -> a
forcePTm t act = go t where
  go (P.Parens _ t _) = go t
  go t                = let ?ptm = t in act t

bindToName :: P.Bind -> Name
bindToName = \case
  P.BOp op       -> NOp op
  P.BName x      -> NRawName x
  P.BUnused _    -> N_
  P.BNonExistent -> N_

elabError :: LvlArg => LocalsArg => SrcArg => PTmArg => Error -> IO a
elabError err = throwIO $ ErrorInCxt ?src ?locals ?lvl ?ptm err

unify :: LvlArg => P.Tm -> Val -> Val -> IO ()
unify t l r = do
  let ?unifyState = U.USPrecise conversionSpeculation
  U.unify (gjoin l) (gjoin r)

--------------------------------------------------------------------------------

data Check = Check Tm ~Val
data Infer = Infer Tm ~VTy ~Val

checkAnnotation :: Elab (Maybe P.Tm -> VTy -> IO Check)
checkAnnotation t a = case t of
  Nothing -> elabError MissingAnnotation
  Just t  -> check t a

-- Question: should I elaborate multibinds separately from check (as I do here),
-- or inline into check?

-- TODO: PROPER SOLUTION: elaborate multibinders to Let.
checkPiMultiBind :: Elab (List P.Bind -> Icit -> Check -> List P.MultiBind -> P.Tm -> IO Check)
checkPiMultiBind xs i (Check a va) binds b = case xs of
  Nil ->
    checkPi binds b
  Cons (bindToName -> x) xs -> do
    Check b vb <- bind x a va \_ -> checkPiMultiBind xs i (Check (S.Wk a) va) binds b
    pure $ Check (S.Pi (BindI x i a b)) (Pi $ ClI x i va \v -> def v \_ -> eval b)

checkPi :: Elab (List P.MultiBind -> P.Tm -> IO Check)
checkPi binds b = case binds of
  Nil -> do
    check b Set
  Cons (P.MultiBind xs i a) binds -> do
    a <- checkAnnotation a Set
    checkPiMultiBind xs i a binds b

-- | Precondition: the VTy arg is in whnf.
checkLamMultiBind :: Elab (List P.Bind -> Icit -> Check -> List P.MultiBind -> P.Tm -> VTy -> IO Check)
checkLamMultiBind xs i (Check a va) binds t b = case (xs, b) of

  -- go under lambda
  (Cons (bindToName -> x) xs, Pi b) | b^.icit == i -> bind x a va \v -> do
    Check t vt <- checkLamMultiBind xs i (Check (S.Wk a) va) binds t (b ∙ v)
    pure $ Check (S.Lam (BindI x i a t)) (Lam $ ClI x i va \v -> def v \_ -> eval t)

  -- insert implicit lambda
  (xs, Pi b) | b^.icit == Impl -> do
    let x      = b^.name
        vdomty = b^.ty
        domty  = readbNoUnfold vdomty
    insertBind x domty vdomty \v -> do
      Check t vt <- checkLamMultiBind xs i (Check (S.Wk a) va) binds t (whnf (b ∙ v))
      pure $ Check (S.Lam (BindI x Impl domty t)) (Lam $ ClI x Impl vdomty \v -> def v \_ -> eval t)

  (xs, Flex{}) -> elabError "unknown checking type"   -- TODO: block
  (Nil, b)     -> checkLam binds t b



checkLam :: Elab (List P.MultiBind -> P.Tm -> VTy -> IO Check)
checkLam binds t b = case binds of
  Nil -> do
    check t b
  Cons (P.MultiBind xs i a) binds -> do
    a <- checkAnnotation a Set
    checkLamMultiBind xs i a binds t b

check :: Elab (P.Tm -> VTy -> IO Check)
check t topA = forcePTm t \case
  P.Let _ S1 (bindToName -> x) a t u -> do
    Check a va <- checkAnnotation a Set
    Check t vt <- check t va
    Check u vu <- define x a va t vt \_ -> check u topA
    pure $ Check (S.Let t (Bind x a u)) vu

  P.Hole _ -> do
    m <- U.freshMeta (readbNoUnfold topA)
    pure $ Check m (eval m)

  topt -> case (topt, whnf topA) of

    (P.Pi  _ binds b, Set) -> checkPi binds b
    (P.Lam _ binds t, b)   -> checkLam binds t b


infer :: Elab (P.Tm -> IO Infer)
infer t = uf


-- check0 :: Elab (P.Tm -> GTy -> IO Tm0)
-- check0 = uf

-- infer0 :: Elab (P.Tm -> IO (Tm0, GTy))
-- infer0 = uf
