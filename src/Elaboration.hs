{-# options_ghc -Wno-unused-imports #-}

module Elaboration where

import Common hiding (Set)
import Core (Tm, Ty, Tm0, LocalsArg, Locals(..))
import Value
import Evaluation
import Elaboration.State

import qualified Presyntax as P
import qualified Common as C
import qualified Core as C
import Unification

--------------------------------------------------------------------------------

type Elab a = LvlArg => EnvArg => LocalsArg => SrcArg => a

{-# inline forceElab #-}
forceElab :: Elab a -> Elab a
forceElab act = seq ?lvl (seq ?env (seq ?locals (seq ?src act)))

{-# inline define #-}
define :: Name -> Ty -> VTy -> Tm -> Val -> Elab (IO a) -> Elab (IO a)
define x a va t vt act =
  let ?lvl    = ?lvl + 1
      ?env    = EDef ?env vt
      ?locals = LDef ?locals x t a
  in forceElab $ localDefineIS x va act

{-# inline forcePTm #-}
forcePTm :: P.Tm -> (SpanArg => P.Tm -> a) -> a
forcePTm t act = go t where
  go (P.Parens _ t _) = go t
  go t                = let ?span = Box (spanOf t) in act t

bindToName :: P.Bind -> Name
bindToName = \case
  P.BOp op       -> NOp op
  P.BName x      -> NRawName x
  P.BUnused _    -> N_
  P.BNonExistent -> N_

--------------------------------------------------------------------------------

checkMaybe :: Elab (Maybe P.Tm -> VTy -> IO Tm)
checkMaybe t a = case t of
  Nothing -> uf
  Just t  -> check t a

inferTy :: Elab (P.Tm -> IO Ty)
inferTy t = forcePTm t \case
  P.Let _ S1 (bindToName -> x) a t u -> do
    a <- checkMaybe a Set
    uf

-- checkLams :: Elab (List P.MultiBind -> P.Tm -> VTy -> SP -> NIClosure -> IO Tm)
-- checkLams bindss t a as b = case bindss of
--   Nil -> impossible
--   Cons (P.MultiBind (Single (bindToName -> x)) i ma) bindss -> do
--     _

check :: Elab (P.Tm -> VTy -> IO Tm)
check t topA = forcePTm t \case
  P.Let _ S1 (bindToName -> x) ma t u -> do
    a <- checkMaybe ma Set
    let va = eval a
    t <- check t va
    let vt = eval t
    u <- define x a va t vt $ check u topA
    pure $ C.Let a t (C.Bind x u)

  P.Hole _ ->
    freshMeta topA

  -- t -> case (t, whnf ftopA) of

  --   (P.Lam pos Nil t, Pi a b) -> impossible

  --   -- matching icit
  --   (P.Lam pos (Cons (P.MultiBind (Single (bindToName -> x)) i ma) bindss) t, Pi a b) | i == b^.icit ->
  --     uf

  --   -- (t, Pi a as b) | b^.icit == Impl -> uf

infer :: Elab (P.Tm -> IO (Tm, GTy))
infer t = uf


check0 :: Elab (P.Tm -> GTy -> IO Tm0)
check0 = uf

infer0 :: Elab (P.Tm -> IO (Tm0, GTy))
infer0 = uf
