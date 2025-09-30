{-# options_ghc -Wno-unused-imports #-}

module Elaboration where

import Common hiding (Set, Prop)
import Core (Tm, Ty, Tm0, LocalsArg, Locals(..))
import Value
import Evaluation
import Elaboration.State

import qualified Presyntax as P
import qualified Common as C
import qualified Core as C

--------------------------------------------------------------------------------

type Elab a = LvlArg => EnvArg => LocalsArg => SrcArg => a

{-# inline forceElab #-}
forceElab :: Elab a -> Elab a
forceElab act = seq ?lvl (seq ?env (seq ?locals (seq ?src act)))

{-# inline define #-}
define :: Name -> Ty -> GTy -> Tm -> GVal -> Elab (IO a) -> Elab (IO a)
define x a ga t gt act =
  let ?lvl    = ?lvl + 1
      ?env    = EDef ?env (g1 gt)
      ?locals = LDef ?locals x t a
  in forceElab $ localDefineIS x ga act

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

checkMaybe :: Elab (Maybe P.Tm -> GTy -> SP -> IO Tm)
checkMaybe t a sp = case t of
  Nothing -> uf
  Just t  -> check t a sp

inferTy :: Elab (P.Tm -> IO (Ty, SP))
inferTy t = forcePTm t \case
  P.Let _ S1 (bindToName -> x) a t u -> do
    (a, as) <- case a of Nothing -> uf
                         Just a  -> inferTy a
    uf

-- checkLams :: Elab (List P.MultiBind -> P.Tm -> VTy -> SP -> NIClosure -> IO Tm)
-- checkLams bindss t a as b = case bindss of
--   Nil -> impossible
--   Cons (P.MultiBind (Single (bindToName -> x)) i ma) bindss -> do
--     _

check :: Elab (P.Tm -> GTy -> SP -> IO Tm)
check t gtopA@(G topA ftopA) sp = forcePTm t \case
  P.Let _ S1 (bindToName -> x) ma t u -> do
    (a, as) <- case ma of Nothing -> uf
                          Just a  -> inferTy a
    let ga = geval a
    t <- check t ga as
    let gt = geval t
    u <- define x a ga t gt $ check u gtopA sp
    pure $ C.Let a as t (C.Bind x u)

  t -> case (t, whnf ftopA) of

    (P.Lam pos Nil t, Pi a as b) -> impossible

    -- matching icit
    (P.Lam pos (Cons (P.MultiBind (Single (bindToName -> x)) i ma) bindss) t, Pi a as b) | i == b^.icit ->
      _

    -- (t, Pi a as b) | b^.icit == Impl -> uf

infer :: Elab (P.Tm -> SP -> IO (Tm, GTy))
infer t s = uf


check0 :: Elab (P.Tm -> GTy -> IO Tm0)
check0 = uf

infer0 :: Elab (P.Tm -> IO (Tm0, GTy))
infer0 = uf
