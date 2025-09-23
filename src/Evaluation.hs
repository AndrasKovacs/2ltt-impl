{-# options_ghc -Wno-orphans #-}

module Evaluation where

import Common
import qualified Core as C
import Value

def :: Val -> (Val -> EnvArg => a) -> EnvArg => a
def v k = let ?env = EDef ?env v in k v
{-# inline def #-}

def0 :: Lvl -> (Lvl -> EnvArg => a) -> EnvArg => a
def0 v k = let ?env = EDef0 ?env v in k v
{-# inline def0 #-}

defLazy :: Val -> (EnvArg => a) -> EnvArg => a
defLazy ~v k = let ?env = EDef ?env v in k
{-# inline defLazy #-}

class Eval a b | a -> b where
  eval :: LvlArg => EnvArg => a -> b

instance Eval Ix Val where
  eval x = go ?env x where
    go (EDef _ v)  0 = v
    go (EDef e _)  x = go e (x - 1)
    go (EDef0 e _) x = go e (x - 1)
    go _           _ = impossible

instance Eval C.TConInfo Val where eval x = x^.value
instance Eval C.DConInfo Val where eval x = x^.value
instance Eval C.DefInfo  Val where eval x = x^.value

instance Eval (C.Bind C.Tm) NClosure where
  {-# inline eval #-}
  eval (C.Bind x t) = NCl x $ Cl \v -> def v \_ -> eval t

instance Eval (C.BindI C.Tm) NIClosure where
  {-# inline eval #-}
  eval (C.BindI x i t) = NICl x i $ Cl \v -> def v \_ -> eval t

instance Eval (C.Bind C.Tm0) Closure0 where
  {-# inline eval #-}
  eval (C.Bind x t) = Cl0 x \v -> def0 v \_ -> eval t

instance Eval a b => Eval (List a) (List b) where
  eval = fmap eval

instance Eval C.Prim Val where
  eval = \case
    C.Lift    -> LamE A_ Set Lift
    C.Set     -> Set
    C.Prop    -> Prop
    C.Ty      -> Ty
    C.ValTy   -> ValTy
    C.CompTy  -> CompTy
    C.ElVal   -> LamE A_ ValTy ElVal
    C.ElComp  -> LamE A_ CompTy ElComp
    C.Exfalso -> uf

proj :: Val -> Proj -> SP -> Val
proj t p sp = case t of
  Record vs      -> index vs (projIndex p)
  Rigid h spn    -> Rigid h (SProj spn p sp)
  Flex h spn     -> Flex h (SProj spn p sp)
  Unfold h spn v -> Unfold h (SProj spn p sp) (proj v p sp)
  _              -> impossible

quote :: Val0 -> Val
quote = \case
  Splice t -> t
  t        -> Quote t

splice :: Val -> Val0
splice = \case
  Quote t -> t
  t       -> Splice t

instance Apply Val (Val, Icit, SP) Val where
  {-# inline (∘) #-}
  (∘) t arg@(!u, !_, !_) = case t of
    Lam _ t        -> t ∘ u
    Rigid h spn    -> Rigid h (spn ∘ arg)
    Flex h spn     -> Flex h (spn ∘ arg)
    Unfold h spn v -> Unfold h (spn ∘ arg) (v ∘ arg)
    _              -> impossible

instance Eval C.Tm0 Val0 where
  eval = \case
    C.LocalVar0 x -> go ?env x where
       go (EDef0 _ v) 0 = LocalVar0 v
       go (EDef e _)  x = go e (x - 1)
       go (EDef0 e _) x = go e (x - 1)
       go _           _ = impossible
    C.TopDef0 di -> TopDef0 di
    C.DCon0 di   -> DCon0 di
    C.Record0 ts -> Record0 (eval ts)
    C.Proj0 t p  -> Proj0 (eval t) p
    C.App0 t u   -> App0 (eval t) (eval u)
    C.Lam0 a t   -> Lam0 (eval a) (eval t)
    C.Decl0 a t  -> Decl0 (eval a) (eval t)
    C.Splice t   -> splice (eval t)

instance Eval C.Tm Val where
  eval = \case
    C.LocalVar x   -> eval x
    C.TCon ci      -> eval ci
    C.DCon ci      -> eval ci
    C.TopDef di    -> eval di
    C.Let _ _ t u  -> def (eval t) \v -> eval u ∘ v
    C.Pi a b       -> Pi (eval a) (eval b)
    C.Prim p       -> eval p
    C.App t u i sp -> eval t ∘ (eval u, i, sp)
    C.Lam a t      -> Lam (eval a) (eval t)
    C.Proj t p sp  -> proj (eval t) p sp
    C.Record ts    -> Record (eval ts)
    C.Quote t      -> quote (eval t)
    C.Fun0 a b     -> Fun0 (eval a) (eval b)
