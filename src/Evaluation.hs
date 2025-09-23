module Evaluation where

import Common
import qualified Core as C
import Value

def :: Val -> (EnvArg => a) -> EnvArg => a
def v k = let ?env = EDef ?env v in k
{-# inline def #-}

class Eval a b | a -> b where
  eval :: LvlArg => EnvArg => a -> b

instance Eval Ix Val where
  eval x = go ?env x where
    go (EDef _ v) 0 = v
    go (EDef e _) x = go e (x - 1)
    go _          _ = impossible

instance Eval C.TConInfo Val where
  eval x = x^.value

instance Eval C.DConInfo Val where
  eval x = x^.value

instance Eval C.DefInfo Val where
  eval x = x^.value

instance Eval (C.Bind C.Tm) NClosure where
  eval (C.Bind x t) = NCl x $ Cl \v -> def v $ eval t

instance Eval (C.BindI C.Tm) NIClosure where
  eval (C.BindI x i t) = NICl x i $ Cl \v -> def v $ eval t

instance Eval C.Tm Val where
  eval = \case
    C.LocalVar x   -> eval x
    C.TCon ci      -> eval ci
    C.DCon ci      -> eval ci
    C.TopDef di    -> eval di
    C.Decl a t     -> Decl (eval a) (eval t)
    C.Let a sp t u -> Let (eval a) sp (eval t) (eval u)
    C.Pi a b       -> Pi (eval a) (eval b)
    C.App t u i
    -- C.
    -- C.TCon c sp -> TCon c (eval sp)
-- eval :: LvlArg => EnvArg => C.Tm -> Val
-- eval = _
