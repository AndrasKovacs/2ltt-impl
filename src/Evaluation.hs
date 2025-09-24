{-# options_ghc -Wno-orphans #-}

module Evaluation where

import Common hiding (Prim(..))
import qualified Common as C
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
    C.Lift      -> ΛE A_ Set Lift
    C.Bot       -> Bot
    C.Set       -> Set
    C.Prop      -> Prop
    C.Ty        -> Ty
    C.ValTy     -> ValTy
    C.CompTy    -> CompTy
    C.ElVal     -> ΛE A_ ValTy ElVal
    C.ElComp    -> ΛE A_ CompTy ElComp
    C.Exfalso   -> ΛI A_ Set \a -> ΛE p_ Bot \p -> Exfalso a p
    C.ExfalsoP  -> ΛI A_ Prop \a -> ΛE p_ Bot \p -> ExfalsoP a p
    C.Eq        -> ΛI A_ Set \a -> ΛE x_ a \x -> ΛE y_ a \y -> Eq a x y
    C.Refl      -> ΛI A_ Set \a -> ΛI x_ a \x -> Refl a x
    C.Sym       -> ΛI A_ Set \a -> ΛI x_ a \x -> ΛI y_ a \y ->
                   ΛE p_ (Eq a x y) \p ->
                   Sym a x y p
    C.Trans     -> ΛI A_ Set \a -> ΛI x_ a \x -> ΛI y_ a \y -> ΛI z_ a \z ->
                   ΛE p_ (Eq a x y) \p -> ΛE q_ (Eq a y z) \q ->
                   Trans a x y z p q
    C.Ap        -> ΛI A_ Set \a -> ΛI B_ Set \b ->
                   ΛE f_ (a ==> b) \f -> ΛI x_ a \x -> ΛI y_ a \y ->
                   ΛE p_ (Eq a x y) \p ->
                   Ap a b f x y p
    C.Fun0      -> ΛE A_ ValTy \a -> ΛE B_ Ty \b -> Fun0 a b
    C.Coe       -> ΛI A_ Set \a -> ΛI B_ Set \b -> ΛE p_ (Eq Set a b) \p -> ΛE x_ a \x ->
                   coe a b p x

pi0P :: Val -> Val
pi0P v = proj v (Proj 0 N_ P)

pi1P :: Val -> Val
pi1P v = proj v (Proj 1 N_ P)

coeSP :: LvlArg => SP -> Val -> Val -> Val -> Val -> Val
coeSP P a b p t = pi0P p ∘ (t, Expl, P)
coeSP S a b p t = coe a b p t

-- Set coercion
coe :: LvlArg => Val -> Val -> Val -> Val -> Val
coe a b p t = case (a, b) of

  -- canonical match
  (topA@(Pi a sp b), topB@(Pi a' sp' b'))
    | b^.icit /= b'^.icit || sp /= sp' -> RCoe topA topB p t
    | True ->
      let i  = b^.icit
          p0 = pi0P p
          p1 = pi1P p
      in Λ (pick (b^.name) (b'^.name)) i a' \x' ->
           let x = coeSP sp a' a (Sym Set a a' p0) x'
           in coe (b ∘ x) (b' ∘ x') (p1 ∘ (x, Expl, sp)) (t ∘ (x, i, sp))

  (Set,  Set)  -> t
  (Prop, Prop) -> t

  -- unfolding
  (ua@(Unfold h sp a), b) -> UCoe ua b p t (coe a b p t)
  (a, ub@(Unfold h sp b)) -> UCoe a ub p t (coe a b p t)

  -- flex
  (a@(Flex h sp), b) -> FCoe (blocker h) a b p t
  (a, b@(Flex h sp)) -> FCoe (blocker h) a b p t

  -- rigid neutral, try coe-refl
  (a@Rigid{}, b) -> tryRefl a b p t
  (a, b@Rigid{}) -> tryRefl a b p t

  -- canonical mismatch
  (a, b) -> RCoe a b p t

tryRefl :: LvlArg => Val -> Val -> Val -> Val -> Val
tryRefl = uf

proj :: Val -> C.Proj -> Val
proj t p = case t of
  Record vs      -> index vs (p^.lvl)
  Rigid h spn    -> Rigid  h (SProject spn p)
  Flex h spn     -> Flex   h (SProject spn p)
  Unfold h spn v -> Unfold h (SProject spn p) (proj v p)
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
    C.TopDef0 di     -> TopDef0 di
    C.DCon0 di       -> DCon0 di
    C.Record0 ts     -> Record0 (eval ts)
    C.Project0 t p   -> Project0 (eval t) p
    C.App0 t u       -> App0 (eval t) (eval u)
    C.Lam0 a t       -> Lam0 (eval a) (eval t)
    C.Decl0 a t      -> Decl0 (eval a) (eval t)
    C.Splice t       -> splice (eval t)

instance Eval C.Tm Val where
  eval = \case
    C.LocalVar x   -> eval x
    C.TCon ci      -> eval ci
    C.DCon ci      -> eval ci
    C.TopDef di    -> eval di
    C.Let _ _ t u  -> def (eval t) \v -> eval u ∘ v
    C.Pi a sp b    -> Pi (eval a) sp (eval b)
    C.Prim p       -> eval p
    C.App t u i sp -> eval t ∘ (eval u, i, sp)
    C.Lam a t      -> Lam (eval a) (eval t)
    C.Project t p  -> proj (eval t) p
    C.Record ts    -> Record (eval ts)
    C.Quote t      -> quote (eval t)

-- Forcing
--------------------------------------------------------------------------------


-- Conversion for the purpose of coe-refl
--------------------------------------------------------------------------------

data ConvRes = Same | Diff | BlockOn MetaVar
  deriving Show

instance Exception ConvRes

class Conv a where
  conv :: LvlArg => a -> a -> IO ()

-- instance Conv Val where
--   conv t u =


--------------------------------------------------------------------------------
