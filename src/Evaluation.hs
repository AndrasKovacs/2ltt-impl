

module Evaluation where

import Common hiding (Prim(..))
import qualified Common as C
import qualified Core as C
import Value
import Elaboration.State

{-# inline def #-}
def :: Val -> (Val -> EnvArg => a) -> EnvArg => a
def v k = let ?env = EDef ?env v in k v

{-# inline def0 #-}
def0 :: Lvl -> (Lvl -> EnvArg => a) -> EnvArg => a
def0 v k = let ?env = EDef0 ?env v in k v

{-# inline fresh #-}
fresh :: (LvlArg => Val -> a) -> LvlArg => a
fresh k = let v = LocalVar ?lvl in let ?lvl = ?lvl + 1 in k v

{-# inline freshLvl #-}
freshLvl :: (LvlArg => Lvl -> a) -> LvlArg => a
freshLvl k = let v = ?lvl in let ?lvl = v + 1 in k v

{-# inline defLazy #-}
defLazy :: Val -> (EnvArg => a) -> EnvArg => a
defLazy ~v k = let ?env = EDef ?env v in k

class Eval a b | a -> b where
  eval :: EnvArg => a -> b

instance Eval Ix Val where
  eval x = go ?env x where
    go (EDef _ v)  0 = v
    go (EDef e _)  x = go e (x - 1)
    go (EDef0 e _) x = go e (x - 1)
    go _           _ = impossible

{-# inline geval #-}
geval :: Eval a Val => EnvArg => a -> G
geval a = gjoin (eval a)

instance Eval C.TConInfo Val where eval x = x^.value
instance Eval C.DConInfo Val where eval x = x^.value
instance Eval C.DefInfo  Val where eval x = x^.value
instance Eval C.RecInfo  Val where eval x = x^.value

instance Eval (C.Bind C.Tm0) Closure0 where
  {-# inline eval #-}
  eval (C.Bind x t) = Cl0 x \v -> def0 v \_ -> eval t

instance Eval a b => Eval (List a) (List b) where
  eval = fmap eval

instance Eval (C.BindI C.Tm) ClosureI where
  {-# inline eval #-}
  eval (C.BindI x i t) = ClI x i \v -> def v \_ -> eval t

instance Eval (C.Bind C.Tm) Closure where
  {-# inline eval #-}
  eval (C.Bind x t) = Cl x \v -> def v \_ -> eval t

instance Eval C.Prim Val where
  eval = \case
    C.Lift      -> ΛE A_ Set Lift
    C.Set       -> Set
    C.Ty        -> Ty
    C.ValTy     -> ValTy
    C.CompTy    -> CompTy
    C.ElVal     -> ΛE A_ ValTy ElVal
    C.ElComp    -> ΛE A_ CompTy ElComp
    C.Fun0      -> ΛE A_ ValTy \a -> ΛE B_ Ty \b -> Fun0 a b
    C.Eq        -> ΛI A_ Set \a -> ΛE x_ a \x -> ΛE y_ a \y -> Eq a x y
    C.Refl      -> ΛI A_ Set \a -> ΛI x_ a \x -> Refl a x
    C.J         -> ΛI A_ Set \a ->
                   ΛI x_ a \x ->
                   ΛE P_ (PiE y_ a \y -> Eq a x y ∙> Set) \bigP ->
                   ΛI y_ a \y ->
                   ΛI p_ (Eq a x y) \p ->
                   ΛE r_ (bigP ∙ x ∙ p) \r ->
                   p ∙ y ∙ p
    C.K         -> ΛI A_ Set \a ->
                   ΛI x_ a \x ->
                   ΛE P_ (Eq a x x ∙> Set) \bigP ->
                   ΛE p_ (Eq a x x) \p ->
                   bigP ∙ p

spine :: Val -> Spine -> Val
spine v = \case
  SId           -> v
  SApp t u i    -> spine v t ∙∘ (u, i)
  SProject t p  -> proj (spine v t) p

projFromSpine :: Spine -> Ix -> Val
projFromSpine sp x = case (sp, x) of
  (SApp _ u _ , 0) -> u
  (SApp sp _ _, x) -> projFromSpine sp (x - 1)
  _                -> impossible

proj :: Val -> C.Proj -> Val
proj t p = case t of
  Rec _ spn      -> projFromSpine spn (p^.index)
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

instance Eval C.Tm0 Val0 where
  eval = \case
    C.LocalVar0 x -> go ?env x where
       go (EDef0 _ v) 0 = LocalVar0 v
       go (EDef e _)  x = go e (x - 1)
       go (EDef0 e _) x = go e (x - 1)
       go _           _ = impossible
    C.TopDef0 di     -> TopDef0 di
    C.DCon0 di       -> DCon0 di
    C.Project0 t p   -> Project0 (eval t) p
    C.App0 t u       -> App0 (eval t) (eval u)
    C.Lam0 a t       -> Lam0 (eval a) (eval t)
    C.Decl0 a t      -> Decl0 (eval a) (eval t)
    C.Splice t       -> splice (eval t)

instance Eval MetaVar Val where
  eval m = unblock m (Flex m SId) \ ~v -> \case
    True  -> v
    False -> Unfold (UHMeta m) SId v

instance Eval C.Tm Val where
  eval = \case
    C.LocalVar x   -> eval x
    C.TCon ci      -> eval ci
    C.DCon ci      -> eval ci
    C.RecTy ri     -> eval ri
    C.RecCon ri    -> eval ri
    C.TopDef di    -> eval di
    C.Let _ t u    -> def (eval t) \v -> eval u ∙ v
    C.Pi a b       -> Pi (eval a) (eval b)
    C.Prim p       -> eval p
    C.App t u i    -> eval t ∙∘ (eval u, i)
    C.Lam a t      -> Lam (eval a) (eval t)
    C.Project t p  -> proj (eval t) p
    C.Quote t      -> quote (eval t)
    C.Meta m       -> eval m

eval0 :: Eval a b => a -> b
eval0 a = let ?env = ENil in eval a

-- Forcing
--------------------------------------------------------------------------------

{-# inline unblock #-}
unblock :: MetaVar -> a -> (Val -> Bool -> a) -> a
unblock m deflt k = case lookupMeta m of
  MEUnsolved x -> deflt
  MESolved x   -> k (x^.solutionVal) (x^.isInline)

-- discard all unfoldings
whnf :: Val -> Val
whnf = \case
  top@(Flex m sp) -> unblock m top \v _ -> whnf $ spine v sp
  Unfold _ _ v    -> whnf v
  v               -> v

-- update head, unfold metas ("weak head meta normal")
whmnf :: Val -> Val
whmnf = \case
  top@(Flex m sp) -> unblock m top \v _ -> whmnf $ spine v sp
  v               -> v

-- update head, preserve all unfoldings
force ::  Val -> Val
force = \case
  top@(Flex m sp) -> unblock m top \v -> \case
    True -> force $ spine v sp      -- inline meta
    _    -> Unfold (UHMeta m) sp v  -- noinline meta
  v -> v


-- Readback
--------------------------------------------------------------------------------

class ReadBack a b | a -> b where
  readb :: LvlArg => UnfoldArg => a -> b

readBack0 :: ReadBack a b => Unfold -> a -> b
readBack0 uf a = let ?unfold = uf; ?lvl = 0 in readb a

instance ReadBack Lvl Ix where
  readb = lvlToIx ?lvl

instance ReadBack RigidHead C.Tm where
  readb = \case
    RHLocalVar x -> C.LocalVar (readb x)
    RHPrim p     -> C.Prim p
    RHDCon i     -> C.DCon i
    RHTCon i     -> C.TCon i
    RHRecTy i    -> C.RecTy i
    RHRec i      -> C.RecCon i

instance ReadBack UnfoldHead C.Tm where
  readb = \case
    UHMeta m     -> C.Meta m
    UHTopDef i _ -> C.TopDef i

instance ReadBack MetaVar C.Tm where
  readb = C.Meta

instance ReadBack Spine (C.Tm -> C.Tm) where
  readb t h = case t of
    SId          -> h
    SApp t u i   -> C.App (readb t h) (readb u) i
    SProject t p -> C.Project (readb t h) p

instance ReadBack ClosureI (C.BindI C.Tm) where
  readb (ClI x i t) = fresh \v -> C.BindI x i (readb (t v))

instance ReadBack Closure0 (C.Bind C.Tm0) where
  readb (Cl0 x t) = freshLvl \l -> C.Bind x (readb (t l))

instance ReadBack Val0 C.Tm0 where
  readb = \case
    LocalVar0 x  -> C.LocalVar0 (readb x)
    TopDef0 i    -> C.TopDef0 i
    DCon0 i      -> C.DCon0 i
    App0 t u     -> C.App0 (readb t) (readb u)
    Lam0 a t     -> C.Lam0 (readb a) (readb t)
    Decl0 a t    -> C.Decl0 (readb a) (readb t)
    Project0 t p -> C.Project0 (readb t) p
    Splice t     -> C.Splice (readb t)

instance ReadBack Val C.Tm where
  readb t =
    let t' = case ?unfold of
          UnfoldAll   -> whnf t
          UnfoldNone  -> force t
          UnfoldMetas -> whmnf t
    in case t' of
      Rigid h sp    -> readb sp (readb h)
      Flex h sp     -> readb sp (readb h)
      Unfold h sp _ -> readb sp (readb h)
      Pi a b        -> C.Pi (readb a) (readb b)
      Lam a t       -> C.Lam (readb a) (readb t)
      Quote t       -> C.Quote (readb t)
