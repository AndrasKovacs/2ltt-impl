{-# options_ghc -Wno-orphans #-}

module Evaluation where

import Common hiding (Prim(..))
import qualified Common as C
import qualified Core as C
import Value
import Elaboration.State

def :: Val -> (Val -> EnvArg => a) -> EnvArg => a
def v k = let ?env = EDef ?env v in k v
{-# inline def #-}

def0 :: Lvl -> (Lvl -> EnvArg => a) -> EnvArg => a
def0 v k = let ?env = EDef0 ?env v in k v
{-# inline def0 #-}

fresh :: (LvlArg => Val -> a) -> LvlArg => a
fresh k =
  let v = LocalVar ?lvl in
  let ?lvl = ?lvl + 1 in
  k v

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
    C.Lift      -> ΛES A_ Set Lift
    C.Bot       -> Bot
    C.Set       -> Set
    C.Prop      -> Prop
    C.Ty        -> Ty
    C.ValTy     -> ValTy
    C.CompTy    -> CompTy
    C.ElVal     -> ΛES A_ ValTy ElVal
    C.ElComp    -> ΛES A_ CompTy ElComp
    C.Exfalso   -> ΛIS A_ Set \a -> ΛES p_ Bot \p -> Exfalso a p
    C.ExfalsoP  -> ΛIS A_ Prop \a -> ΛES p_ Bot \p -> ExfalsoP a p
    C.Eq        -> ΛIS A_ Set \a -> ΛES x_ a \x -> ΛES y_ a \y -> Eq a x y
    C.Refl      -> ΛIS A_ Set \a -> ΛIS x_ a \x -> Refl a x
    C.Sym       -> ΛIS A_ Set \a -> ΛIS x_ a \x -> ΛIS y_ a \y ->
                   ΛEP p_ (Eq a x y) \p ->
                   Sym a x y p
    C.Trans     -> ΛIS A_ Set \a -> ΛIS x_ a \x -> ΛIS y_ a \y -> ΛIS z_ a \z ->
                   ΛEP p_ (Eq a x y) \p -> ΛEP q_ (Eq a y z) \q ->
                   Trans a x y z p q
    C.Ap        -> ΛIS A_ Set \a -> ΛIS B_ Set \b ->
                   ΛES f_ (a ∙∙> b) \f -> ΛIS x_ a \x -> ΛIS y_ a \y ->
                   ΛEP p_ (Eq a x y) \p ->
                   Ap a b f x y p
    C.Fun0      -> ΛES A_ ValTy \a -> ΛES B_ Ty \b -> Fun0 a b
    C.Coe       -> ΛIS A_ Set \a -> ΛIS B_ Set \b -> ΛEP p_ (Eq Set a b) \p -> ΛES x_ a \x ->
                   coe a b p x
    C.PropExt   -> ΛIS A_ Prop \a -> ΛIS B_ Prop \b -> ΛEP f_ (a ∙∘> b) \f -> ΛEP g_ (b ∙∘> a) \g ->
                   PropExt a b f g
    C.FunExt    -> ΛIS A_ Set \a -> ΛIS B_ (a ∙∙> Set) \b ->
                   let funtype = PiES a_ a (b ∙∙) in
                   ΛIS f_ funtype \f -> ΛIS g_ funtype \g ->
                   ΛEP p_ (PiES a_ a \x -> Eq (b ∙∙ x) (f ∙∙ x) (g ∙∙ x)) \p ->
                   FunExt a b f g p
    C.FunExtP   -> ΛIS A_ Prop \a -> ΛIS B_ (a ∙∘> Set) \b ->
                   let funtype = PiEP a_ a (b ∙∘) in
                   ΛIS f_ funtype \f -> ΛIS g_ funtype \g ->
                   ΛEP p_ (PiEP a_ a \x -> Eq (b ∙∘ x) (f ∙∘ x) (g ∙∘ x)) \p ->
                   FunExtP a b f g p

spine :: LvlArg => Val -> Spine -> Val
spine v = \case
  SId           -> v
  SApp t u i sp -> spine v t ∘ (u, i, sp)
  SProject t p  -> proj (spine v t) p

proj0 :: Val -> Val
proj0 v = proj v (Proj 0 N_)

proj1 :: Val -> Val
proj1 v = proj v (Proj 1 N_)

coeSP :: LvlArg => SP -> Val -> Val -> Val -> Val -> Val
coeSP P a b p t = proj0 p ∙∘ t
coeSP S a b p t = coe a b p t

-- Set coercion
coe :: LvlArg => Val -> Val -> Val -> Val -> Val
coe a b p t = case (a, b) of

  -- canonical match
  (topA@(Pi a sp b), topB@(Pi a' sp' b'))
    | b^.icit /= b'^.icit || sp /= sp' -> RCoe topA topB p t
    | True ->
      let i  = b^.icit
          p0 = proj0 p
          p1 = proj1 p
      in Λ (pick (b^.name) (b'^.name)) i a' sp \x' ->
           let x = coeSP sp a' a (Sym Set a a' p0) x'
           in coe (b ∘ x) (b' ∘ x') (p1 ∘ (x, Expl, sp)) (t ∘ (x, i, sp))

  (topA@(

  (Set,  Set)  -> t
  (Prop, Prop) -> t

  -- unfolding
  (ua@(Unfold h sp a), b) -> UCoe ua b p t (coe a b p t)
  (a, ub@(Unfold h sp b)) -> UCoe a ub p t (coe a b p t)

  -- flex
  (a@(Flex h sp), b) -> FCoe (blocker h) a b p t
  (a, b@(Flex h sp)) -> FCoe (blocker h) a b p t

  -- rigid neutral, try coe-refl
  (a@Rigid{}, b) -> coeRefl a b p t
  (a, b@Rigid{}) -> coeRefl a b p t

  -- canonical mismatch
  (a, b) -> RCoe a b p t

coeRefl :: LvlArg => Val -> Val -> Val -> Val -> Val
coeRefl a b p t = case runIO (catch (Same <$ conv a b) pure) of
  Same      -> t
  Diff      -> RCoe a b p t
  BlockOn m -> Flex (FHCoe m a b p t) SId

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
    Lam _ _ t      -> t ∘ u
    Rigid h spn    -> Rigid h (spn ∘ arg)
    Flex h spn     -> Flex h (spn ∘ arg)
    Unfold h spn v -> Unfold h (spn ∘ arg) (v ∘ arg)
    _              -> impossible

infixl 8 ∙∙
(∙∙) :: LvlArg => Val -> Val -> Val
(∙∙) t u = t ∘ (u, Expl, S)
{-# inline (∙∙) #-}

infixl 8 ∙∘
(∙∘) :: LvlArg => Val -> Val -> Val
(∙∘) t u = t ∘ (u, Expl, P)
{-# inline (∙∘) #-}

infixl 8 ∘∙
(∘∙) :: LvlArg => Val -> Val -> Val
(∘∙) t u = t ∘ (u, Impl, S)
{-# inline (∘∙) #-}

infixl 8 ∘∘
(∘∘) :: LvlArg => Val -> Val -> Val
(∘∘) t u = t ∘ (u, Impl, P)
{-# inline (∘∘) #-}

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
    C.Lam a s t    -> Lam (eval a) s (eval t)
    C.Project t p  -> proj (eval t) p
    C.Record ts    -> Record (eval ts)
    C.Quote t      -> quote (eval t)


-- Forcing
--------------------------------------------------------------------------------

{-# inline unblock #-}
unblock :: MetaVar -> a -> (Val -> Bool -> IO a) -> IO a
unblock m deflt k = readMeta m >>= \case
  MEUnsolved x -> pure deflt
  MESolved x   -> k (x^.solutionVal) (x^.isInline)

-- compute until rigid head, discard unfoldings
whnf :: LvlArg => Val -> IO Val
whnf = \case
  top@(Flex h sp) -> case h of
    FHMeta m        -> unblock m top \v _ -> whnf $ spine v sp
    FHCoe m a b p t -> unblock m top \_ _ -> whnf $ spine (coe a b p t) sp
  Unfold _ _ v -> whnf v
  v            -> pure v

-- update head while preserving unfoldings
force :: LvlArg => Val -> IO Val
force = \case
  top@(Flex h sp) -> case h of
    FHMeta m -> unblock m top \v -> \case
      True -> force $ spine v sp             -- inline meta
      _    -> pure $ Unfold (UHMeta m) sp v  -- noinline meta
    FHCoe m a b p t -> unblock m top \_ _ ->
      force $ coe a b p t
  v -> pure v


-- Conversion for the purpose of coe-refl
--------------------------------------------------------------------------------

data ConvRes = Same | Diff | BlockOn MetaVar
  deriving Show
instance Exception ConvRes

class Conv a where conv :: LvlArg => a -> a -> IO ()

instance {-# overlappable #-} Eq a => Conv a where
  {-# inline conv #-}
  conv x y = unless (x == y) $ throwIO Diff

{-# inline convSP #-}
convSP :: Conv a => LvlArg => SP -> a -> a -> IO ()
convSP sp x y = case sp of S -> conv x y
                           P -> pure ()

instance Conv RigidHead where
  conv h h' = case (h, h') of
    (RHLocalVar x  , RHLocalVar x'    ) -> conv x x'
    (RHCoe a b p t , RHCoe a' b' p' t') -> do conv a a'; conv t t'; conv b b'
    (RHPrim p      , RHPrim p'        ) -> conv p p'
    _                                   -> throwIO Diff

instance Conv Proj where
  conv p p' = conv (p^.lvl) (p'^.lvl)

instance Conv Spine where
  conv t u = case (t, u) of
    (SId         , SId             ) -> pure ()
    (SApp t u i s, SApp t' u' i' s') -> do conv t t'; convSP s u u'
    (SProject t p, SProject t' p'  ) -> do conv t t'; conv p p'
    _                                -> throwIO Diff

instance Conv NIClosure where
  conv t u = do
    conv (t^.icit) (u^.icit)
    fresh \v -> conv (t ∘ v) (u ∘ v)

instance Conv a => Conv (List a) where
  conv ts ts' = case (ts, ts') of
    (Nil      , Nil        ) -> pure ()
    (Cons t ts, Cons t' ts') -> do conv t t'; conv ts ts'
    _                        -> throwIO Diff

instance Conv Val where
  conv t t' = do
    t  <- whnf t
    t' <- whnf t'
    case (t, t') of

      -- canonical & rigid match
      (Pi a as b , Pi a' as' b') -> do conv as as'; conv a a'; conv b b'
      (Rigid h sp, Rigid h' sp') -> do conv h h'; conv sp sp'
      (Lam _ _ t , Lam _ _ t'  ) -> do conv t t'
      (Record ts , Record ts'  ) -> do conv ts ts'

      -- syntax-directed eta
      (t, Lam _ s' t')         -> fresh \v -> conv (t ∘ (v, t'^.icit, s')) (t' ∘ v)
      (Lam _ s t, t')          -> fresh \v -> conv (t ∘ v) (t' ∘ (v, t^.icit, s))
      (Record ts@(Cons{}), t') -> for ts  \i t  -> conv t (proj t' (Proj i N_))
      (t, Record ts'@(Cons{})) -> for ts' \i t' -> conv (proj t (Proj i N_)) t'

      -- flex
      (Flex h _, _) -> throwIO $! BlockOn (blocker h)
      (_, Flex h _) -> throwIO $! BlockOn (blocker h)

      -- rigid mismatch
      _ -> throwIO Diff


--------------------------------------------------------------------------------
