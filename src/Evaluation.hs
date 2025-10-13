
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

{-# inline freshLvl #-}
freshLvl :: (LvlArg => Lvl -> a) -> LvlArg => a
freshLvl k = let v = ?lvl in let ?lvl = v + 1 in k v

{-# inline fresh #-}
fresh :: (LvlArg => Val -> a) -> LvlArg => a
fresh k = freshLvl \l -> k $! LocalVar l

{-# inline defLazy #-}
defLazy :: Val -> (EnvArg => a) -> EnvArg => a
defLazy ~v k = let ?env = EDef ?env v in k

class Eval a b | a -> b where
  eval :: EnvArg => a -> b

evalIn :: Eval a b => Env -> a -> b
evalIn e a = let ?env = e in eval a

lookupIx :: EnvArg => Ix -> Val
lookupIx x = go ?env x where
  go (EDef _ v)  0 = v
  go (ELet _ v)  0 = v
  go (EDef e _)  x = go e (x - 1)
  go (EDef0 e _) x = go e (x - 1)
  go (ELet e _)  x = go e (x - 1)
  go _           _ = impossible

lookupIx0 :: EnvArg => Ix -> Lvl
lookupIx0 x = go ?env x where
  go (EDef0 _ l) 0 = l
  go (EDef e _)  x = go e (x - 1)
  go (EDef0 e _) x = go e (x - 1)
  go (ELet e _)  x = go e (x - 1)
  go _           _ = impossible

{-# inline geval #-}
geval :: Eval a Val => EnvArg => a -> G
geval a = gjoin (eval a)

instance Eval (C.Bind C.Tm0) Closure0 where
  {-# inline eval #-}
  eval (C.Bind x t) = Cl0 x \v -> def0 v \_ -> eval t

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

meta :: MetaVar -> Env -> Val
meta m e =
  let h = MetaHead m e in
  unblock h (Flex h SId) \ ~v -> \case
    True  -> v
    False -> Unfold (UHMeta h) SId v

instance Eval C.TmEnv Env where
  eval = \case
    C.TENil      -> ENil
    C.TELet e t  -> ELet (eval e) (eval t)
    C.TEDef e t  -> EDef (eval e) (eval t)
    C.TEDef0 e x -> EDef0 (eval e) (lookupIx0 x)

instance Eval C.MetaSub Env where
  eval = \case
    C.MSId    -> ?env
    C.MSSub s -> eval s

instance Eval C.Tm0 Val0 where
  eval = \case
    C.LocalVar0 x  -> LocalVar0 (lookupIx0 x)
    C.TopDef0 di   -> TopDef0 di
    C.DCon0 di     -> DCon0 di
    C.Project0 t p -> Project0 (eval t) p
    C.App0 t u     -> App0 (eval t) (eval u)
    C.Lam0 a t     -> Lam0 (eval a) (eval t)
    C.Decl0 a t    -> Decl0 (eval a) (eval t)
    C.Splice t     -> splice (eval t)

instance Eval C.Tm Val where
  eval = \case
    C.LocalVar x  -> lookupIx x
    C.TCon i      -> i^.value
    C.DCon i      -> i^.value
    C.RecTy i     -> i^.value
    C.Rec i       -> i^.value
    C.TopDef i    -> i^.value
    C.Let _ t u   -> def (eval t) \v -> eval u ∙ v
    C.Pi a b      -> Pi (eval a) (eval b)
    C.Prim p      -> eval p
    C.App t u i   -> eval t ∙∘ (eval u, i)
    C.Lam a t     -> Lam (eval a) (eval t)
    C.Project t p -> proj (eval t) p
    C.Quote t     -> quote (eval t)
    C.Meta m sub  -> meta m (eval sub)

-- Forcing
--------------------------------------------------------------------------------

{-# inline unblock #-}
unblock :: MetaHead -> a -> (Val -> Bool -> a) -> a
unblock (MetaHead m env) deflt k = case lookupMeta m of
  MEUnsolved x -> deflt
  MESolved x   -> let ~v = (let ?env = env in eval (x^.solution)) in
                  k v (x^.isInline)

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

{-# inline readBack #-}
readBack :: ReadBack a b => Lvl -> Unfold -> a -> b
readBack l uf = let ?lvl = l; ?unfold = uf in readb

readBackNoUnfold :: ReadBack a b => Lvl -> a -> b
readBackNoUnfold l = readBack l UnfoldNone

instance ReadBack Lvl Ix where
  readb = lvlToIx ?lvl

instance ReadBack RigidHead C.Tm where
  readb = \case
    RHLocalVar x -> C.LocalVar (readb x)
    RHPrim p     -> C.Prim p
    RHDCon i     -> C.DCon i
    RHTCon i     -> C.TCon i
    RHRecTy i    -> C.RecTy i
    RHRec i      -> C.Rec i

instance ReadBack UnfoldHead C.Tm where
  readb = \case
    UHMeta m     -> readb m
    UHTopDef i   -> C.TopDef i
    UHLocalDef l -> C.LocalVar (readb l)

instance ReadBack Env C.MetaSub where
  readb e = C.MSSub (go e) where
    go :: LvlArg => Env -> C.TmEnv
    go = \case
      ENil      -> C.TENil
      ELet e v  -> C.TELet (go e) (readb v)
      EDef e v  -> C.TEDef (go e) (readb v)
      EDef0 e l -> C.TEDef0 (go e) (readb l)

instance ReadBack MetaHead C.Tm where
  readb (MetaHead m env) = C.Meta m (readb env)

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
