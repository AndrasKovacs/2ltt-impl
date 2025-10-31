
module Evaluation where

import Common hiding (Prim(..))
import qualified Common      as S
import qualified Core.Syntax as S
import Core.Value
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

instance Eval (S.Bind S.Tm0) Closure0 where
  {-# inline eval #-}
  eval (S.Bind x t) = Cl0 x \v -> def0 v \_ -> eval t

instance Eval (S.BindI S.Tm) ClosureI where
  {-# inline eval #-}
  eval (S.BindI x i t) = ClI x i \v -> def v \_ -> eval t

instance Eval (S.Bind S.Tm) Closure where
  {-# inline eval #-}
  eval (S.Bind x t) = Cl x \v -> def v \_ -> eval t

instance Eval S.Prim Val where
  eval = \case
    S.Lift      -> ΛE A_ Set Lift
    S.Set       -> Set
    S.Ty        -> Ty
    S.ValTy     -> ValTy
    S.CompTy    -> CompTy
    S.ElVal     -> ΛE A_ ValTy ElVal
    S.ElComp    -> ΛE A_ CompTy ElComp
    S.Fun0      -> ΛE A_ ValTy \a -> ΛE B_ Ty \b -> Fun0 a b
    S.Eq        -> ΛI A_ Set \a -> ΛE x_ a \x -> ΛE y_ a \y -> Eq a x y
    S.Refl      -> ΛI A_ Set \a -> ΛI x_ a \x -> Refl a x
    S.J         -> ΛI A_ Set \a ->
                   ΛI x_ a \x ->
                   ΛE P_ (PiE y_ a \y -> Eq a x y ∙> Set) \bigP ->
                   ΛI y_ a \y ->
                   ΛI p_ (Eq a x y) \p ->
                   ΛE r_ (bigP ∙ x ∙ p) \r ->
                   p ∙ y ∙ p
    S.K         -> ΛI A_ Set \a ->
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

proj :: Val -> S.Proj -> Val
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

meta0 :: MetaVar -> Env -> Val0
meta0 m e =
  let h = MetaHead m e in
  unblock0 h (Meta0 h) \ ~v -> \case
    True  -> v
    False -> SolvedMeta0 h v

instance Eval S.TmEnv Env where
  eval = \case
    S.TENil      -> ENil
    S.TELet e t  -> ELet (eval e) (eval t)
    S.TEDef e t  -> EDef (eval e) (eval t)
    S.TEDef0 e x -> EDef0 (eval e) (lookupIx0 x)

instance Eval S.MetaSub Env where
  eval = \case
    S.MSId    -> ?env
    S.MSSub s -> eval s

instance Eval S.Tm0 Val0 where
  eval = \case
    S.LocalVar0 x  -> LocalVar0 (lookupIx0 x)
    S.Meta0 m sub  -> meta0 m (eval sub)
    S.TopDef0 di   -> TopDef0 di
    S.DCon0 di     -> DCon0 di
    S.Project0 t p -> Project0 (eval t) p
    S.App0 t u     -> App0 (eval t) (eval u)
    S.Lam0 a t     -> Lam0 (eval a) (eval t)
    S.Decl0 a t    -> Decl0 (eval a) (eval t)
    S.Splice t     -> splice (eval t)

instance Eval S.Tm Val where
  eval = \case
    S.LocalVar x  -> lookupIx x
    S.TCon i      -> i^.value
    S.DCon i      -> i^.value
    S.RecTy i     -> i^.value
    S.Rec i       -> i^.value
    S.TopDef i    -> i^.value
    S.Let _ t u   -> def (eval t) \v -> eval u ∙ v
    S.Pi a b      -> Pi (eval a) (eval b)
    S.Prim p      -> eval p
    S.App t u i   -> eval t ∙∘ (eval u, i)
    S.Lam a t     -> Lam (eval a) (eval t)
    S.Project t p -> proj (eval t) p
    S.Quote t     -> quote (eval t)
    S.Meta m sub  -> meta m (eval sub)

-- Forcing
--------------------------------------------------------------------------------

{-# inline unblock #-}
unblock :: MetaHead -> a -> (Val -> Bool -> a) -> a
unblock (MetaHead m env) deflt k = case lookupMeta m of
  MEUnsolved x -> deflt
  MESolved x   -> let ~v = (let ?env = env in eval (x^.solution)) in
                  k v (x^.isInline)
  _            -> impossible

{-# inline unblock0 #-}
unblock0 :: MetaHead -> a -> (Val0 -> Bool -> a) -> a
unblock0 (MetaHead m env) deflt k = case lookupMeta m of
  MEUnsolved x -> deflt
  MESolved0 x  -> let ~v = (let ?env = env in eval (x^.solution)) in
                  k v (x^.isInline)
  _            -> impossible

-- Discard all unfoldings
whnf :: Val -> Val
whnf = \case
  top@(Flex m sp) -> unblock m top \v _ -> whnf $ spine v sp
  Unfold _ _ v    -> whnf v
  v               -> v

whnf0 :: Val0 -> Val0
whnf0 = \case
  top@(Meta0 m)            -> unblock0 m top \v _ -> whnf0 v
  top@(Splice (Flex m sp)) -> unblock m top \v _ -> case whnf $ spine v sp of
    Quote v -> whnf0 v
    v       -> Splice v
  SolvedMeta0 _ v -> whnf0 v
  v               -> v

-- Update head, unfold metas ("weak head meta normal")
whmnf :: Val -> Val
whmnf = \case
  top@(Flex m sp) -> unblock m top \v _ -> whmnf $ spine v sp
  v               -> v

whmnf0 :: Val0 -> Val0
whmnf0 = \case
  top@(Meta0 m) -> unblock0 m top \v _ -> whmnf0 v
  top@(Splice (Flex m sp)) -> unblock m top \v _ -> case whmnf $ spine v sp of
    Quote v -> whmnf0 v
    v       -> Splice v
  v -> v

-- Update head, preserve all unfoldings
force ::  Val -> Val
force = \case
  top@(Flex m sp) -> unblock m top \ ~v -> \case
    True -> force $ spine v sp
    _    -> Unfold (UHMeta m) sp v
  v -> v

force0 :: Val0 -> Val0
force0 = \case
  top@(Meta0 m) -> unblock0 m top \ ~v -> \case
    True -> force0 v
    _    -> SolvedMeta0 m v
  top@(Splice (Flex m sp)) -> unblock m top \ ~v -> \case
    True  -> case force $ spine v sp of Quote v -> force0 v; v -> Splice v
    False -> Splice (Unfold (UHMeta m) sp v)
  v -> v


-- Readback
--------------------------------------------------------------------------------

class ReadBack a b | a -> b where
  readb :: LvlArg => UnfoldArg => a -> b

{-# inline readBack #-}
readBack :: ReadBack a b => Lvl -> Unfold -> a -> b
readBack l unf = let ?lvl = l; ?unfold = unf in readb

readBackNoUnfold :: ReadBack a b => Lvl -> a -> b
readBackNoUnfold l = readBack l UnfoldNone

readbMetaHead :: LvlArg => UnfoldArg => MetaHead -> S.Tm
readbMetaHead (MetaHead m e) = S.Meta m (readb e)

readbMetaHead0 :: LvlArg => UnfoldArg => MetaHead -> S.Tm0
readbMetaHead0 (MetaHead m e) = S.Meta0 m (readb e)

instance ReadBack Lvl Ix where
  readb = lvlToIx ?lvl

instance ReadBack RigidHead S.Tm where
  readb = \case
    RHLocalVar x -> S.LocalVar (readb x)
    RHPrim p     -> S.Prim p
    RHDCon i     -> S.DCon i
    RHTCon i     -> S.TCon i
    RHRecTy i    -> S.RecTy i
    RHRec i      -> S.Rec i

instance ReadBack UnfoldHead S.Tm where
  readb = \case
    UHMeta m     -> readbMetaHead m
    UHTopDef i   -> S.TopDef i
    UHLocalDef l -> S.LocalVar (readb l)

instance ReadBack Env S.MetaSub where
  readb e = S.MSSub (go e) where
    go :: LvlArg => Env -> S.TmEnv
    go = \case
      ENil      -> S.TENil
      ELet e v  -> S.TELet (go e) (readb v)
      EDef e v  -> S.TEDef (go e) (readb v)
      EDef0 e l -> S.TEDef0 (go e) (readb l)

instance ReadBack Spine (S.Tm -> S.Tm) where
  readb t h = case t of
    SId          -> h
    SApp t u i   -> S.App (readb t h) (readb u) i
    SProject t p -> S.Project (readb t h) p

instance ReadBack ClosureI (S.BindI S.Tm) where
  readb (ClI x i t) = fresh \v -> S.BindI x i (readb (t v))

instance ReadBack Closure0 (S.Bind S.Tm0) where
  readb (Cl0 x t) = freshLvl \l -> S.Bind x (readb (t l))

instance ReadBack Val0 S.Tm0 where
  readb t =
    let t' = case ?unfold of
          UnfoldAll   -> whnf0 t
          UnfoldNone  -> force0 t
          UnfoldMetas -> whmnf0 t
    in case t' of
      LocalVar0 x     -> S.LocalVar0 (readb x)
      Meta0 m         -> readbMetaHead0 m
      SolvedMeta0 m _ -> readbMetaHead0 m
      TopDef0 i       -> S.TopDef0 i
      DCon0 i         -> S.DCon0 i
      App0 t u        -> S.App0 (readb t) (readb u)
      Lam0 a t        -> S.Lam0 (readb a) (readb t)
      Decl0 a t       -> S.Decl0 (readb a) (readb t)
      Project0 t p    -> S.Project0 (readb t) p
      Splice t        -> S.Splice (readb t)

instance ReadBack Val S.Tm where
  readb t =
    let t' = case ?unfold of
          UnfoldAll   -> whnf t
          UnfoldNone  -> force t
          UnfoldMetas -> whmnf t
    in case t' of
      Rigid h sp             -> readb sp (readb h)
      Flex (MetaHead m e) sp -> readb sp (S.Meta m (readb e))
      Unfold h sp _          -> readb sp (readb h)
      Pi a b                 -> S.Pi (readb a) (readb b)
      Lam a t                -> S.Lam (readb a) (readb t)
      Quote t                -> S.Quote (readb t)
