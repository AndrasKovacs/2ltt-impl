
module Evaluation where

import Common hiding (Prim(..))
import Common      qualified as C
import Core.Syntax qualified as S
import Core.Info
import Core.Value
import Elaboration.State

{-# inline def #-}
def :: Val -> (Val -> EnvArg => a) -> EnvArg => a
def v k = let ?env = EBind ?env v in k v

{-# inline def0 #-}
def0 :: Val0 -> (Val0 -> EnvArg => a) -> EnvArg => a
def0 v k = let ?env = EBind0 ?env v in k v

{-# inline freshLvl #-}
freshLvl :: (LvlArg => Lvl -> a) -> LvlArg => a
freshLvl k = let v = ?lvl in let ?lvl = v + 1 in k v

{-# inline fresh #-}
fresh :: VTy -> (LvlArg => Val -> a) -> LvlArg => a
fresh ~a k = freshLvl \l -> k (LocalVar l a)

{-# inline fresh0 #-}
fresh0 :: (LvlArg => Val0 -> a) -> LvlArg => a
fresh0 k = freshLvl \l -> k (LocalVar0 l)

{-# inline defLazy #-}
defLazy :: Val -> (EnvArg => a) -> EnvArg => a
defLazy ~v k = let ?env = EDef ?env v in k

class Eval a b | a -> b where
  eval :: EnvArg => a -> b

evalIn :: Eval a b => Env -> a -> b
evalIn e a = let ?env = e in eval a

lookupIx :: EnvArg => Ix -> Val
lookupIx x = go ?env x where
  go (EBind _ v)  0 = v
  go (EDef _ v)   0 = v
  go (EBind e _)  x = go e (x - 1)
  go (EBind0 e _) x = go e (x - 1)
  go (EDef e _)   x = go e (x - 1)
  go _            _ = impossible

lookupIx0 :: EnvArg => Ix -> Val0
lookupIx0 x = go ?env x where
  go (EBind0 _ l) 0 = l
  go (EBind e _)  x = go e (x - 1)
  go (EBind0 e _) x = go e (x - 1)
  go (EDef e _)   x = go e (x - 1)
  go _            _ = impossible

{-# inline geval #-}
geval :: Eval a Val => EnvArg => a -> G
geval a = gjoin (eval a)

instance Eval (Bind S.Tm0) Closure0 where
  {-# inline eval #-}
  eval (Bind x a t) = Cl0 x (eval a) \v -> def0 v \_ -> eval t

instance Eval (BindI S.Tm) ClosureI where
  {-# inline eval #-}
  eval (BindI x i a t) = ClI x i (eval a) \v -> def v \_ -> eval t

instance Eval (Bind S.Tm) Closure where
  {-# inline eval #-}
  eval (Bind x a t) = Cl x (eval a) \v -> def v \_ -> eval t

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

spine0 :: Val0 -> Spine0 -> Val0
spine0 v sp = case sp of
  S0Id            -> v
  S0CProject sp p -> cproject0 (spine0 v sp) p

projFromSpine :: Spine -> Ix -> Val
projFromSpine sp x = case (sp, x) of
  (SApp _ u _ , 0) -> u
  (SApp sp _ _, x) -> projFromSpine sp (x - 1)
  _                -> impossible

proj :: Val -> Proj -> Val
proj t p = case t of
  Rec _ spn      -> projFromSpine spn (p^.index)
  Rigid h spn    -> Rigid  h (SProject spn p)
  Flex h spn     -> Flex   h (SProject spn p)
  Unfold h spn v -> Unfold h (SProject spn p) (proj v p)
  _              -> impossible

gproj :: G -> Proj -> G
gproj (G v fv) p = G (proj v p) (proj fv p)

quote :: Val0 -> Val
quote = \case
  Splice v S0Id -> v
  v             -> Quote v

splice :: Val -> Val0
splice = \case
  Quote t -> t
  t       -> Splice t S0Id

meta :: MetaVar -> Env -> Val
meta m e =
  let h = MetaHead m e in
  unblock h (Flex h SId) \ ~v -> \case
    True  -> v
    False -> Unfold (UHMeta h) SId v

meta0 :: MetaVar -> Env -> Val0
meta0 m e =
  let h = MetaHead m e in
  unblock0 h (Flex0 h S0Id) \ ~v -> \case
    True  -> v
    False -> Unfold0 h S0Id v

instance Eval S.TmEnv Env where
  eval = \case
    S.TENil       -> ENil
    S.TEDef e t   -> EDef   (eval e) (eval t)
    S.TEBind e t  -> EBind  (eval e) (eval t)
    S.TEBind0 e t -> EBind0 (eval e) (eval t)

instance Eval S.MetaSub Env where
  eval = \case
    S.MSId    -> ?env
    S.MSSub s -> eval s

cproject0 :: Val0 -> Proj -> Val0
cproject0 v p = case v of
  CRec i args    -> elemAt args (p^.index)
  Unfold0 m sp v -> Unfold0 m (S0CProject sp p) (cproject0 v p)
  Flex0 m sp     -> Flex0  m (S0CProject sp p)
  Rigid0 v sp    -> Rigid0 v (S0CProject sp p)
  Splice v sp    -> Splice v (S0CProject sp p)
  v              -> Rigid0 v (S0CProject S0Id p)

-- | TODO: share this value in Rec0Info
rec0 :: Rec0Info -> Val0
rec0 i = if i^.isComp then CRec i Nil else Rec0 i

weaken :: (EnvArg => a) -> (EnvArg => a)
weaken act = case ?env of
  EBind e _ -> let ?env = e in act
  _         -> impossible

instance Eval S.Tm0 Val0 where
  eval = \case
    S.LocalVar0 x   -> lookupIx0 x
    S.Meta0 m sub   -> meta0 m (eval sub)
    S.TopDef0 di    -> TopDef0 di
    S.DCon0 di      -> DCon0 di
    S.Project0 t p  -> Project0 (eval t) p
    S.App0 t u      -> App0 (eval t) (eval u)
    S.Lam0 t        -> Lam0 (eval t)
    S.Decl0 t       -> Decl0 (eval t)
    S.Splice t      -> splice (eval t)
    S.Let0 t u      -> Let0 (eval t) (eval u)
    S.CProject hd p -> cproject0 (eval hd) p
    S.Rec0 i        -> rec0 i

instance Eval S.Tm Val where
  eval = \case
    S.LocalVar x  -> lookupIx x
    S.TCon i      -> i^.value
    S.DCon i      -> i^.value
    S.RecTy i     -> i^.tConValue
    S.Rec i       -> i^.dConValue
    S.TopDef i    -> i^.value
    S.Let t u     -> def (eval t) \v -> eval u ∙ v
    S.Pi b        -> Pi (eval b)
    S.Prim p      -> eval p
    S.App t u i   -> eval t ∙∘ (eval u, i)
    S.Lam t       -> Lam (eval t)
    S.Project t p -> proj (eval t) p
    S.Quote t     -> quote (eval t)
    S.Meta m sub  -> meta m (eval sub)
    S.Wk t        -> weaken $ eval t

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
  Unfold0 _ _ v                -> whnf0 v
  top@(Flex0 m sp)             -> unblock0 m top \v _ -> whnf0 $ spine0 v sp
  top@(Splice (Flex m sp) sp') -> unblock m top \v _ -> case whnf $ spine v sp of
    Quote v -> whnf0 $ spine0 v sp'
    v       -> Splice v sp'
  top@(Splice (Unfold _ _ v) sp') -> case whnf v of
    Quote v -> whnf0 $ spine0 v sp'
    v       -> Splice v sp'
  v -> v

-- Update head, unfold metas ("weak head meta normal")
whmnf :: Val -> Val
whmnf = \case
  top@(Flex m sp) -> unblock m top \v _ -> whmnf $ spine v sp
  v               -> v

whmnf0 :: Val0 -> Val0
whmnf0 = \case
  Unfold0 _ _ v                -> whmnf0 v
  top@(Flex0 m sp)             -> unblock0 m top \v _ -> whmnf0 $ spine0 v sp
  top@(Splice (Flex m sp) sp') -> unblock m top \v _ -> case whmnf $ spine v sp of
    Quote v -> whmnf0 $ spine0 v sp'
    v       -> Splice v sp'
  v -> v

-- Update head, preserve all unfoldings
force ::  Val -> Val
force = \case
  top@(Flex m sp) -> unblock m top \ ~v -> \case
    True -> force $ spine v sp
    _    -> Unfold (UHMeta m) sp (spine v sp)
  v -> v

force0 :: Val0 -> Val0
force0 = \case
  top@(Flex0 m sp) -> unblock0 m top \ ~v -> \case
    True -> force0 $ spine0 v sp
    _    -> Unfold0 m sp (spine0 v sp)
  top@(Splice (Flex m sp) sp') -> unblock m top \ ~v -> \case
    True -> case force $ spine v sp of
      Quote v -> force0 $ spine0 v sp'
      v       -> Splice v sp'
    _    -> Splice (Unfold (UHMeta m) sp (spine v sp)) sp'
  v -> v


-- Readback
--------------------------------------------------------------------------------

class ReadBack a b | a -> b where
  readb :: LvlArg => UnfoldArg => a -> b

readbNoUnfold :: ReadBack a b => LvlArg => a -> b
readbNoUnfold = readBackNoUnfold ?lvl

normalize :: ReadBack a b => LvlArg => a -> b
normalize a = readBack ?lvl UnfoldAll a

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
    RHLocalVar x _ -> S.LocalVar (readb x)
    RHPrim p       -> S.Prim p
    RHDCon i       -> S.DCon i
    RHTCon i       -> S.TCon i
    RHRecTy i      -> S.RecTy i
    RHRec i        -> S.Rec i

instance ReadBack UnfoldHead S.Tm where
  readb = \case
    UHMeta m       -> readbMetaHead m
    UHTopDef i     -> S.TopDef i
    UHLocalDef l _ -> S.LocalVar (readb l)

instance ReadBack Env S.MetaSub where
  readb e = S.MSSub (go e) where
    go :: LvlArg => Env -> S.TmEnv
    go = \case
      ENil       -> S.TENil
      EDef e v   -> S.TEDef   (go e) (readb v)
      EBind e v  -> S.TEBind  (go e) (readb v)
      EBind0 e l -> S.TEBind0 (go e) (readb l)

instance ReadBack Spine (S.Tm -> S.Tm) where
  readb t h = case t of
    SId          -> h
    SApp t u i   -> S.App (readb t h) (readb u) i
    SProject t p -> S.Project (readb t h) p

instance ReadBack ClosureI (BindI S.Tm) where
  readb (ClI x i a t) = BindI x i (readb a) $ fresh a \v -> readb (t v)

instance ReadBack Closure0 (Bind S.Tm0) where
  readb (Cl0 x a t) = Bind x (readb a) $ fresh0 \v -> readb (t v)

forceUnfold :: UnfoldArg => Val -> Val
forceUnfold t = case ?unfold of
  UnfoldAll   -> whnf t
  UnfoldNone  -> force t
  UnfoldMetas -> whmnf t

forceUnfold0 :: UnfoldArg => Val0 -> Val0
forceUnfold0 t = case ?unfold of
  UnfoldAll   -> whnf0 t
  UnfoldNone  -> force0 t
  UnfoldMetas -> whmnf0 t

instance ReadBack Spine0 (S.Tm0 -> S.Tm0) where
  readb sp hd = case sp of
    S0Id            -> hd
    S0CProject sp p -> S.CProject (readb sp hd) p

instance ReadBack (SnocList Val0) (S.Tm0 -> S.Tm0) where
  readb args hd = case args of
    Nil         -> hd
    Snoc args v -> S.App0 (readb args hd) (readb v)

instance ReadBack Val0 S.Tm0 where
  readb t = case forceUnfold0 t of
    Unfold0 m sp _  -> readb sp (readbMetaHead0 m)
    Rigid0 v sp     -> readb sp (readb v)
    Flex0 m sp      -> readb sp (readbMetaHead0 m)
    Splice v sp     -> readb sp (S.splice (readb v))
    TopDef0 i       -> S.TopDef0 i
    DCon0 i         -> S.DCon0 i
    App0 t u        -> S.App0 (readb t) (readb u)
    Lam0 t          -> S.Lam0 (readb t)
    Decl0 t         -> S.Decl0 (readb t)
    Let0 t u        -> S.Let0 (readb t) (readb u)
    Project0 t p    -> S.Project0 (readb t) p
    LocalVar0 x     -> S.LocalVar0 (readb x)
    CRec i args     -> readb args (S.Rec0 i)
    Rec0 i          -> S.Rec0 i

instance ReadBack Val S.Tm where
  readb t = case forceUnfold t of
    Rigid h sp             -> readb sp (readb h)
    Flex (MetaHead m e) sp -> readb sp (S.Meta m (readb e))
    Unfold h sp _          -> readb sp (readb h)
    Pi b                   -> S.Pi (readb b)
    Lam t                  -> S.Lam (readb t)
    Quote t                -> S.Quote (readb t)

-- Type computation
----------------------------------------------------------------------------------------------------

-- | Input: type of function, arg value.
--   Output: Domain name, icitness, type, type of result
appTy :: VTy -> Val -> (Name, Icit, VTy, VTy)
appTy funty ~arg = case whnf funty of
  Pi b -> (b^.name, b^.icit, b^.ty, b ∙ arg)
  _    -> impossible

recParamEnv :: Spine -> Env
recParamEnv = \case
  SId         -> ENil
  SApp sp t _ -> EDef (recParamEnv sp) t
  _           -> impossible

recFieldEnv :: FieldInfo -> Proj -> Spine -> Val -> Env
recFieldEnv fs (Proj ix x) params vt = case fs of
  FINil           -> recParamEnv params
  FISnoc fs _ _ _ -> EDef (recFieldEnv fs (Proj (ix + 1) x) params vt)
                          (proj vt (Proj ix x))

-- | Input: value, its type, projection.
--   Output: RecInfo, record parameters, type of result
projTy :: Val -> VTy -> Proj -> (RecInfo, Spine, VTy)
projTy t a (Proj ix x) = case whnf t of
  RecTy i params ->
    let go :: FieldInfo -> Ix -> Ix -> VTy
        go fs ix here = case (fs, ix) of
          (FISnoc fs x i a, 0 ) -> evalIn (recFieldEnv fs (Proj here x) params t) a
          (FISnoc fs _ _ _, ix) -> go fs (ix - 1) (here + 1)
          _                     -> impossible
    in (i, params, go (i^.fields) ix 0)
  _ -> impossible

----------------------------------------------------------------------------------------------------
