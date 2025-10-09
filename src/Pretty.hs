
module Pretty (Names, NamesArg, Txt, runTxt, Pretty(..), pretty) where

import Prelude hiding (pi)
import Common
import Core

--------------------------------------------------------------------------------

{-
- Shadowed locals are disambiguated with DB levels. There's a separate DB namespace
  for each local name, including "_"

- Shadowed top-level names are printed with full qualification.

- Printing precedences are compatible with parsing precedences.
  - 0-99:    operators weaker than application
  - 100:     application
  - 101-199: operators stronger than application
  - 200:     splice
  - 201:     projection

- TODO:
  - proper layouts (linebreak, indentation)
  - toggle unicode printing for builtins
  - toggle elab-filled implicit argument printing

-}

--------------------------------------------------------------------------------

type Names = List Name
type NamesArg = (?names :: Names)

localsToNames :: Locals -> Names
localsToNames = \case
  LNil          -> Nil
  LDef ls x _ _ -> Cons x (localsToNames ls)
  LBind0 ls x _ -> Cons x (localsToNames ls)
  LBind ls x _  -> Cons x (localsToNames ls)

newtype Txt = Txt (String -> String)

runTxt :: Txt -> String
runTxt (Txt f) = f mempty

instance Semigroup Txt where
  {-# inline (<>) #-}
  Txt x <> Txt y = Txt (\s -> x $! y s)

instance Monoid Txt where
  {-# inline mempty #-}
  mempty = Txt id

instance IsString Txt where
  {-# inline fromString #-}
  fromString = \case
    []                    -> Txt \acc -> acc
    (a:[])                -> Txt \acc -> a:acc
    (a:b:[])              -> Txt \acc -> a:b:acc
    (a:b:c:[])            -> Txt \acc -> a:b:c:acc
    (a:b:c:d:[])          -> Txt \acc -> a:b:c:d:acc
    (a:b:c:d:e:[])        -> Txt \acc -> a:b:c:d:e:acc
    (a:b:c:d:e:f:[])      -> Txt \acc -> a:b:c:d:e:f:acc
    (a:b:c:d:e:f:g:[])    -> Txt \acc -> a:b:c:d:e:f:g:acc
    (a:b:c:d:e:f:g:h:[])  -> Txt \acc -> a:b:c:d:e:f:g:h:acc
    (a:b:c:d:e:f:g:h:i:s) -> Txt \acc -> let s' = foldr' (:) s acc in
                                         a:b:c:d:e:f:g:h:i:s'

instance Show Txt where
  show (Txt s) = s []

str    = fromString :: String -> Txt; {-# inline str #-}
char c = Txt (c:); {-# inline char #-}

type PrecArg = (?prec :: Int)
type DoPretty a = PrecArg => NamesArg => a

class Pretty a where
  prt :: DoPretty (a -> Txt)

prt' :: Pretty a => Int -> NamesArg => a -> Txt
prt' p a = let ?prec = p in prt a

pretty :: Pretty a => LocalsArg => a -> Txt
pretty a = let ?prec = (-2); ?names = localsToNames ?locals in prt a

instance Pretty Name where
  prt = \case
    NRawName x -> str (show x)
    NOp op     -> error "TODO: operators"
    N_         -> Txt ('_':)

{-# inline par #-}
par :: PrecArg => Int -> Txt -> Txt
par p s | p < ?prec = char '(' <> s <> char ')'
        | True      = s

proj   x = prt' 201  x
splice x = prt' 200  x
app    x = prt' 100  x
pi     x = prt' (-1) x
llet   x = prt' (-2) x

projp   x = par 201  x
splicep x = par 200  x
appp    x = par 100  x
pip     x = par (-1) x
lletp   x = par (-2) x

localVar :: DoPretty (Ix -> Txt)
localVar i = let

  go :: Names -> Ix -> (Name, (Int, Int))
  go (Cons x xs) 0 = (x // go' xs x 0 // 0)
  go (Cons x xs) i = let (x', (pre, post)) = go xs (i - 1)
                         post' = if x == x' then post + 1 else post
                     in (x', (pre, post'))
  go _           _ = error "out of scope variable"

  go' :: Names -> Name -> Int -> Int
  go' Nil          _ acc = acc
  go' (Cons x' xs) x acc = let acc' = if x == x' then acc' + 1 else acc
                           in go' xs x acc'

  -- variable name, name occurrences before i, occurrences after i
  (x, (before, after)) = go ?names i

  in case after of
    0 -> prt x
    _ -> prt x <> "@" <> prt before


topName :: DoPretty (Name -> Txt)
topName x | elem x ?names = "Main." <> prt x
          | True          = prt x

{-# inline bind #-}
bind :: Name -> DoPretty (Txt -> a) -> DoPretty a
bind x act = let ?names = Cons x ?names in act (prt x)

{-# inline piBind #-}
piBind :: Txt -> Icit -> Txt -> Txt
piBind x Impl a = "{" <> x <> " : " <> a <> "}"
piBind x Expl a = "(" <> x <> " : " <> a <> ")"

goPis :: DoPretty (Tm -> Txt)
goPis = \case
  Pi a (BindI x i b) | x /= N_ -> let pa = app a in bind x \x -> piBind x i pa <> goPis b
  t                            -> " → " <> pi t

goLams' :: DoPretty (Tm -> Txt)
goLams' = \case
  Lam a (BindI x i t) -> goLams a x i t
  t                   -> ". " <> prt t

goLams :: DoPretty (Tm -> Name -> Icit -> Tm -> Txt)
goLams a x i t = case i of
  Expl -> bind x \x -> "(" <> x <> " : " <> llet a <> ")" <> goLams' t
  Impl -> bind x \x -> "{" <> x <> " : " <> llet a <> "}" <> goLams' t

goLams0' :: DoPretty (Tm0 -> Txt)
goLams0' = \case
  Lam0 a (Bind x t) -> goLams0 a x t
  t                 -> ". " <> prt t

goLams0 :: DoPretty (Tm -> Name -> Tm0 -> Txt)
goLams0 a x t =
  bind x \x -> "(" <> x <> " : " <> llet a <> ")" <> goLams0' t

instance Pretty Prim where
  prt = \case
    Lift   -> "↑"
    Set    -> "Set"
    Ty     -> "Ty"
    ValTy  -> "ValTy"
    CompTy -> "CompTy"
    ElVal  -> "ElVal"
    ElComp -> "ElComp"
    Eq     -> "Eq"
    Refl   -> "Refl"
    J      -> "J"
    K      -> "K"
    Fun0   -> "_→_"

instance Pretty Int     where prt = str . show
instance Pretty Ix      where prt = str . show
instance Pretty MetaVar where prt = str . show

instance Pretty Proj where
  prt (Proj i N_) = prt i
  prt (Proj i x)  = prt x

instance Pretty Tm0 where
  prt = \case
    LocalVar0 x         -> localVar x
    TopDef0 i           -> topName (i^.name)
    DCon0 i             -> topName (i^.name)
    Project0 t p        -> projp (proj t <> "." <> prt p)
    App0 t u            -> appp (app t <> " " <> splice u)
    Lam0 a (Bind x t)   -> lletp ("λ " <> goLams0 a x t)
    Decl0 a (Bind N_ t) -> lletp ("let _ : " <> llet a <> "; " <> llet t)
    Decl0 a (Bind x t)  -> let pa = llet a in bind x \x ->
                           lletp ("let " <> x <> " : " <> pa <> "; " <> llet t)
    Splice t            -> splicep ("~" <> proj t)

instance Pretty Tm where
  prt = \case
    LocalVar x -> localVar x
    TCon i     -> topName (i^.name)
    DCon i     -> topName (i^.name)
    RecCon i   -> topName (i^.name)
    RecTy i    -> topName (i^.name)
    TopDef i   -> topName (i^.name)
    Meta m     -> "?" <> prt m

    Let a t (Bind x u)   -> let pa = llet a; pt = llet t in bind x \x ->
                            lletp ("let " <> x <> " : " <> pa <> " = " <> pt <> "; " <> llet u)
    Pi a (BindI N_ i b)  -> let pa = app a in bind N_ \_ -> pip (pa <> " → " <> pi b)
    Pi a (BindI x i b)   -> let pa = app a in bind x  \x -> pip (piBind x i pa <> goPis b)
    Prim p               -> prt p

    Prim Fun0 `AppE` a `AppE` b -> pip (app a <> " → " <> pi b)

    App t u Impl         -> appp (app t <> " {" <> splice u <> "}")
    App t u Expl         -> appp (app t <> " " <> splice u)
    Lam a (BindI x i t)  -> lletp ("λ " <> goLams a x i t)
    Project t p          -> projp (proj t <> "." <> prt p)
    Quote t              -> "<" <> llet t <> ">"


--------------------------------------------------------------------------------
