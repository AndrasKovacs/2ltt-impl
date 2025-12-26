
module Pretty (Names, NamesArg, Txt, runTxt, Pretty(..), pretty, prettyTop, dbgPretty) where

import Prelude hiding (pi)
import Common hiding (Prim(..))
import Common qualified as C
import Core.Syntax hiding (splice)
import Evaluation (ReadBack(..), readbNoUnfold)

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

newtype Txt = Txt (String -> String)

runTxt :: Txt -> String
runTxt (Txt f) = f mempty

instance Semigroup Txt where
  {-# inline (<>) #-}
  Txt x <> Txt y = Txt (oneShot (\s -> x $! y s))

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

pretty :: Pretty a => LocalsArg => a -> String
pretty a = let ?prec = letPrec; ?names = localsToNames ?locals in runTxt (prt a)

prettyTop :: Pretty a => a -> String
prettyTop a = let ?locals = LNil in pretty a

dbgPretty :: ReadBack a b => Pretty b => LocalsArg => LvlArg => a -> String
dbgPretty a = pretty (readbNoUnfold a)

instance Pretty Name where
  prt = \case
    NRawName x -> str (show x)
    NSrcName x -> str (show x)
    NOp op     -> error "TODO: operators"
    N_         -> Txt ('_':)

{-# inline par #-}
par :: PrecArg => Int -> Txt -> Txt
par p s | p < ?prec = char '(' <> s <> char ')'
        | True      = s

projPrec, splicePrec, appPrec, piPrec, letPrec :: Int
projPrec   = 201
splicePrec = 200
appPrec    = 100
piPrec     = (-1)
letPrec    = (-2)

proj   x = prt' projPrec   x
splice x = prt' splicePrec x
app    x = prt' appPrec    x
pi     x = prt' piPrec     x
llet   x = prt' letPrec    x

projp   x = par projPrec    x
splicep x = par splicePrec  x
appp    x = par appPrec     x
pip     x = par piPrec      x
lletp   x = par letPrec     x

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
  Pi (BindI x i a b) | x /= N_ -> let pa = llet a in bind x \x -> piBind x i pa <> goPis b
  t                            -> " → " <> pi t

goLams' :: DoPretty (Tm -> Txt)
goLams' = \case
  Lam (BindI x i a t) -> goLams a x i t
  t                   -> ". " <> prt t

goLams :: DoPretty (Tm -> Name -> Icit -> Tm -> Txt)
goLams a x i t = case i of
  Expl -> let pa = llet a in bind x \x -> "(" <> x <> " : " <> pa <> ")" <> goLams' t
  Impl -> let pa = llet a in bind x \x -> "{" <> x <> " : " <> pa <> "}" <> goLams' t

goLams0' :: DoPretty (Tm0 -> Txt)
goLams0' = \case
  Lam0 (Bind x a t) -> goLams0 a x t
  t                 -> ". " <> prt t

goLams0 :: DoPretty (Tm -> Name -> Tm0 -> Txt)
goLams0 a x t =
  bind x \x -> "(" <> x <> " : " <> llet a <> ")" <> goLams0' t

weaken :: (NamesArg => a) -> (NamesArg => a)
weaken act = case ?names of
  Nil -> impossible
  Cons _ xs -> let ?names = xs in act

instance Pretty C.Prim where
  prt = \case
    C.Lift   -> "↑"
    C.Set    -> "Set"
    C.Ty     -> "Ty"
    C.ValTy  -> "ValTy"
    C.CompTy -> "CompTy"
    C.ElVal  -> "ElVal"
    C.ElComp -> "ElComp"
    C.Eq     -> "Eq"
    C.Refl   -> "Refl"
    C.J      -> "J"
    C.K      -> "K"
    C.Fun0   -> "_→_"

instance Pretty Int     where prt = str . show
instance Pretty Ix      where prt = str . show
instance Pretty MetaVar where prt = str . show

instance Pretty Proj where
  prt (Proj i N_) = prt i
  prt (Proj i x)  = prt x

instance Pretty TmEnv where
  prt e = "(" <> go e <> ")" where
    go :: DoPretty (TmEnv -> Txt)
    go = \case
      TENil      -> mempty
      TEDef e t  -> go e <> splice t
      TEBind e t -> go e <> splice t
      TEBind0{}  -> impossible

instance Pretty MetaSub where
  prt = \case
    MSId        -> mempty
    MSSub s     -> prt s

instance Pretty Tm0 where
  prt = \case
    LocalVar0 x         -> localVar x
    TopDef0 i           -> topName (i^.name)
    DCon0 i             -> topName (i^.name)
    Project0 t p        -> projp (proj t <> "." <> prt p)
    App0 t u            -> appp (app t <> " " <> splice u)
    Lam0 (Bind x a t)   -> lletp ("λ " <> goLams0 a x t)
    Decl0 (Bind N_ a t) -> lletp ("let _ : " <> llet a <> "; " <> llet t)
    Decl0 (Bind x a t)  -> let pa = llet a in bind x \x ->
                           lletp ("let " <> x <> " : " <> pa <> "; " <> llet t)
    Splice t            -> splicep ("~" <> proj t)
    Meta0{}             -> impossible
    Rec0{}              -> impossible
    CProject{}          -> impossible
    Let0{}              -> impossible

instance Pretty Tm where
  prt = \case
    LocalVar x  -> localVar x
    TCon i      -> topName (i^.name)
    DCon i      -> topName (i^.name)
    Rec  i      -> topName (i^.name)
    RecTy i     -> topName (i^.name)
    TopDef i    -> topName (i^.name)

    Meta m MSId          -> prt m
    Meta m (MSSub TENil) -> prt m
    Meta m s             -> appp (prt m <> prt s)

    Let t (Bind x a u)   -> let pa = llet a; pt = llet t in bind x \x ->
                            lletp ("let " <> x <> " : " <> pa <> " = " <> pt <> "; " <> llet u)
    Pi (BindI N_ i a b)  -> let pa = app a in bind N_ \_ -> pip (pa <> " → " <> pi b)
    Pi (BindI x i a b)   -> let pa = llet a in bind x  \x -> pip (piBind x i pa <> goPis b)
    Prim p               -> prt p

    Prim C.Fun0 `AppE` a `AppE` b -> pip (app a <> " → " <> pi b)

    App t u Impl         -> appp (app t <> " {" <> llet u <> "}")
    App t u Expl         -> appp (app t <> " " <> splice u)
    Lam (BindI x i a t)  -> lletp ("λ " <> goLams a x i t)
    Project t p          -> projp (proj t <> "." <> prt p)
    Quote t              -> "<" <> llet t <> ">"
    Wk t                 -> weaken $ prt t

instance Pretty Locals where
  prt = \case
    LNil          -> mempty
    LDef ls x t a -> prt ls <> "(" <> prt x <> ":" <> llet a <> " = " <> llet t <> ")"
    LBind ls x a  -> prt ls <> "(" <> prt x <> ":" <> llet a <> ")"
    LBind0{}      -> impossible

--------------------------------------------------------------------------------
