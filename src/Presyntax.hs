{-# options_ghc -funbox-strict-fields #-}

module Presyntax where

import Common hiding (Name, Icit(..))

type Name = Span
type Ty = Tm

data Icit = Impl Pos Pos | Expl
  deriving Show

newtype Precedence = Precedence Int
  deriving (Eq, Show, Num, Ord, Enum) via Int

data Fixity = FLeft | FRight | FNon | FClosed
  deriving Show

data OpDecl = OpDecl Fixity (List Name) Precedence
  deriving Show

data Bind
  = BOp OpDecl
  | BName Name
  | BUnused Pos
  deriving Show

data Projection
  = PName Name        -- name
  | POp Name          -- operator
  | PLvl Pos Lvl Pos  -- record field index
  deriving Show

data SpineEntry
  = SETm Tm
  | SEOp Name
  | SEProjOp Tm Name
  deriving Show

data Spine
  = SNil
  | SCons SpineEntry Icit Spine
  deriving Show

-- TODO
data RecField = RecField
  deriving Show

data RecFields
  = RFNil
  | RFCons RecField RecFields
  deriving Show

data MultiBind = MultiBind (List Bind) Icit (Maybe Ty)
  deriving Show

data Tm
  = Lam Pos (List MultiBind) Tm
  | Let Pos Stage Bind (Maybe Ty) Tm Tm    -- let x = t; u | let x : A = t; u
                                           --  | let x := t; u | let x : A := t; u
  | Spine Tm Spine
  | Unparsed SpineEntry Spine

  | Set Pos Pos                            -- Set
  | Ty Pos Pos                             -- Ty
  | ValTy Pos Pos                          -- ValTy
  | CompTy Pos Pos                         -- CompTy
  | ElVal Pos Pos                          -- ElVal
  | ElComp Pos Pos                         -- ElComp
  | Prop Pos Pos                           -- Prop

  | Pi Pos (List MultiBind) Tm             -- (x : A) -> B | {x : A} -> B
  | Parens Pos Tm Pos                      -- (t)    -- used to correctly track spans
  | Hole Pos                               -- ?
  | Inferred Pos                           -- _
  | Lift Pos Pos                           -- ↑ | ^
  | Quote Pos Tm Pos                       -- <_>
  | Splice Pos Tm                          -- ~t
  | Ident Name                             -- any general identifier
  | LocalLvl Pos Lvl Pos                   -- @n (De Bruijn level)
  | Dot Tm Projection                      -- field name or qualified name or record field index

  | Rec Pos RecFields Pos                  -- rec (<fields>)
  | RecTy Pos RecTyFields Pos              -- Rec (<type fields>)
  deriving Show

data Record0Decl
  deriving Show

data Record1Decl
  deriving Show

data RecTyFields = RecTyFields
  deriving Show

data Top
  = TNil
  | TDef Stage Bind (Maybe Ty) Tm Top
  | TInductive0 Pos Name
  | TRecord0 Pos Name Record0Decl Top
  | TRecord1 Pos Name Record1Decl Top
  deriving Show

instance SpanOf SpineEntry where
  leftPos = \case
    SETm x       -> leftPos x
    SEOp x       -> leftPos x
    SEProjOp x _ -> leftPos x

  rightPos = \case
    SETm x       -> rightPos x
    SEOp x       -> rightPos x
    SEProjOp _ x -> rightPos x

instance SpanOf Spine where
  leftPos = \case
    SCons _ (Impl x _) _ -> leftPos x
    SCons x Expl _       -> leftPos x
    SNil                 -> impossible

  rightPos = \case
    SCons _ (Impl _ x) SNil -> rightPos x
    SCons x Expl SNil       -> rightPos x
    SCons _ _ x             -> rightPos x
    SNil                    -> impossible

instance SpanOf Projection where
  leftPos = \case
    PName x    -> leftPos x
    PLvl x _ _ -> leftPos x
    POp x      -> leftPos x

  rightPos = \case
    PName x    -> rightPos x
    PLvl _ _ x -> rightPos x
    POp x      -> rightPos x

instance SpanOf Tm where
  leftPos = \case
    Lam x _ _       -> leftPos x
    Let x _ _ _ _ _ -> leftPos x
    Set x _         -> leftPos x
    Ty x _          -> leftPos x
    Pi x _ _        -> leftPos x
    Parens x _ _    -> leftPos x
    Hole x          -> leftPos x
    Quote x _ _     -> leftPos x
    Lift x _        -> leftPos x
    Ident x         -> leftPos x
    LocalLvl x _ _  -> leftPos x
    Dot x _         -> leftPos x
    Unparsed x _    -> leftPos x
    ValTy x _       -> leftPos x
    CompTy x _      -> leftPos x
    ElVal x _       -> leftPos x
    ElComp x _      -> leftPos x
    Prop x _        -> leftPos x
    Inferred x      -> leftPos x
    Splice x _      -> leftPos x
    Rec x _ _       -> leftPos x
    RecTy x _ _     -> leftPos x
    Spine x _       -> leftPos x

  rightPos = \case
    Lam _ _ x       -> rightPos x
    Let _ _ _ _ _ x -> rightPos x
    Set _ x         -> rightPos x
    Ty _ x          -> rightPos x
    Pi _ _ x        -> rightPos x
    Parens _ _ x    -> rightPos x
    Hole x          -> rightPos x
    Quote _ _ x     -> rightPos x
    Lift _ x        -> rightPos x
    Ident x         -> rightPos x
    LocalLvl _ _ x  -> rightPos x
    Dot _ x         -> rightPos x
    Unparsed _ x    -> rightPos x
    ValTy _ x       -> rightPos x
    CompTy _ x      -> rightPos x
    ElVal _ x       -> rightPos x
    ElComp _ x      -> rightPos x
    Prop _ x        -> rightPos x
    Inferred x      -> rightPos x
    Splice _ x      -> rightPos x
    RecTy _ _ x     -> rightPos x
    Rec _ _ x       -> rightPos x
    Spine _ x       -> rightPos x
