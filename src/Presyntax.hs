{-# options_ghc -funbox-strict-fields #-}

module Presyntax where

import Common hiding (Name)

type Name = Span
type Ty = Tm

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
  | PLvl Pos Lvl Pos  -- record field index
  deriving Show

-- unparsed sequence of operator chunks & explicit and implicit (braced) terms applications
data Unparsed
  = UNil Pos
  | UExpl Tm Unparsed
  | UImpl Tm Unparsed
  | UOp Name Unparsed
  deriving Show

data RecFields
  = RFNil
  | RFCons (Maybe Name) Icit Tm RecFields  -- TODO: sprinkle Pos
  deriving Show

data Tm
  = Lam Pos Bind Icit (Maybe Ty) Tm        -- (\ | λ) (x. t | {x}. t | (x : A). t | {x : A}. t)
  | Let Pos Stage Bind (Maybe Ty) Tm Tm    -- let x = t; u | let x : A = t; u | let x := t; u | let x : A := t; u

  | MetaTy Pos Pos                         -- MetaTy
  | Ty Pos Pos                             -- Ty
  | ValTy Pos Pos                          -- ValTy
  | CompTy Pos Pos                         -- CompTy
  | ElVal Pos Pos                          -- ElVal
  | ElComp Pos Pos                         -- ElComp
  | Prop Pos Pos                           -- Prop

  | Pi Pos Bind Icit Tm Tm                 -- (x : A) -> B | {x : A} -> B
  | Parens Pos Tm Pos                      -- (t)    -- used to correctly track spans
  | Hole Pos                               -- ?
  | Inferred Pos                           -- _
  | Lift Pos Pos                           -- Code | ↑ | ^
  | Quote Pos Tm Pos                       -- <_>
  | Splice Pos Tm                          -- ~t
  | Ident Name                             -- any general identifier
  | LocalLvl Pos Lvl Pos                   -- @n (De Bruijn level)
  | Dot Tm Projection                      -- record field or qualified name or inductive constructor by index
  | Unparsed Unparsed                      -- unparsed operator expression
  | ParserError Pos Pos                    -- delayed parse error
  | Rec Pos RecFields Pos                  -- record
  deriving Show

data RecordDecl
  deriving Show

data Top
  = TNil
  | TDef Pos Stage Bind (Maybe Ty) Tm Top
  | TRecord Pos Stage Name RecordDecl Top
  deriving Show

instance SpanOf Unparsed where
  leftPos = \case
    UNil x    -> leftPos x
    UExpl x _ -> leftPos x
    UImpl x _ -> leftPos x
    UOp x _   -> leftPos x

  rightPos = \case
    UNil x    -> rightPos x
    UExpl _ x -> rightPos x
    UImpl _ x -> rightPos x
    UOp _ x   -> rightPos x

instance SpanOf Projection where
  leftPos = \case
    PName x    -> leftPos x
    PLvl x _ _ -> leftPos x

  rightPos = \case
    PName x    -> rightPos x
    PLvl _ _ x -> rightPos x

instance SpanOf Tm where
  leftPos = \case
    Lam x _ _ _ _   -> leftPos x
    Let x _ _ _ _ _ -> leftPos x
    MetaTy x _      -> leftPos x
    Ty x _          -> leftPos x
    Pi x _ _ _ _    -> leftPos x
    Parens x _ _    -> leftPos x
    Hole x          -> leftPos x
    Quote x _ _     -> leftPos x
    Lift x _        -> leftPos x
    Ident x         -> leftPos x
    LocalLvl x _ _  -> leftPos x
    Dot x _         -> leftPos x
    Unparsed x      -> leftPos x
    ValTy x _       -> leftPos x
    CompTy x _      -> leftPos x
    ElVal x _       -> leftPos x
    ElComp x _      -> leftPos x
    Prop x _        -> leftPos x
    Inferred x      -> leftPos x
    ParserError x _ -> leftPos x
    Splice x _      -> leftPos x
    Rec x _ _       -> leftPos x

  rightPos = \case
    Lam _ _ _ _ x   -> rightPos x
    Let _ _ _ _ _ x -> rightPos x
    MetaTy _ x      -> rightPos x
    Ty _ x          -> rightPos x
    Pi _ _ _ _ x    -> rightPos x
    Parens _ _ x    -> rightPos x
    Hole x          -> rightPos x
    Quote _ _ x     -> rightPos x
    Lift _ x        -> rightPos x
    Ident x         -> rightPos x
    LocalLvl _ _ x  -> rightPos x
    Dot _ x         -> rightPos x
    Unparsed x      -> rightPos x
    ValTy _ x       -> rightPos x
    CompTy _ x      -> rightPos x
    ElVal _ x       -> rightPos x
    ElComp _ x      -> rightPos x
    Prop _ x        -> rightPos x
    Inferred x      -> rightPos x
    ParserError _ x -> rightPos x
    Splice _ x      -> rightPos x
    Rec _ _ x       -> rightPos x
