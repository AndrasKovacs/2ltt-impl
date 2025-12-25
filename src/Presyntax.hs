
module Presyntax where

import Common hiding (Name, Proj(..), Prim(..), Bind(..))

-- TODO: use TH to generate SpanOf instances

type Ty = Tm

data Bind
  = BOp Pos Operator Pos
  | BName SrcName
  | BUnused Pos   -- "_" as a binder
  | BNonExistent  -- a binder which doesn't exist in source (like non-dependent fun domain binder)
  deriving Show

data Projection
  = PName SrcName        -- name
  | POp SrcName          -- operator
  | PLvl Pos Lvl Pos  -- record field index
  deriving Show

data Spine (b :: Bool) where
  SNil    :: Spine 'True
  STm     :: Tm -> Icit -> Spine b -> Spine b
  SOp     :: SrcName -> Spine b -> Spine 'False
  SProjOp :: Tm -> SrcName -> Spine b -> Spine 'False
deriving instance Show (Spine b)

data UnparsedSpine where
  USTm     :: Tm -> Spine 'False -> UnparsedSpine
  USOp     :: SrcName -> Spine b -> UnparsedSpine
  USProjOp :: Tm -> SrcName -> Spine b -> UnparsedSpine
deriving instance Show UnparsedSpine

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
  | Let Pos Stage Bind (Maybe Ty) Tm Tm  -- let x = t; u | let x : A = t; u | let x := t; u | let x : A := t; u
  | Decl0 Pos Bind Ty Tm                 -- let x : a; t   (forward declaration)
  | LetRec Pos Bind (Maybe Ty) Tm Tm     -- letrec x : a := t; u
  | Spine Tm (Spine 'True)
  | Unparsed UnparsedSpine

  | Set Pos Pos                            -- Set
  | Ty Pos Pos                             -- Ty
  | ValTy Pos Pos                          -- ValTy
  | CompTy Pos Pos                         -- CompTy
  | ElVal Pos Pos                          -- ElVal
  | ElComp Pos Pos                         -- ElComp

  | Pi Pos (List MultiBind) Tm             -- (x : A) -> B | {x : A} -> B
  | Parens Pos Tm Pos                      -- (t)    -- used to correctly track spans
  | Hole Pos                               -- ?
  | Inferred Pos                           -- _
  | Lift Pos Pos                           -- ↑ | ^
  | Quote Pos Tm Pos                       -- <_>
  | Splice Pos Tm                          -- ~t
  | Ident SrcName                          -- any general identifier
  | LocalLvl SrcName Lvl Pos               -- x@n (De Bruijn level)
  | Dot Tm Projection                      -- field name or qualified name or record field index
  | Rec Pos RecFields Pos                  -- TODO
  deriving Show

type Record0Decl = List (Bind, Ty)
type Record1Decl = List (Bind, Ty)

data Top
  = TNil Pos -- end of file position
  | TDef Bind Stage (Maybe Ty) Tm Top
  | TDecl Bind Ty Top
  | TInductive0 Pos Bind
  | TInductive1 Pos Bind
  | TRecord Pos Bind (List MultiBind) Ty Record0Decl Top
  deriving Show

instance SpanOf UnparsedSpine where
  leftPos = \case
    USTm x _       -> leftPos x
    USOp x _       -> leftPos x
    USProjOp x _ _ -> leftPos x

  rightPos = \case
    USTm _ x       -> rightPos x
    USOp _ x       -> rightPos x
    USProjOp _ _ x -> rightPos x

instance SpanOf (Spine b) where
  leftPos = \case
    SNil          -> impossible
    STm x _ _     -> leftPos x
    SOp x _       -> leftPos x
    SProjOp x _ _ -> leftPos x

  rightPos = \case
    SNil             -> impossible
    STm x _ SNil     -> rightPos x
    SOp x SNil       -> rightPos x
    SProjOp _ x SNil -> rightPos x
    STm _ _ x        -> rightPos x
    SOp _ x          -> rightPos x
    SProjOp _ _ x    -> rightPos x

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
    Lam x _ _        -> leftPos x
    Let x _ _ _ _ _  -> leftPos x
    LetRec x _ _ _ _ -> leftPos x
    Decl0 x _ _ _    -> leftPos x
    Set x _          -> leftPos x
    Ty x _           -> leftPos x
    Pi x _ _         -> leftPos x
    Parens x _ _     -> leftPos x
    Hole x           -> leftPos x
    Quote x _ _      -> leftPos x
    Lift x _         -> leftPos x
    Ident x          -> leftPos x
    LocalLvl x _ _   -> leftPos x
    Dot x _          -> leftPos x
    Unparsed x       -> leftPos x
    ValTy x _        -> leftPos x
    CompTy x _       -> leftPos x
    ElVal x _        -> leftPos x
    ElComp x _       -> leftPos x
    Inferred x       -> leftPos x
    Splice x _       -> leftPos x
    Rec x _ _        -> leftPos x
    Spine x _        -> leftPos x

  rightPos = \case
    Lam _ _ x        -> rightPos x
    Let _ _ _ _ _ x  -> rightPos x
    LetRec _ _ _ _ x -> rightPos x
    Decl0 _ _ _ x    -> rightPos x
    Set _ x          -> rightPos x
    Ty _ x           -> rightPos x
    Pi _ _ x         -> rightPos x
    Parens _ _ x     -> rightPos x
    Hole x           -> rightPos x
    Quote _ _ x      -> rightPos x
    Lift _ x         -> rightPos x
    Ident x          -> rightPos x
    LocalLvl _ _ x   -> rightPos x
    Dot _ x          -> rightPos x
    Unparsed  x      -> rightPos x
    ValTy _ x        -> rightPos x
    CompTy _ x       -> rightPos x
    ElVal _ x        -> rightPos x
    ElComp _ x       -> rightPos x
    Inferred x       -> rightPos x
    Splice _ x       -> rightPos x
    Rec _ _ x        -> rightPos x
    Spine _ x        -> rightPos x

instance SpanOf Bind where
  leftPos = \case
    BOp x _ _    -> leftPos x
    BName x      -> leftPos x
    BUnused x    -> leftPos x
    BNonExistent -> impossible
  rightPos = \case
    BOp _ _ x    -> rightPos x
    BName x      -> rightPos x
    BUnused x    -> rightPos x
    BNonExistent -> impossible

instance SpanOf Top where
  leftPos = \case
    TNil x              -> leftPos x
    TDef x _ _ _ _      -> leftPos x
    TDecl x _ _         -> leftPos x
    TInductive0 x _     -> leftPos x
    TInductive1 x _     -> leftPos x
    TRecord x _ _ _ _ _ -> leftPos x

  rightPos = \case
    TNil x              -> rightPos x
    TDef _ _ _ _ x      -> rightPos x
    TDecl _ _ x         -> rightPos x
    TInductive0 _ x     -> rightPos x
    TInductive1 x _     -> rightPos x
    TRecord x _ _ _ _ _ -> rightPos x
