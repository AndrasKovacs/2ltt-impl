
module Presyntax where

import Common hiding (Name, Proj(..), Prim(..), Bind(..))

type Ty = Tm

data Bind
  = BOp Operator
  | BName RawName
  | BUnused Pos   -- "_" as a binder
  | BNonExistent  -- a binder which doesn't exist in source (like non-dependent fun domain binder)
  deriving Show

data Projection
  = PName RawName        -- name
  | POp RawName          -- operator
  | PLvl Pos Lvl Pos  -- record field index
  deriving Show

data Spine (b :: Bool) where
  SNil    :: Spine 'True
  STm     :: Tm -> Icit -> Spine b -> Spine b
  SOp     :: RawName -> Spine b -> Spine 'False
  SProjOp :: Tm -> RawName -> Spine b -> Spine 'False
deriving instance Show (Spine b)

data UnparsedSpine where
  USTm     :: Tm -> Spine 'False -> UnparsedSpine
  USOp     :: RawName -> Spine b -> UnparsedSpine
  USProjOp :: Tm -> RawName -> Spine b -> UnparsedSpine
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
  | Ident RawName                          -- any general identifier
  | LocalLvl Pos Lvl Pos                   -- @n (De Bruijn level)
  | Dot Tm Projection                      -- field name or qualified name or record field index

  | Rec Pos RecFields Pos                  -- TODO
  | RecTy Pos (List (Bind, Ty)) Pos        -- TODO
  deriving Show

type Record0Decl = List (Bind, Ty)
type Record1Decl = List (Bind, Ty)

data Top
  = TNil
  | TDef Stage Bind (Maybe Ty) Tm Top
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
    SNil          -> impossible
    STm _ _ x     -> rightPos x
    SOp _ x       -> rightPos x
    SProjOp _ _ x -> rightPos x

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
    RecTy x _ _      -> leftPos x
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
    RecTy _ _ x      -> rightPos x
    Rec _ _ x        -> rightPos x
    Spine _ x        -> rightPos x
