
module Elaboration.State where

import qualified Data.Array.Dynamic.L as ADL
import qualified Data.Ref.F as RF
import qualified Data.Vector.Mutable as VM
import qualified Data.Vector.Hashtables as HT
import qualified Data.Primitive.MutVar as P

import Common
import Core (Tm, Ty, Locals, LocalsArg)
import qualified Core as C
import Value (VTy)

-- Metacontext
--------------------------------------------------------------------------------

data Unsolved = Unsolved {
    unsolvedLocals :: Locals
  , unsolvedTy     :: Ty       -- the type is under the Locals
  }
makeFields ''Unsolved

-- TODO: optimize closed solutions by using call-by-need instead of call-by-name?
data Solved = Solved {
    solvedLocals      :: Locals
  , solvedTy          :: Ty
  , solvedSolution    :: Tm     -- the type and solution are under the Locals
  , solvedIsInline    :: Bool   -- should we immediately unfold the meta
  , solvedOccursCache :: RF.Ref MetaVar
  }
makeFields ''Solved

data MetaEntry = MEUnsolved Unsolved | MESolved Solved

type MetaCxt = ADL.Array MetaEntry

metaCxt :: MetaCxt
metaCxt = runIO ADL.empty
{-# noinline metaCxt #-}

nextMeta :: IO MetaVar
nextMeta = coerce <$!> ADL.size metaCxt

readMeta :: MetaVar -> IO MetaEntry
readMeta (MkMetaVar i) = ADL.read metaCxt i
{-# inline readMeta #-}

lookupMeta :: MetaVar -> MetaEntry
lookupMeta (MkMetaVar i) = runIO (ADL.read metaCxt i)
{-# inline lookupMeta #-}

writeMeta :: MetaVar -> MetaEntry -> IO ()
writeMeta (MkMetaVar i) e = ADL.write metaCxt i e
{-# inline writeMeta #-}

newMeta :: LocalsArg => Ty -> IO MetaVar
newMeta a = do
  s <- ADL.size metaCxt
  ADL.push metaCxt (MEUnsolved (Unsolved ?locals a))
  pure (coerce s)
{-# inline newMeta #-}

-- | Trim the size of the metacontext to `Lvl`.
resetMetaCxt :: MetaVar -> IO ()
resetMetaCxt size = do
  currSize <- nextMeta
  if size < currSize then ADL.pop metaCxt >> resetMetaCxt size
                     else pure ()

-- Frozen metas
--------------------------------------------------------------------------------

frozen :: RF.Ref MetaVar
frozen = runIO $ RF.new 0
{-# noinline frozen #-}

-- | Freeze all current metas, return size of metacontext.
freezeMetas :: IO MetaVar
freezeMetas = do
  frz <- nextMeta
  RF.write frozen frz
  pure frz

isFrozen :: MetaVar -> IO Bool
isFrozen x = do
  frz <- RF.read frozen
  pure $! x < frz

-- Identifier scope
--------------------------------------------------------------------------------

data LocalInfo = LI {
    localInfoName :: Name
  , localInfoLvl  :: Lvl
  , localInfoVTy  :: VTy
  }
makeFields ''LocalInfo

data ISEntry
  = ISNil
  | ISTopDef    {-# nounpack #-} C.DefInfo
  | ISTopRec    {-# nounpack #-} C.RecInfo
  | ISTopTCon   {-# nounpack #-} C.TConInfo
  | ISTopDef0   {-# nounpack #-} C.Def0Info
  | ISTopRec0   {-# nounpack #-} C.Rec0Info
  | ISTopTCon0  {-# nounpack #-} C.TCon0Info
  | ISTopDCon (List C.DConInfo)
  | ISLocal LocalInfo ISEntry

type IdentScope =
  HT.Dictionary (HT.PrimState IO) VM.MVector Name VM.MVector ISEntry

identScope :: IdentScope
identScope = runIO $ HT.initialize 5
{-# noinline identScope #-}

{-# noinline localDefineInsert #-}
localDefineInsert :: LocalInfo -> Name -> IO ()
localDefineInsert i x =
  HT.upsert identScope (maybe (ISLocal i ISNil) (ISLocal i)) x

{-# noinline localDefineDelete #-}
localDefineDelete :: Name -> IO ()
localDefineDelete x = HT.alter identScope go x where
  go (Just (ISLocal _ e)) = Just e
  go _                    = impossible

{-# inline localDefineIS #-}
localDefineIS :: LvlArg => Name -> VTy -> IO a -> IO a
localDefineIS x a act = do
  localDefineInsert (LI x ?lvl a) x
  res <- act
  localDefineDelete x
  pure res

resetIS :: IO () -- HT doesn't export a "clear" function
resetIS = do
  HT.DRef r <- HT.initialize 5 :: IO IdentScope
  d <- P.readMutVar r
  let HT.DRef r = identScope
  P.writeMutVar r d

-- Operator scope
--------------------------------------------------------------------------------


-- TODO


-- Unique ID for top-level entities
--------------------------------------------------------------------------------

uidRef :: RF.Ref Int
uidRef = runIO $ RF.new 0
{-# noinline uidRef #-}

newUid :: IO Int
newUid = do
  i <- RF.read uidRef
  RF.write uidRef (i + 1)
  pure i


-- Benchmarking
--------------------------------------------------------------------------------

-- TODO




--------------------------------------------------------------------------------

reset :: IO ()
reset = do
  ADL.clear metaCxt
  RF.write frozen 0
  resetIS
  RF.write uidRef 0
