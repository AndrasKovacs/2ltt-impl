
module Elaboration.State where

import Data.Array.Dynamic.L        qualified as ADL
import Data.Ref.F                  qualified as RF
import Data.Vector.Mutable         qualified as VM
import Data.Vector.Hashtables      qualified as HT
import Data.Primitive.MutVar       qualified as P
import Data.IntSet                 qualified as IS

import Common
import Core.Syntax (Tm, Ty, Locals, LocalsArg, Tm0)
import Core.Value (VTy, EnvArg, GTy)
import Core.Info
import Presyntax qualified as P

-- Metacontext
--------------------------------------------------------------------------------

data Unsolved = Unsolved {
    unsolvedLocals   :: Locals
  , unsolvedTy       :: Ty       -- the type is under the Locals
  , unsolvedBlocking :: IS.IntSet
  }
makeFields ''Unsolved

-- TODO: optimize closed solutions by using call-by-need instead of call-by-name?
data Solved = Solved {
    solvedLocals      :: Locals
  , solvedTy          :: Ty
  , solvedSolution    :: Tm     -- the type and solution are under the Locals
  , solvedIsInline    :: Bool   -- should we immediately unfold the meta
  , solvedOccursCache :: RF.Ref MetaVar -- mutable cache for approximate occurs checking
                                        -- we initialize it to (-1). It holds the last meta
                                        -- that we succefully checked for *not occurring*
                                        -- in the solution
  }
makeFields ''Solved

data Solved0 = Solved0 {
    solved0Locals      :: Locals
  , solved0Ty          :: Ty
  , solved0Solution    :: Tm0             -- the type and solution are under the Locals
  , solved0IsInline    :: Bool            -- should we immediately unfold the meta
  , solved0OccursCache :: RF.Ref MetaVar
  }
makeFields ''Solved0

data MetaEntry = MEUnsolved Unsolved | MESolved Solved | MESolved0 Solved0

type MetaCxt = ADL.Array MetaEntry

{-# noinline metaCxt #-}
metaCxt :: MetaCxt
metaCxt = runIO ADL.empty

nextMeta :: IO MetaVar
nextMeta = coerce <$!> ADL.size metaCxt

{-# inline readMeta #-}
readMeta :: MetaVar -> IO MetaEntry
readMeta (MkMetaVar i) = ADL.read metaCxt i

{-# inline lookupMeta #-}
lookupMeta :: MetaVar -> MetaEntry
lookupMeta (MkMetaVar i) = runIO (ADL.read metaCxt i)

{-# inline lookupUnsolved #-}
lookupUnsolved :: MetaVar -> IO Unsolved
lookupUnsolved m = ADL.read metaCxt (coerce m) >>= \case
  MEUnsolved e -> pure e
  _            -> impossible

{-# inline writeMeta #-}
writeMeta :: MetaVar -> MetaEntry -> IO ()
writeMeta (MkMetaVar i) e = ADL.write metaCxt i e

newSolution :: MetaVar -> Locals -> Ty -> Tm -> IO ()
newSolution m ls a sol = do
  occCache <- RF.new (-1)
  writeMeta m $ MESolved $ Solved ls a sol False occCache -- TODO: inlining

{-# inline newMeta #-}
newMeta :: LocalsArg => Ty -> IO MetaVar
newMeta a = do
  s <- ADL.size metaCxt
  debug ["NEWMETA", show s]
  ADL.push metaCxt (MEUnsolved (Unsolved ?locals a mempty))
  pure (coerce s)

-- | Trim the size of the metacontext to `Lvl`.
resetMetaCxt :: MetaVar -> IO ()
resetMetaCxt size = do
  currSize <- nextMeta
  if size < currSize then ADL.pop metaCxt >> resetMetaCxt size
                     else pure ()

-- Postponed problems
--------------------------------------------------------------------------------

type ProblemId = Int

data Problem where
  PCheckTm ::
       (LvlArg, EnvArg, LocalsArg, SrcArg, LazySpanArg)
    => P.Tm -> GTy -> MetaVar -> Problem
    -- term, type, placeholder meta applied to Env
  PSolved :: Problem

type Problems = ADL.Array Problem

{-# noinline problems #-}
problems :: Problems
problems = runIO $ ADL.empty

newProblem :: Problem -> IO ProblemId
newProblem p = do
  i <- ADL.size problems
  ADL.push problems p
  pure i

lookupProblem :: ProblemId -> IO Problem
lookupProblem = ADL.read problems

newlyBlocked :: MetaVar -> ProblemId -> IO ()
newlyBlocked m p = do
  e <- lookupUnsolved m
  ADL.write metaCxt (coerce m) $ MEUnsolved $ e & blocking %~ IS.insert p

problemSolved :: ProblemId -> IO ()
problemSolved i = ADL.write problems i PSolved

-- Frozen metas
--------------------------------------------------------------------------------

{-# noinline frozen #-}
frozen :: RF.Ref MetaVar
frozen = runIO $ RF.new 0

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

-- TODO: pre-allocate the value
data LocalInfo = LI {
    localInfoLvl :: Lvl
  , localInfoTy  :: ~VTy
  }
makeFields ''LocalInfo

data ISEntry
  = ISTopDef     {-# nounpack #-} DefInfo
  | ISTopRecTCon {-# nounpack #-} RecInfo
  | ISTopRecDCon {-# nounpack #-} RecInfo
  | ISTopTCon    {-# nounpack #-} TConInfo
  | ISTopDef0    {-# nounpack #-} Def0Info
  | ISTopRec0    {-# nounpack #-} Rec0Info
  | ISTopTCon0   {-# nounpack #-} TCon0Info
  | ISTopDCon (List DConInfo)
  | ISLocal LocalInfo
  | ISShadowedLocal LocalInfo ISEntry


type IdentScope =
  HT.Dictionary (HT.PrimState IO) VM.MVector Name VM.MVector ISEntry

identScope :: IdentScope
identScope = runIO $ HT.initialize 5
{-# noinline identScope #-}

lookupIS :: Name -> IO (Maybe ISEntry)
lookupIS = HT.lookup identScope

{-# noinline localDefineInsert #-}
localDefineInsert :: LocalInfo -> Name -> IO ()
localDefineInsert i x =
  HT.upsert identScope (maybe (ISLocal i) (ISShadowedLocal i)) x

{-# noinline localDefineDelete #-}
localDefineDelete :: Name -> IO ()
localDefineDelete x = HT.alter identScope go x where
  go (Just (ISShadowedLocal _ e)) = Just e
  go (Just ISLocal{})             = Nothing
  go _                            = impossible

-- | Note: we already extended the cxt, top var is (?lvl - 1).
{-# inline localDefineIS #-}
localDefineIS :: LvlArg => Name -> VTy -> IO a -> IO a
localDefineIS x a act = do
  localDefineInsert (LI (?lvl - 1) a) x
  res <- act
  localDefineDelete x
  pure res

-- | Precondition: no shadowing.
topDefineIS :: DefInfo -> IO ()
topDefineIS inf = HT.insert identScope (inf^.name) (ISTopDef inf)

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

{-# noinline uidRef #-}
uidRef :: RF.Ref Int
uidRef = runIO $ RF.new 0

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
  ADL.clear problems
  RF.write frozen 0
  resetIS
  RF.write uidRef 0
