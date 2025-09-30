
module Elaboration.State where

import qualified Data.Array.Dynamic.L as ADL
import qualified Data.Ref.F as RF
import qualified Data.Ref.L as RL
import qualified Data.Vector.Mutable as VM
import qualified Data.Vector.Hashtables as HT
import qualified Data.Primitive.MutVar as P
import qualified Data.ByteString as B

import Common
import Core (Tm, Ty, Locals, LocalsArg)
import qualified Core as C
import Value (Val, VTy)
-- import qualified Value as V

-- Metacontext
--------------------------------------------------------------------------------

data Unsolved = Unsolved {
    unsolvedTy     :: Ty
  , unsolvedLocals :: Locals
  }
makeFields ''Unsolved

data Solved = Solved {
    solvedOccursCache :: RF.Ref MetaVar
  , solvedLocals      :: C.Locals
  , solvedSolution    :: Tm
  , solvedSolutionVal :: Val
  , solvedTy          :: VTy
  , solvedIsInline    :: Bool
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
  ADL.push metaCxt (MEUnsolved (Unsolved a ?locals))
  pure (coerce s)
{-# inline newMeta #-}

-- | Trim the size of the metacontext to `Lvl`.
resetMetaCxt :: MetaVar -> IO ()
resetMetaCxt size = do
  currSize <- nextMeta
  if size < currSize then ADL.pop metaCxt >> resetMetaCxt size
                     else pure ()

-- Identifier scope
--------------------------------------------------------------------------------

data LocalInfo = LI {
  localInfoName :: Name
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
  HT.Dictionary (HT.PrimState IO) VM.MVector B.ByteString VM.MVector ISEntry

identScope :: IdentScope
identScope = runIO $ HT.initialize 5
{-# noinline identScope #-}

resetIS :: IO () -- HT doesn't export a "clear" function
resetIS = do
  HT.DRef r <- HT.initialize 5 :: IO IdentScope
  d <- P.readMutVar r
  let HT.DRef r = identScope
  P.writeMutVar r d

-- Operator scope
--------------------------------------------------------------------------------


-- TODO



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


-- Source of code being elaborated
--------------------------------------------------------------------------------

elabSource :: RL.Ref (Maybe Src)
elabSource = runIO $ RL.new Nothing
{-# noinline elabSource #-}

readElabSource :: IO (Maybe Src)
readElabSource = RL.read elabSource

writeElabSource :: Maybe Src -> IO ()
writeElabSource msrc = RL.write elabSource msrc

-- Benchmarking
--------------------------------------------------------------------------------

-- TODO


--------------------------------------------------------------------------------

reset :: IO ()
reset = do
  ADL.clear metaCxt
  RF.write frozen 0
  resetIS
  writeElabSource Nothing
