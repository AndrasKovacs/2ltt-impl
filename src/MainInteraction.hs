
module MainInteraction where

import Common
import Elaboration.State
import Elaboration
import Errors
import Parser
import Core.Syntax qualified as S
import Core.Value
import Pretty

-- | Elaborate a string, render output.
justElab :: String -> IO ()
justElab (strToUtf8 -> s) = do
  reset
  top <- parse s
  putStrLn "PARSING"
  putStrLn $ replicate 60 '-'
  print top
  let sp = byteStringToSpan s
  let ?lvl    = 0
      ?env    = ENil
      ?locals = S.LNil
      ?src    = SrcNoFile s
      ?span   = LazySpan sp
  top <- elab top
  renderElab top

renderElab :: Top -> IO ()
renderElab top = do
  putStrLn "\n"
  putStrLn "ELABORATION"
  putStrLn $ replicate 60 '-'

  let go :: Top -> MetaVar -> IO ()
      go top metaBlock = case top of
        TNil -> pure ()
        TDef1 (TopDef info) endBlock top -> do

          let goMetas :: MetaVar -> IO ()
              goMetas m | m == endBlock = pure ()
              goMetas m = do
                case lookupMeta m of
                  MEUnsolved e -> do
                    let ?locals = e^.locals
                    putStrLn $ show m ++ " : " ++ prettyTop (e^.locals)
                               ++ " → " ++ pretty (e^.ty)
                  MESolved e -> do
                    let ?locals = e^.locals
                    putStrLn $ show m ++ " : " ++ prettyTop (e^.locals)
                               ++ " → " ++ pretty (e^.ty)
                               ++ " = " ++ pretty (e^.solution)
                  MESolved0{} -> impossible
                goMetas (m + 1)

          goMetas metaBlock
          putStrLn $ show (info^.name) ++ " : " ++ prettyTop (info^.ty) ++ "\n  = "
                     ++ prettyTop (info^.body) ++ "\n"
          go top endBlock

  -- print top
  go top 0

p1 :: String
p1 =
  """
  Nat : Set = (N : Set) → (N → N) → N → N

  """
