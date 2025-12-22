
module MainInteraction where

import FlatParse.Stateful qualified as FP

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
justElab s = do
  reset
  top <- parseString s
  let ?lvl    = 0
      ?env    = ENil
      ?locals = S.LNil
      ?src    = SrcNoFile (FP.strToUtf8 s)
      ?span   = LazySpan impossible
  renderElab =<< elab top

renderElab :: Top -> IO ()
renderElab top = do
  putStr "\n"
  let go :: Top -> MetaVar -> IO ()
      go top metaBlock = case top of
        TNil -> pure ()
        TDef1 info endBlock top -> do

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
          putStrLn $ show (info^.name) ++ " : " ++ prettyTop (info^.ty) ++ "\n"
                     ++ prettyTop (info^.body)
          go top endBlock
  go top 0
