
module MainInteraction where

import Common
import Elaboration.State
import Elaboration
-- import Errors
import Parser
import Core.Syntax qualified as S
import Core.Value
import Pretty

-- | Elaborate a string, render output.
justElab :: String -> IO ()
justElab (strToUtf8 -> s) = do
  reset
  top <- parse s
  -- putStrLn "PARSING"
  -- putStrLn $ replicate 60 '-'
  -- print top
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
  putStrLn "\nELABORATION"
  putStrLn $ replicate 60 '-'

  let goMetaTy :: S.LocalsArg => S.Ty -> String
      goMetaTy a = case ?locals of
        S.LNil -> ": " ++ pretty a
        _      -> prettyTop ?locals ++ " : " ++ pretty a

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
                    putStrLn $ show m ++ " " ++ goMetaTy (e^.ty)
                  MESolved e -> do
                    let ?locals = e^.locals
                    putStrLn $ show m ++ " " ++ goMetaTy (e^.ty)
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
  -- Type : Set = Set

  -- id : {A : Type} → A → A
  --   = λ {A} x. x

  Eq : (A : Set) → A → A → Set
    = λ A x y. (P : A → Set) → P x → P y

  Refl : {A : Set}(a : A) → Eq A a a
    = λ a P pa. pa

  -- Nat : Set = (N : Set) → (N → N) → N → N
  -- zero : Nat = λ N s z. z

  -- test : Eq Nat zero zero
  --   = Refl zero

  localTest1 : Set
    =
      let m   : Set = _;
      let foo : Set = x;
      let p   : Eq Set m foo = Refl foo;
      Set

  """
