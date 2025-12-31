
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
  putStrLn $ runTxt (renderElab top)

renderElab :: Top -> Txt
renderElab top =

  let prtLocals :: S.LocalsArg => Pretty a => a -> Txt
      prtLocals a =
        let ?names = S.localsToNames ?locals
            ?prec = letPrec in
        prt a in

  let goMetaTy :: S.LocalsArg => S.Ty -> Txt
      goMetaTy a = case ?locals of
        S.LNil -> ": " <> prtLocals a
        _      -> prtTop ?locals <> " : " <> prtLocals a in

  let go :: Top -> MetaVar -> Txt
      go top metaBlock = case top of
        TNil -> mempty
        TDef1 (TopDef info) endBlock top ->

          let goMetas :: MetaVar -> Txt
              goMetas m | m == endBlock = mempty
              goMetas m =
                (case lookupMeta m of
                  MEUnsolved e ->
                    let ?locals = e^.locals in
                    str (show m) <> " " <> goMetaTy (e^.ty) <> newl
                  MESolved e ->
                    let ?locals = e^.locals in
                    str (show m) <> " " <> goMetaTy (e^.ty)
                               <> " = " <> prtLocals (e^.solution) <> newl
                  MESolved0{} -> impossible)
                <> goMetas (m + 1) in

          goMetas metaBlock <>

          str (show (info^.name)) <> " : " <> prtTop (info^.ty) <>
              " =" <> indent 2 (newl <> prtTop (info^.body)) <> newl <> newl <>

          go top endBlock in

  newl <>
  "ELABORATION" <> newl <>
  str (replicate 60 '-') <> newl <> newl <>
  go top 0



  -- -- print top
  -- go top 0

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

  -- localTest1 : Set
  --   =
  --     let foo : Set = Set;
  --     let m   : Set = _;
  --     let p   : Eq Set m foo = Refl {Set} foo;
  --     Set

  -- unifyTest1 : Set
  --   = let m : Set → Set = _;
  --     let p : (A : Set) → Eq Set (m A) A = λ A. Refl {Set} A;
  --     Set

  unifyTest2 : Set
    = let m : Set → Set = λ x. x;
      let p : (A : Set) → Eq Set (m A) A = λ A. Refl {_} A;
      Set


  """
