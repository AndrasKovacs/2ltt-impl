module Utils where

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Level using (Level; _⊔_; suc)
open import Data.Product
open import Agda.Builtin.Sigma
open import Data.Empty renaming (⊥ to Empty)

-- Acknowledgements to Szumi Xie for many proof irrelevant equality utilities:
-- https://github.com/szumixie/single-subst/blob/main/TT/Lib.agda

private variable
  ℓ ℓ' : Level
  A A' : Set ℓ
  P P' : Prop
  B B' : A → Set ℓ
  C : P → Set ℓ
  x y z : A

-- Prop primitives

data ⊤ : Prop where
    tt : ⊤

data ⊥ : Prop where

exfalso : ⊥ → A
exfalso ()

exfalso-prop : ∀ {P : Prop ℓ} → ⊥ → P
exfalso-prop ()

exfalso-empty-prop : Empty → P
exfalso-empty-prop ()

infix 4 _≡_
data _≡_ {A : Set ℓ} (x : A) : A → Prop ℓ where
  instance refl : x ≡ x

infix 4 _＝_
data _＝_ {P : Prop ℓ} (x : P) : P → Prop ℓ where
  instance reflP : x ＝ x

{-# BUILTIN REWRITE _≡_ #-}

private variable
  p q : A ≡ A'

record _≃_ (A : Set ℓ) (B : Set ℓ) : Set ℓ where
  field
    to : A → B
    from : B → A
    to-from : ∀ x → to (from x) ≡ x
    from-to : ∀ x → from (to x) ≡ x

open _≃_ public

record _true (A : Prop ℓ) : Set ℓ where
  constructor by
  field
    witness : A

open _true public

record ΣProp {ℓ ℓ'} (A : Prop ℓ) (B : A → Prop ℓ') : Prop (ℓ ⊔ ℓ') where
  constructor _,P_
  field
    fst : A
    snd : B fst

open ΣProp public

data ∃P (A : Set) (B : A → Prop) : Prop where
  _,∃_ : (a : A) → B a → ∃P A B

∃P-elim : ∀ {A : Set} {B : A → Prop} {P : Prop} → ((a : A) → B a → P) → ∃P A B → P
∃P-elim f (a ,∃ b) = f a b

-- Some fragment of OTT

postulate
  coe₀ : A ≡ A' → A → A'
  funext : ∀ {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g
  propfunext : ∀ {f g : (x : P) → C x} → (∀ x → f x ≡ g x) → f ≡ g
  propext : ∀ {ℓ} {P Q : Prop ℓ} → (P → Q) → (Q → P) → _≡_ {A = Prop ℓ} P Q

opaque
  coe : A ≡ A' → A → A'
  coe = coe₀


cong : (f : A → A') → x ≡ y → f x ≡ f y
cong f refl = refl

ifunext : {f g : {x : A} → B x}
        → (∀ x → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ (λ {x} → g {x})
ifunext h = cong (λ k {x} → k x) (funext h)

cong₂ : ∀ {B C : Set ℓ} {z w : B} → (f : A → B → C) → x ≡ y → z ≡ w → f x z ≡ f y w
cong₂ f refl refl = refl

sym : x ≡ y → y ≡ x
sym refl = refl

trans : x ≡ y → y ≡ z → x ≡ z
trans refl p = p

private
  Π : (A : Set ℓ) → (B : A → Set ℓ') → Set (ℓ ⊔ ℓ')
  Π A B = (a : A) → B a

-- We don't add computation rules for the equality type---since it is inductively
-- defined that would break things.
postulate
  coe-Σ : (Σ A B ≡ Σ A' B') → (ΣProp (A ≡ A') (λ p → ∀ x → B x ≡ B' (coe p x)))
  coe-pair :
    {a : A} {b : B a}
    {p : Σ A B ≡ Σ A' B'}
    → coe₀ p (a , b) ≡ (coe (coe-Σ p .fst) a , coe (coe-Σ p .snd a) b)
  {-# REWRITE coe-pair #-}

  coe-Π : (((a : A) → B a) ≡ ((a : A') → B' a))
    → (ΣProp (A' ≡ A) (λ p → ∀ x → B (coe p x) ≡ B' x))
  coe-lam : 
    {f : Π {ℓ} {ℓ'} A B}
    {p : ((a : A) → B a) ≡ ((a : A') → B' a)}
    → coe₀ p f ≡ λ a → coe (coe-Π p .snd _) (f (coe (coe-Π p .fst) a))
  {-# REWRITE coe-lam #-}

-- Adding this as the last rule because it's the most general. Otherwise
-- the typechecker dies
postulate
  coe₀-eq : coe₀ refl x ≡ x
  {-# REWRITE coe₀-eq #-}

-- Equality helpers

subst : (P : A → Set ℓ) (p : x ≡ y) → P x → P y
subst P p a = coe (cong P p) a

substP : (P : A → Prop ℓ) (p : x ≡ y) → P x → P y
substP P refl a = a

coeP : ∀ {ℓ} {P Q : Prop ℓ} → _≡_ {A = Prop ℓ} P Q → P → Q
coeP refl a = a

infix 4 _≡[_]_

_≡[_]_ : ∀ (a : A) (p : A ≡ A') (b : A') → Prop _
_≡[_]_ a p b = coe p a ≡ b

opaque
  unfolding coe

  Σ≡ : {p₁ p₂ : Σ A B} (p : p₁ .proj₁ ≡ p₂ .proj₁) → subst B p (p₁ .proj₂) ≡ (p₂ .proj₂) → p₁ ≡ p₂
  Σ≡ refl refl = refl

  ≡Σ : {p₁ p₂ : Σ A B} (p : p₁ ≡ p₂)
    → ΣProp (p₁ .proj₁ ≡ p₂ .proj₁) (λ p → subst B p (p₁ .proj₂) ≡ (p₂ .proj₂))
  ≡Σ refl = refl ,P refl

  reflᴰ : x ≡[ refl ] x
  reflᴰ = refl

  symᴰ : x ≡[ p ] y → y ≡[ sym p ] x
  symᴰ {p = refl} refl = refl

  transᴰ : x ≡[ p ] y → y ≡[ q ] z → x ≡[ trans p q ] z
  transᴰ {p = refl} {q = refl} refl m = m

  congᴰ : (B : A → Set ℓ) → (f : (a : A) → B a) → (p : x ≡ y) → f x ≡[ cong B p ] f y
  congᴰ _ _ refl = refl

  dep : x ≡ y → x ≡[ refl ] y
  dep p = p

  undep : x ≡[ refl ] y → x ≡ y
  undep p = p

  movel : x ≡ coe (sym q) y → x ≡[ q ] y
  movel {q = refl} refl = refl

  splitl : x ≡[ trans p q ] y → coe p x ≡[ q ] y
  splitl {p = refl} q = q

  splitr : x ≡[ trans p (sym q) ] y → x ≡[ p ] coe q y
  splitr {p = refl} {q = refl} refl = refl

  merger : x ≡[ p ] coe q y → x ≡[ trans p (sym q) ] y
  merger {p = refl} {q = refl} refl = refl


opaque
  unfolding coe

  ap-→ : ∀ {C C' : Set ℓ} → A ≡ A' → C ≡ C' → (A → C) ≡ (A' → C')
  ap-→ refl refl = refl

  ap-$ : ∀ {f g : (x : A) → B x} → f ≡ g → ∀ x → f x ≡ g x
  ap-$ refl x = refl
