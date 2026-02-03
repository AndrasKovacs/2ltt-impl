
{-# OPTIONS --rewriting #-}

module ClosureConv where

--------------------------------------------------------------------------------

open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂)
open import Data.Unit
open import Level
open import Relation.Binary.PropositionalEquality
  renaming (trans to infixr 5 _◼_; sym to infix 5 _⁻¹; cong to ap)
  hiding ([_])
open import Function
{-# BUILTIN REWRITE _≡_ #-}

coe : ∀ {i}{A B : Set i} → A ≡ B → A → B
coe refl x = x

tr : ∀ {i j}{A : Set i}(B : A → Set j){x y : A} → x ≡ y → B x → B y
tr B p b = coe (ap B p) b

Σ≡ : ∀ {i j}{A : Set i}{B : A → Set j}
       {a₀ a₁ : A}(a₂ : a₀ ≡ a₁){b₀ : B a₀}{b₁ : B a₁}(b₂ : tr B a₂ b₀ ≡ b₁) →
  _,_  {i}{j}{A}{B} a₀ b₀ ≡ _,_ a₁ b₁
Σ≡ refl refl = refl

coe-coe : ∀ {i}{A B C : Set i}(p : B ≡ C)(q : A ≡ B){x} → coe p (coe q x) ≡ coe (q ◼ p) x
coe-coe refl refl = refl

coe-UIP : ∀ {i}{A : Set i}(p : A ≡ A){x} → coe p x ≡ x
coe-UIP refl = refl

Eq : ∀ {i}(A : Set i) → A → A → Set i
Eq A x y = x ≡ y

the : ∀ {i}(A : Set i) → A → A
the A x = x

ap₂ : ∀ {i j k}{A : Set i}{B : A → Set j}{C : Set k}
        (f : ∀ a → B a → C)
        {a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
        (b₀ : B a₀)
      → f a₀ b₀ ≡ f a₁ (tr B a₂ b₀)
ap₂ f refl b = refl

postulate
  funext  : ∀ {i j}{A : Set i}{B : A → Set j}{f g : ∀ a → B a}   → (∀ a → f a ≡ g a) → f ≡ g
  funexti : ∀ {i j}{A : Set i}{B : A → Set j}{f g : ∀ {a} → B a} → (∀ a → f {a} ≡ g {a}) → Eq (∀ {a} → B a) f g

-- Syntax of a type theory with an abstract closure type former
--------------------------------------------------------------------------------

postulate
  Scope : Set
  S0    : Scope
  Ty    : Scope → Level → Set
  Tm    : ∀ {s i} → Ty s i → Set
  Top   : ∀ s i → Ty s i
  Tt    : ∀ {s i} → Tm (Top s i)
  Topη  : ∀ {s i}(t : Tm (Top s i)) → t ≡ Tt
  Sg    : ∀ {s i j}(A : Ty s i) → (Tm A → Ty s j) → Ty s (i ⊔ j)
  Pair  : ∀ {s i j A B}(t : Tm A)(u : Tm (B t)) → Tm (Sg {s}{i}{j} A B)
  Fst   : ∀ {s i j A B}(t : Tm (Sg {s}{i}{j} A B)) → Tm A
  Snd   : ∀ {s i j A B}(t : Tm (Sg {s}{i}{j} A B)) → Tm (B (Fst t))
  Fstβ  : ∀ {s i j A B t u} → Fst (Pair {s}{i}{j}{A}{B} t u) ≡ t
{-# REWRITE Fstβ #-}
postulate
  Sndβ  : ∀ {s i j A B t u} → Snd (Pair {s}{i}{j}{A}{B} t u) ≡ u
  Sgη : ∀ {s i j A B t} → Pair {s}{i}{j}{A}{B} (Fst t) (Snd t) ≡ t
{-# REWRITE Sndβ Sgη #-}

postulate
  Cl : ∀ {s i j}(A : Ty s i) → (Tm A → Ty s j) → Ty s (i ⊔ j)

  Lam :
    ∀ {i j k}
      (E : ∀ s → Ty s i)                 -- type of environment
      (A : ∀ s → Tm (E s) → Ty s j)      -- domain
      (B : ∀ s e → Tm (A s e) → Ty s k)  -- codomain
      (t : ∀ s e a → Tm (B s e a))       -- body
      (s : Scope)
      (e : Tm (E s))                     -- capture
    → Tm (Cl (A s e) (B s e))

  App : ∀ {s i j A B}(t : Tm (Cl {s}{i}{j} A B))(u : Tm A) → Tm (B u)
  Clη : ∀ {i j s A B} (t t' : Tm (Cl {s}{i}{j} A B)) → (∀ u → App t u ≡ App t' u) → t ≡ t'
  Clβ : ∀ {i j k E A B s e t u} → App (Lam {i}{j}{k} E A B t s e) u ≡ t s e u
{-# REWRITE Clβ #-}

--------------------------------------------------------------------------------

Pair≡ : ∀ {s i j}{A : Ty s i}{B : Tm A → Ty s j}
          {a₀ a₁ : Tm A}(a₂ : a₀ ≡ a₁)
          {b₀ : Tm (B a₀)}{b₁ : Tm (B a₁)}(b₂ : tr (Tm ∘ B) a₂ b₀ ≡ b₁)
        → Pair {s}{i}{j} a₀ b₀ ≡ Pair a₁ b₁
Pair≡ refl refl = refl

tr-App-lem :
  ∀ {s i j k}{I : Set i}{i₀ i₁ : I}(i₂ : i₀ ≡ i₁)
    {A : I → Ty s j}{B : ∀ i → Tm (A i) → Ty s k}
    (t : Tm (Cl {s}{j}{k} (A i₀) (B i₀)))
    (u : Tm (A i₁))
  → App (tr (λ i → Tm (Cl (A i) (B i))) i₂ t) u
  ≡ coe (ap₂ (λ i x → Tm (B i x)) (i₂ ⁻¹) u ⁻¹) (App t (tr (Tm ∘ A) (i₂ ⁻¹) u))
tr-App-lem refl t u = refl


-- Model of MLTT, implementing closure conversion
--------------------------------------------------------------------------------

record con : Set₁ where
  no-eta-equality
  constructor mkcon
  field
    lvl : Level
    ᵒ   : Scope → Set
    ᶜ   : ∀ s → Ty s lvl
    ↑   : ∀ {s} → Tm (ᶜ s) → ᵒ s
    ↓   : ∀ {s} → ᵒ s → Tm (ᶜ s)
    ↑↓  : ∀ {s} x → ↑ {s} (↓ x) ≡ x
    ↓↑  : ∀ {s} x → ↓ {s} (↑ x) ≡ x
open con public

record ty (Γ : con)(i : Level) : Set where
  constructor mkty
  field
    ᵒ : ∀ {s} → Γ .ᵒ s → Ty s i
open ty public

record tm (Γ : con) {i}(A : ty Γ i) : Set where
  constructor mktm
  field
    ᵒ : ∀ {s} (γ : Γ .ᵒ s) → Tm (A .ᵒ γ)
open tm public

record sub (Γ Δ : con) : Set where
  constructor mksub
  field
   ᵒ : ∀ {s} → Γ .ᵒ s → Δ .ᵒ s
open sub public

∙ : con
∙ .lvl  = zero
∙ .ᵒ  s = ⊤
∙ .ᶜ  s = Top s zero
∙ .↑  _ = tt
∙ .↓  _ = Tt
∙ .↑↓ _ = refl
∙ .↓↑ x = Topη x ⁻¹

infixl 2 _▶_
_▶_ : ∀ (Γ : con){i} → ty Γ i → con
_▶_ Γ {i} A .lvl = Γ .lvl ⊔ i
(Γ ▶ A) .ᵒ s  = Σ  (Γ .ᵒ s) λ γ → Tm (A .ᵒ γ)
(Γ ▶ A) .ᶜ s  = Sg (Γ .ᶜ s) λ γ → A .ᵒ (Γ .↑ γ)
(Γ ▶ A) .↑ x  = (Γ .↑ (Fst x)) , Snd x
(Γ ▶ A) .↓ x  = Pair (Γ .↓ (x .₁)) (tr (Tm ∘ (A .ᵒ) ) (Γ .↑↓ (x .₁) ⁻¹) (x .₂))
(Γ ▶ A) .↑↓ x =
   Σ≡ (Γ .↑↓ (x .₁))
      (coe-coe (ap (Tm ∘ (A .ᵒ)) (Γ .↑↓ (x .₁))) (ap (Tm ∘ (A .ᵒ)) (Γ .↑↓ (x .₁) ⁻¹)) ◼ coe-UIP _)
(Γ ▶ A) .↓↑ {s} x =
  Pair≡ (Γ .↓↑ (Fst x))
        {b₀ = tr (λ x₁ → Tm (A .ᵒ x₁)) (Γ .↑↓ (Γ .↑ (Fst x)) ⁻¹) (Snd x)}
        {b₁ = Snd x}
        (coe-coe (ap (Tm ∘ (A .ᵒ)  ∘ Γ .↑) (Γ .↓↑ (Fst x)))
                 (ap (Tm ∘ (A .ᵒ)) (Γ .↑↓ (Γ .↑ (Fst x)) ⁻¹))
         ◼ coe-UIP _)

ε : ∀ {Γ} → sub Γ ∙
ε {Γ} .ᵒ _ = tt

εη : ∀ {Γ}{σ : sub Γ ∙} → σ ≡ ε
εη = refl

ids : ∀ {Γ} → sub Γ Γ
ids .ᵒ γ = γ

infixr 6 _∘ₛ_
_∘ₛ_ : ∀ {Γ Δ Ξ}(σ : sub Δ Ξ)(γ : sub Γ Δ) → sub Γ Ξ
(σ ∘ₛ δ) .ᵒ γ = σ .ᵒ (δ .ᵒ γ)

idl : ∀ {Γ Δ}{σ : sub Γ Δ} →  σ ∘ₛ ids ≡ σ
idl = refl

idr : ∀ {Γ Δ}{σ : sub Γ Δ} → ids ∘ₛ σ ≡ σ
idr = refl

ass : ∀ {Γ Δ Ξ θ}{σ : sub Ξ θ}{δ : sub Δ Ξ}{ν : sub Γ Δ} → σ ∘ₛ (δ ∘ₛ ν) ≡ (σ ∘ₛ δ) ∘ₛ ν
ass = refl

infixl 6 _[_]T
_[_]T : ∀ {Γ Δ i} → ty Δ i → sub Γ Δ → ty Γ i
(A [ σ ]T) .ᵒ γ = A .ᵒ (σ .ᵒ γ)

infixl 6 _[_]
_[_] : ∀ {Γ Δ i A} → tm Δ {i} A → (σ : sub Γ Δ) → tm Γ (A [ σ ]T)
_[_] t σ .ᵒ γ = t .ᵒ (σ .ᵒ γ)

[ids]T : ∀ {Γ i}{A : ty Γ i} → A [ ids ]T ≡ A
[ids]T = refl

[∘ₛ]T : ∀ {i Γ Δ Ξ}{A : ty Ξ i}{σ : sub Δ Ξ}{δ : sub Γ Δ}
        → A [ σ ∘ₛ δ ]T ≡ A [ σ ]T [ δ ]T
[∘ₛ]T = refl

p : ∀ {Γ i}(A : ty Γ i) → sub (Γ ▶ A) Γ
p  A .ᵒ (γ , α) = γ

q : ∀ {Γ i}(A : ty Γ i) → tm (Γ ▶ A) (A [ p A ]T)
q A .ᵒ (γ , α) = α

infixl 5 _,ₛ_
_,ₛ_ : ∀ {Γ Δ}(σ : sub Γ Δ){i}{A : ty Δ i}(t : tm Γ (A [ σ ]T)) → sub Γ (Δ ▶ A)
_,ₛ_ σ t .ᵒ γ = σ .ᵒ γ , t .ᵒ γ

p-∘ₛ : ∀ {Γ Δ}{σ : sub Γ Δ}{i}{A : ty Δ i}{t : tm Γ (A [ σ ]T)} → p A ∘ₛ (σ ,ₛ t) ≡ σ
p-∘ₛ = refl

q-[] : ∀ {Γ Δ}{σ : sub Γ Δ}{i}{A : ty Δ i}{t : tm Γ (A [ σ ]T)} → q A [ σ ,ₛ t ] ≡ t
q-[] = refl

,ₛη  : ∀ {Γ i}{A : ty Γ i} → p A ,ₛ q A ≡ ids
,ₛη = refl

,ₛ-∘ₛ : ∀ {Γ Δ Ξ i}{A : ty Ξ i}{σ : sub Γ Δ}{δ : sub Δ Ξ}{t : tm Δ (A [ δ ]T)}
        → Eq (sub Γ (Ξ ▶ A)) ((δ ,ₛ t) ∘ₛ σ) (δ ∘ₛ σ ,ₛ t [ σ ])
,ₛ-∘ₛ = refl

Π : ∀ {Γ i j}(A : ty Γ i) → ty (Γ ▶ A) j → ty Γ (i ⊔ j)
Π {Γ}{i}{j} A B .ᵒ {s} γ = Cl {s}{i}{j} (A .ᵒ γ) (λ α → B .ᵒ (γ , α))

Π[] : ∀ {Γ Δ}{σ : sub Γ Δ}{i j}{A : ty Δ i}{B : ty (Δ ▶ A) j}
    → Π A B [ σ ]T ≡ Π (A [ σ ]T) (B [ σ ∘ₛ p _ ,ₛ q _ ]T)
Π[] = refl

lam : ∀ {Γ i j}{A : ty Γ i}{B : ty (Γ ▶ A) j}(t : tm (Γ ▶ A) B) → tm Γ (Π A B)
lam {Γ} {i} {j} {A} {B} t .ᵒ {s} γ =
  tr (λ x → Tm (Cl (A .ᵒ x) (λ α → B .ᵒ (x , α))))
     (Γ .↑↓ γ)
     (Lam {lvl Γ}
          {i}
          {j}
          (λ s     → Γ .ᶜ s)
          (λ s e   → A .ᵒ (Γ .↑ e))
          (λ s e α → B .ᵒ (Γ .↑ e , α))
          (λ s e α → t .ᵒ (Γ .↑ e , α))
          s
          (Γ .↓ γ))

app : ∀ {Γ i j}{A : ty Γ i}{B : ty (Γ ▶ A) j}(t : tm Γ (Π A B)) → tm (Γ ▶ A) B
app t .ᵒ (γ , α) = App (t .ᵒ γ) α

app[] :
  ∀ {Δ Γ}{σ : sub Δ Γ}{i j}{A : ty Γ i}{B : ty (Γ ▶ A) j}{t : tm Γ (Π A B)}
  → Eq (tm (Δ ▶ A [ σ ]T) (B [ σ ∘ₛ p _ ,ₛ q _ ]T))
       (app t [ σ ∘ₛ p _ ,ₛ q _ ])
       (app (t [ σ ]))
app[] = refl

Πη :
  ∀ {Γ i j A B}{t : tm Γ (Π {Γ}{i}{j} A B)} → lam (app t) ≡ t
Πη {Γ} {i} {j} {A} {B} {t} =
  ap mktm (
    funexti λ s → funext λ γ →
      Clη _ _ λ u →
        tr-App-lem ((Γ .↑↓ γ)) (Lam (Γ .ᶜ) (λ s₁ e → A .ᵒ (Γ .↑ e)) (λ s₁ e α → B .ᵒ (Γ .↑ e , α))
                                  (λ s₁ e α → App (t .ᵒ (Γ .↑ e)) α) s (Γ .↓ γ)) u
      ◼ J (λ γ' eq → coe (ap₂ (λ i₁ x → Tm (B .ᵒ (i₁ , x))) eq u ⁻¹)
               (App (t .ᵒ γ')
                (coe (ap (Tm ∘ (λ v → A .ᵒ v)) eq) u))
               ≡ App (t .ᵒ γ) u)
           (Γ .↑↓ γ ⁻¹)
           refl
  )

Πβ : ∀ {Γ i j A B}{t : tm (Γ ▶ A) B} → app {Γ}{i}{j}{A}{B} (lam t) ≡ t
Πβ {Γ} {i} {j} {A} {B} {t} =
  ap mktm (funexti λ s → funext λ {(γ , α) →
       tr-App-lem (Γ .↑↓ γ)
                  (Lam (Γ .ᶜ) (λ s₁ e → A .ᵒ (Γ .↑ e))
                   (λ s₁ e α₁ → B .ᵒ (Γ .↑ e , α₁)) (λ s₁ e α₁ → t .ᵒ (Γ .↑ e , α₁)) s
                   (Γ .↓ γ)) α
    ◼ J
       (λ γ' eq →
          coe (ap₂ (λ i₁ x → Tm (B .ᵒ (i₁ , x))) eq α ⁻¹)
          (t .ᵒ (γ' , coe (ap (λ x → Tm (A .ᵒ x)) eq) α))
          ≡ t .ᵒ (γ , α))
       (Γ .↑↓ γ ⁻¹)
       refl
  })


--------------------------------------------------------------------------------
