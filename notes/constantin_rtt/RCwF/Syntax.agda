{-# OPTIONS --type-in-type #-}
module RCwF.Syntax where

open import Utils
open import Data.Unit renaming (⊤ to 𝟙)
open import Semiring
import RCwF.Model
import RCwF.DisplayedModel

-- Syntax

module Over {D : SemiringBase} {S : InSemiringBase.SemiringAxioms D} where
  open InSemiringBase D
  open SemiringAxioms S
  open RCwF.Model.Over S
  open RCwF.DisplayedModel.Over S

  postulate
    syn : Total

  open Total syn public
  open InBaseSorts sorts
  open InResSorts base rsorts

  -- Injectivity for syntax sorts

  postulate
    Sub-inj₀ : Sub Γ Δ ≡ Sub Γ' Δ' → Γ ≡ Γ'
    Sub-inj₁ : Sub Γ Δ ≡ Sub Γ' Δ' → Δ ≡ Δ'
    Ty-inj   : Ty Γ ≡ Ty Γ' → Γ ≡ Γ'
    Tm-injᶜ  : Tm Γ A ≡ Tm Γ' A' → Γ ≡ Γ'
    Tm-injᵀ  : (e : Tm Γ A ≡ Tm Γ' A') → A ≡[ cong Ty (Tm-injᶜ e) ] A'
    Conᴿ-inj : Conᴿ Γ ≡ Conᴿ Γ' → Γ ≡ Γ'

  -- Eliminator

  module Elim (methods : Totalᴰ syn) where
    open Totalᴰ methods
    open InBaseSortsᴰ base sortsᴰ
    open InResSortsᴰ base sortsᴰ baseᴰ rsorts resourced rsortsᴰ

    variable
      Γᴰ' : Conᴰ Γ'
      Δᴰ' : Conᴰ Δ'
      Aᴰ' : Tyᴰ Γᴰ' A'
      Γᴿ' : Conᴿ Γ'

    postulate
      ⟦_⟧ᶜ : (Γ : Con) → Conᴰ Γ
      ⟦_⟧ˢ : (σ : Sub Γ Δ) → Subᴰ ⟦ Γ ⟧ᶜ ⟦ Δ ⟧ᶜ σ
      ⟦_⟧ᵀ : (A : Ty Γ) → Tyᴰ ⟦ Γ ⟧ᶜ A
      ⟦_⟧ᵗ : (a : Tm Γ A) → Tmᴰ ⟦ Γ ⟧ᶜ ⟦ A ⟧ᵀ a
      ⟦_⟧ᴿ  : (Γᴿ : Conᴿ Γ) → Conᴿᴰ ⟦ Γ ⟧ᶜ Γᴿ
      ⟦_⟧ˢᴿ : (σᴿ : Subᴿ Γᴿ Δᴿ σ) → Subᴿᴰ ⟦ Γᴿ ⟧ᴿ ⟦ Δᴿ ⟧ᴿ ⟦ σ ⟧ˢ σᴿ
      ⟦_⟧ᵗᴿ : (aᴿ : Tmᴿ Γᴿ μ A a) → Tmᴿᴰ ⟦ Γᴿ ⟧ᴿ ⟦ a ⟧ᵗ aᴿ

    -- ap helpers for displayed sorts with varying base context

    opaque
      unfolding coe

      ap-Conᴰᶜ : Γ ≡ Γ' → Conᴰ Γ ≡ Conᴰ Γ'
      ap-Conᴰᶜ refl = refl

      ap-Subᴰᶜ : (pΓ : Γ ≡ Γ') → (pΔ : Δ ≡ Δ')
        → Γᴰ ≡[ ap-Conᴰᶜ pΓ ] Γᴰ'
        → Δᴰ ≡[ ap-Conᴰᶜ pΔ ] Δᴰ'
        → σ ≡[ ap-Sub pΓ pΔ ] σ'
        → Subᴰ Γᴰ Δᴰ σ ≡ Subᴰ Γᴰ' Δᴰ' σ'
      ap-Subᴰᶜ refl refl refl refl refl = refl

      ap-Tyᴰᶜ : (pΓ : Γ ≡ Γ')
        → Γᴰ ≡[ ap-Conᴰᶜ pΓ ] Γᴰ'
        → A ≡[ ap-Ty pΓ ] A'
        → Tyᴰ Γᴰ A ≡ Tyᴰ Γᴰ' A'
      ap-Tyᴰᶜ refl refl refl = refl

      ap-Tmᴰᶜ : (pΓ : Γ ≡ Γ') → (pA : A ≡[ ap-Ty pΓ ] A')
        → (pΓᴰ : Γᴰ ≡[ ap-Conᴰᶜ pΓ ] Γᴰ')
        → Aᴰ ≡[ ap-Tyᴰᶜ pΓ pΓᴰ pA ] Aᴰ'
        → a ≡[ ap-Tmᶜ pΓ pA ] a'
        → Tmᴰ Γᴰ Aᴰ a ≡ Tmᴰ Γᴰ' Aᴰ' a'
      ap-Tmᴰᶜ refl refl refl refl refl = refl

      ap-Conᴿᴰᶜ : (pΓ : Γ ≡ Γ')
        → Γᴰ ≡[ ap-Conᴰᶜ pΓ ] Γᴰ'
        → Γᴿ ≡[ ap-Conᴿ pΓ ] Γᴿ'
        → Conᴿᴰ Γᴰ Γᴿ ≡ Conᴿᴰ Γᴰ' Γᴿ'
      ap-Conᴿᴰᶜ refl refl refl = refl

    -- ap helpers for ⟦⟧

    opaque
      unfolding coe

      ap-⟦⟧ᶜ : (e : Γ ≡ Γ') → ⟦ Γ ⟧ᶜ ≡[ ap-Conᴰᶜ e ] ⟦ Γ' ⟧ᶜ
      ap-⟦⟧ᶜ refl = refl

      ap-⟦⟧ᵀ : (eΓ : Γ ≡ Γ') → (eA : A ≡[ ap-Ty eΓ ] A')
        → ⟦ A ⟧ᵀ ≡[ ap-Tyᴰᶜ eΓ (ap-⟦⟧ᶜ eΓ) eA ] ⟦ A' ⟧ᵀ
      ap-⟦⟧ᵀ refl refl = refl

    -- ⟦coe⟧ rules

    postulate
      ⟦coe⟧ˢ : (p : Sub Γ Δ ≡ Sub Γ' Δ')
        → ⟦ coe p σ ⟧ˢ
          ≡ coe (ap-Subᴰᶜ (Sub-inj₀ p) (Sub-inj₁ p)
                   (ap-⟦⟧ᶜ (Sub-inj₀ p)) (ap-⟦⟧ᶜ (Sub-inj₁ p)) refl) ⟦ σ ⟧ˢ
      {-# REWRITE ⟦coe⟧ˢ #-}

      ⟦coe⟧ᵀ : (p : Ty Γ ≡ Ty Γ')
        → ⟦ coe p A ⟧ᵀ
          ≡ coe (ap-Tyᴰᶜ (Ty-inj p) (ap-⟦⟧ᶜ (Ty-inj p)) refl) ⟦ A ⟧ᵀ
      {-# REWRITE ⟦coe⟧ᵀ #-}

      ⟦coe⟧ᵗ : (p : Tm Γ A ≡ Tm Γ' A')
        → ⟦ coe p a ⟧ᵗ
          ≡ coe (ap-Tmᴰᶜ (Tm-injᶜ p) (Tm-injᵀ p)
                   (ap-⟦⟧ᶜ (Tm-injᶜ p)) (ap-⟦⟧ᵀ (Tm-injᶜ p) (Tm-injᵀ p)) refl) ⟦ a ⟧ᵗ
      {-# REWRITE ⟦coe⟧ᵗ #-}

      ⟦coe⟧ᴿ : (p : Conᴿ Γ ≡ Conᴿ Γ')
        → ⟦ coe p Γᴿ ⟧ᴿ
          ≡ coe (ap-Conᴿᴰᶜ (Conᴿ-inj p) (ap-⟦⟧ᶜ (Conᴿ-inj p)) refl) ⟦ Γᴿ ⟧ᴿ
      {-# REWRITE ⟦coe⟧ᴿ #-}

    -- Operation rules: base

    postulate
      ⟦∙⟧ : ⟦ ∙ ⟧ᶜ ≡ ∙ᴰ
      {-# REWRITE ⟦∙⟧ #-}

      ⟦id⟧ : ⟦ id {Γ} ⟧ˢ ≡ idᴰ
      {-# REWRITE ⟦id⟧ #-}

      ⟦∘⟧ : ⟦ σ ∘ τ ⟧ˢ ≡ ⟦ σ ⟧ˢ ∘ᴰ ⟦ τ ⟧ˢ
      {-# REWRITE ⟦∘⟧ #-}

      ⟦ε⟧ : ⟦ ε {Γ} ⟧ˢ ≡ εᴰ
      {-# REWRITE ⟦ε⟧ #-}

      ⟦[]T⟧ : ⟦ A [ σ ]T ⟧ᵀ ≡ ⟦ A ⟧ᵀ [ ⟦ σ ⟧ˢ ]Tᴰ
      {-# REWRITE ⟦[]T⟧ #-}

      ⟦[]⟧ : ⟦ a [ σ ] ⟧ᵗ ≡ ⟦ a ⟧ᵗ [ ⟦ σ ⟧ˢ ]ᴰ
      {-# REWRITE ⟦[]⟧ #-}

      ⟦▷⟧ : ⟦ Γ ▷ A ⟧ᶜ ≡ ⟦ Γ ⟧ᶜ ▷ᴰ ⟦ A ⟧ᵀ
      {-# REWRITE ⟦▷⟧ #-}

      ⟦p⟧ : ⟦ p {Γ} {A} ⟧ˢ ≡ pᴰ
      {-# REWRITE ⟦p⟧ #-}

      ⟦q⟧ : ⟦ q {Γ} {A} ⟧ᵗ ≡ qᴰ
      {-# REWRITE ⟦q⟧ #-}

      ⟦,⟧ : ⟦ σ , a ⟧ˢ ≡ ⟦ σ ⟧ˢ ,ᴰ ⟦ a ⟧ᵗ
      {-# REWRITE ⟦,⟧ #-}

      ⟦U⟧ : ⟦ U {Γ} ⟧ᵀ ≡ Uᴰ
      {-# REWRITE ⟦U⟧ #-}

      ⟦El⟧ : ⟦ El a ⟧ᵀ ≡ Elᴰ ⟦ a ⟧ᵗ
      {-# REWRITE ⟦El⟧ #-}

      ⟦Π⟧ : ⟦ Π ρ A B ⟧ᵀ ≡ Πᴰ ρ ⟦ A ⟧ᵀ ⟦ B ⟧ᵀ
      {-# REWRITE ⟦Π⟧ #-}

      ⟦lam⟧ : ⟦ lam {ρ = ρ} b ⟧ᵗ ≡ lamᴰ ⟦ b ⟧ᵗ
      {-# REWRITE ⟦lam⟧ #-}

      ⟦app⟧ : ⟦ app a ⟧ᵗ ≡ appᴰ ⟦ a ⟧ᵗ
      {-# REWRITE ⟦app⟧ #-}

    -- Operation rules: resources

    postulate
      ⟦∙ᴿ⟧ : ⟦ ∙ᴿ ⟧ᴿ ≡ ∙ᴿᴰ
      {-# REWRITE ⟦∙ᴿ⟧ #-}

      ⟦+ᴿ⟧ : ⟦ Γᴿ +ᴿ Δᴿ ⟧ᴿ ≡ ⟦ Γᴿ ⟧ᴿ +ᴿᴰ ⟦ Δᴿ ⟧ᴿ
      {-# REWRITE ⟦+ᴿ⟧ #-}

      ⟦*ᴿ⟧ : ⟦ ρ *ᴿ Γᴿ ⟧ᴿ ≡ ρ *ᴿᴰ ⟦ Γᴿ ⟧ᴿ
      {-# REWRITE ⟦*ᴿ⟧ #-}

      ⟦▷ᴿ⟧ : ⟦ Γᴿ ▷[ ρ ] A ⟧ᴿ ≡ ⟦ Γᴿ ⟧ᴿ ▷ᴿᴰ[ ρ ] ⟦ A ⟧ᵀ
      {-# REWRITE ⟦▷ᴿ⟧ #-}

      ⟦projᶜ⟧ : ⟦ projᶜ Γᴿ ⟧ᴿ ≡ projᶜᴰ ⟦ Γᴿ ⟧ᴿ
      {-# REWRITE ⟦projᶜ⟧ #-}

-- Context eliminator shorthand
module ElimCon
  {D : SemiringBase} {S : InSemiringBase.SemiringAxioms D}
  (open InSemiringBase D)
  (open RCwF.Model.Over S)
  (open RCwF.DisplayedModel.Over S)
  (open Over {D} {S})
  (P : Con → Set)
  (P∙ : P ∙)
  (P▷ : ∀ Γ A → P Γ → P (Γ ▷ A))
  where

  private
    sᴰ : BaseSortsᴰ sorts
    sᴰ = record { Conᴰ = P ; Subᴰ = λ _ _ _ → 𝟙 ; Tyᴰ = λ _ _ → 𝟙 ; Tmᴰ = λ _ _ _ → 𝟙 }

    bᴰ : InBaseSortsᴰ.BaseCtorsᴰ base sᴰ
    bᴰ = record
      { idᴰ    = tt
      ; _∘ᴰ_   = λ _ _ → tt
      ; id∘ᴰ   = refl
      ; ∘idᴰ   = refl
      ; assocᴰ = refl
      ; ∙ᴰ     = P∙
      ; εᴰ     = tt
      ; ∃!εᴰ   = refl
      ; _[_]Tᴰ = λ _ _ → tt
      ; [id]Tᴰ = refl
      ; [∘]Tᴰ  = refl
      ; _[_]ᴰ  = λ _ _ → tt
      ; [id]ᴰ  = refl
      ; [∘]ᴰ   = refl
      ; _▷ᴰ_   = λ {Γ} {A} Γᴰ _ → P▷ Γ A Γᴰ
      ; pᴰ     = tt
      ; qᴰ     = tt
      ; _,ᴰ_   = λ _ _ → tt
      ; p∘,ᴰ   = refl
      ; ,∘ᴰ    = refl
      ; p,qᴰ   = refl
      ; q[,]ᴰ  = refl
      ; Uᴰ     = tt
      ; Elᴰ    = λ _ → tt
      ; U[]ᴰ   = refl
      ; El[]ᴰ  = refl
      ; Πᴰ     = λ _ _ _ → tt
      ; lamᴰ   = λ _ → tt
      ; appᴰ   = λ _ → tt
      ; Πβᴰ    = λ _ → refl
      ; Πηᴰ    = λ _ → refl
      ; Π[]ᴰ   = refl
      ; lam[]ᴰ = λ _ → refl
      }

    rsᴰ : ResSortsᴰ sorts sᴰ rsorts
    rsᴰ = record
      { Conᴿᴰ = λ _ _ → 𝟙
      ; Subᴿᴰ = λ _ _ _ _ → ⊤
      ; Tmᴿᴰ  = λ _ _ _ → ⊤
      ; _+ᴿᴰ_ = λ _ _ → tt
      ; _*ᴿᴰ_ = λ _ _ → tt
      }

    rdᴰ : InResSortsᴰ.ResCtorsᴰ base sᴰ bᴰ rsorts resourced rsᴰ
    rdᴰ = record
      { 0ᵗᴰ       = λ _ _ → tt
      ; +ᴿ-commᴰ  = refl
      ; +ᴿ-assocᴰ = refl
      ; +ᴿ-0ᴰ     = refl
      ; *ᴿ-assocᴰ = refl
      ; idᴿᴰ      = tt
      ; _∘ᴿᴰ_     = λ _ _ → tt
      ; ∙ᴿᴰ       = tt
      ; +ᴿ-∙ᴰ     = refl
      ; *ᴿ-∙ᴰ     = refl
      ; ∃!∙ᴿᴰ     = λ _ → refl
      ; εᴿᴰ       = tt
      ; _[_]ᴿᴰ    = λ _ _ → tt
      ; _▷ᴿᴰ[_]_  = λ _ _ _ → tt
      ; ext+ᴰ      = refl
      ; ext*ᴰ      = refl
      ; projᶜᴰ     = λ _ → tt
      ; proj-ηᴰ    = λ _ → refl
      ; projᶜ-βᴰ   = refl
      ; pᴿᴰ       = tt
      ; qᴿᴰ       = tt
      ; _,ᴿᴰ[_]_  = λ _ _ _ → tt
      ; lamᴿᴰ     = λ _ → tt
      ; appᴿᴰ     = λ _ → tt
      }

    nᴰ : Totalᴰ syn
    nᴰ = record { sortsᴰ = sᴰ ; baseᴰ = bᴰ ; rsortsᴰ = rsᴰ ; resourcedᴰ = rdᴰ }

  ⟦_⟧ : (Γ : Con) → P Γ
  ⟦ Γ ⟧ = Elim.⟦_⟧ᶜ nᴰ Γ
