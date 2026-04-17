{-# OPTIONS --type-in-type #-}
module RCwF.DisplayedModel where

open import Utils
open import Semiring
import RCwF.Model

module Over {D : SemiringBase} (S : InSemiringBase.SemiringAxioms D) where
  open InSemiringBase D
  open SemiringAxioms S
  open RCwF.Model.Over S

  record BaseSortsᴰ (sorts : BaseSorts) : Set where
    open BaseSorts sorts
    field
      Conᴰ : Con → Set
      Subᴰ : ∀ {Γ Δ} → Conᴰ Γ → Conᴰ Δ → Sub Γ Δ → Set
      Tyᴰ  : ∀ {Γ} → Conᴰ Γ → Ty Γ → Set
      Tmᴰ  : ∀ {Γ A} → (Γᴰ : Conᴰ Γ) → Tyᴰ Γᴰ A → Tm Γ A → Set

  module InBaseSortsᴰ {sorts : BaseSorts} (base : InBaseSorts.BaseCtors sorts) (sortsᴰ : BaseSortsᴰ sorts) where
    open BaseSorts sorts
    open InBaseSorts sorts
    open InBaseSorts.BaseCtors base
    open BaseSortsᴰ sortsᴰ

    variable
      Γᴰ Δᴰ Θᴰ : Conᴰ Γ
      Aᴰ Bᴰ : Tyᴰ Γᴰ A
      σᴰ τᴰ δᴰ : Subᴰ Γᴰ Δᴰ σ
      aᴰ : Tmᴰ Γᴰ Aᴰ a

    opaque
      unfolding coe
      ap-Subᴰ : σ ≡ τ → Subᴰ Γᴰ Δᴰ σ ≡ Subᴰ Γᴰ Δᴰ τ
      ap-Subᴰ refl = refl

      ap-Tyᴰ : A ≡ B → Tyᴰ Γᴰ A ≡ Tyᴰ Γᴰ B
      ap-Tyᴰ refl = refl

      ap-Tmᴰ : (pA : A ≡ B) → Aᴰ ≡[ ap-Tyᴰ pA ] Bᴰ
        → a ≡[ ap-Tm pA ] b → Tmᴰ Γᴰ Aᴰ a ≡ Tmᴰ Γᴰ Bᴰ b
      ap-Tmᴰ refl refl refl = refl

    module BaseUtilsᴰ
      (_[_]Tᴰ : ∀ {Γ Δ A σ} {Γᴰ : Conᴰ Γ} {Δᴰ : Conᴰ Δ}
        → Tyᴰ Δᴰ A → Subᴰ Γᴰ Δᴰ σ → Tyᴰ Γᴰ (A [ σ ]T))
      where
      opaque
        unfolding ap-Subᴰ ap-Tyᴰ
        ap-[]Tᴰ-impl : (p : σ ≡ τ) → σᴰ ≡[ ap-Subᴰ p ] τᴰ
          → Aᴰ [ σᴰ ]Tᴰ ≡[ ap-Tyᴰ (ap-[]T p) ] Aᴰ [ τᴰ ]Tᴰ
        ap-[]Tᴰ-impl refl refl = refl

    record BaseCtorsᴰ : Set where
      field
        idᴰ    : Subᴰ Γᴰ Γᴰ id
        _∘ᴰ_   : Subᴰ Δᴰ Θᴰ σ → Subᴰ Γᴰ Δᴰ τ → Subᴰ Γᴰ Θᴰ (σ ∘ τ)
        id∘ᴰ   : idᴰ ∘ᴰ σᴰ ≡[ ap-Subᴰ id∘ ] σᴰ
        ∘idᴰ   : σᴰ ∘ᴰ idᴰ ≡[ ap-Subᴰ ∘id ] σᴰ
        assocᴰ : δᴰ ∘ᴰ (σᴰ ∘ᴰ τᴰ) ≡[ ap-Subᴰ assoc ] (δᴰ ∘ᴰ σᴰ) ∘ᴰ τᴰ

        ∙ᴰ     : Conᴰ ∙
        εᴰ     : Subᴰ Γᴰ ∙ᴰ ε
        ∃!εᴰ   : εᴰ {Γᴰ = Γᴰ} ≡[ ap-Subᴰ ∃!ε ] σᴰ

        _[_]Tᴰ : Tyᴰ Δᴰ A → Subᴰ Γᴰ Δᴰ σ → Tyᴰ Γᴰ (A [ σ ]T)
        [id]Tᴰ : Aᴰ [ idᴰ ]Tᴰ ≡[ ap-Tyᴰ [id]T ] Aᴰ
        [∘]Tᴰ  : Aᴰ [ σᴰ ∘ᴰ τᴰ ]Tᴰ ≡[ ap-Tyᴰ [∘]T ] (Aᴰ [ σᴰ ]Tᴰ) [ τᴰ ]Tᴰ

        _[_]ᴰ  : Tmᴰ Δᴰ Aᴰ a → (σᴰ : Subᴰ Γᴰ Δᴰ σ) → Tmᴰ Γᴰ (Aᴰ [ σᴰ ]Tᴰ) (a [ σ ])
        [id]ᴰ  : {aᴰ : Tmᴰ Γᴰ Aᴰ a} → aᴰ [ idᴰ ]ᴰ ≡[ ap-Tmᴰ [id]T [id]Tᴰ [id] ] aᴰ
        [∘]ᴰ   : {aᴰ : Tmᴰ Δᴰ Aᴰ a} → aᴰ [ σᴰ ∘ᴰ τᴰ ]ᴰ ≡[ ap-Tmᴰ [∘]T [∘]Tᴰ [∘] ] (aᴰ [ σᴰ ]ᴰ) [ τᴰ ]ᴰ

        _▷ᴰ_   : (Γᴰ : Conᴰ Γ) → Tyᴰ Γᴰ A → Conᴰ (Γ ▷ A)
        pᴰ     : Subᴰ (Γᴰ ▷ᴰ Aᴰ) Γᴰ p
        qᴰ     : Tmᴰ (Γᴰ ▷ᴰ Aᴰ) (Aᴰ [ pᴰ ]Tᴰ) q
        _,ᴰ_   : (σᴰ : Subᴰ Γᴰ Δᴰ σ) → Tmᴰ Γᴰ (Aᴰ [ σᴰ ]Tᴰ) a → Subᴰ Γᴰ (Δᴰ ▷ᴰ Aᴰ) (σ , a)
        p∘,ᴰ   : pᴰ ∘ᴰ (σᴰ ,ᴰ aᴰ) ≡[ ap-Subᴰ p∘, ] σᴰ
        ,∘ᴰ    : (σᴰ ,ᴰ aᴰ) ∘ᴰ τᴰ ≡[ ap-Subᴰ ,∘ ]
                   ((σᴰ ∘ᴰ τᴰ) ,ᴰ coe (ap-Tmᴰ (sym [∘]T) (symᴰ [∘]Tᴰ) refl) (aᴰ [ τᴰ ]ᴰ))
        p,qᴰ   : _,ᴰ_ {Aᴰ = Aᴰ} pᴰ qᴰ ≡[ ap-Subᴰ p,q ] idᴰ

      ap-[]Tᴰ : (p : σ ≡ τ) → σᴰ ≡[ ap-Subᴰ p ] τᴰ
        → Aᴰ [ σᴰ ]Tᴰ ≡[ ap-Tyᴰ (ap-[]T p) ] Aᴰ [ τᴰ ]Tᴰ
      ap-[]Tᴰ = BaseUtilsᴰ.ap-[]Tᴰ-impl _[_]Tᴰ

      _↑ᴰ_ : (σᴰ : Subᴰ Γᴰ Δᴰ σ) → (Aᴰ : Tyᴰ Δᴰ A) → Subᴰ (Γᴰ ▷ᴰ (Aᴰ [ σᴰ ]Tᴰ)) (Δᴰ ▷ᴰ Aᴰ) (σ ↑ A)
      σᴰ ↑ᴰ Aᴰ = (σᴰ ∘ᴰ pᴰ) ,ᴰ coe (ap-Tmᴰ (sym [∘]T) (symᴰ [∘]Tᴰ) refl) qᴰ

      field
        q[,]ᴰ  : {aᴰ : Tmᴰ Γᴰ (Aᴰ [ σᴰ ]Tᴰ) a}
          → qᴰ [ σᴰ ,ᴰ aᴰ ]ᴰ
            ≡[ ap-Tmᴰ (trans (sym [∘]T) (ap-[]T p∘,))
                       (transᴰ (symᴰ [∘]Tᴰ) (ap-[]Tᴰ p∘, p∘,ᴰ))
                       q[,] ]
            aᴰ

        Uᴰ     : Tyᴰ Γᴰ U
        Elᴰ    : Tmᴰ Γᴰ Uᴰ a → Tyᴰ Γᴰ (El a)
        U[]ᴰ   : Uᴰ [ σᴰ ]Tᴰ ≡[ ap-Tyᴰ U[] ] Uᴰ
        El[]ᴰ  : (Elᴰ aᴰ) [ σᴰ ]Tᴰ ≡[ ap-Tyᴰ El[] ] Elᴰ (coe (ap-Tmᴰ U[] U[]ᴰ refl) (aᴰ [ σᴰ ]ᴰ))

        Πᴰ     : (ρ : R) → (Aᴰ : Tyᴰ Γᴰ A) → Tyᴰ (Γᴰ ▷ᴰ Aᴰ) B → Tyᴰ Γᴰ (Π ρ A B)
        lamᴰ   : ∀ {b} → Tmᴰ (Γᴰ ▷ᴰ Aᴰ) Bᴰ b → Tmᴰ Γᴰ (Πᴰ ρ Aᴰ Bᴰ) (lam b)
        appᴰ   : Tmᴰ Γᴰ (Πᴰ ρ Aᴰ Bᴰ) a → Tmᴰ (Γᴰ ▷ᴰ Aᴰ) Bᴰ (app a)
        Πβᴰ    : ∀ {b} → (tᴰ : Tmᴰ (Γᴰ ▷ᴰ Aᴰ) Bᴰ b) → appᴰ {ρ = ρ} (lamᴰ tᴰ) ≡[ ap-Tmᴰ refl reflᴰ (dep (Πβ b)) ] tᴰ
        Πηᴰ    : (fᴰ : Tmᴰ Γᴰ (Πᴰ ρ Aᴰ Bᴰ) a) → lamᴰ (appᴰ fᴰ) ≡[ ap-Tmᴰ refl reflᴰ (dep (Πη a)) ] fᴰ
        Π[]ᴰ   : (Πᴰ ρ Aᴰ Bᴰ) [ σᴰ ]Tᴰ ≡[ ap-Tyᴰ Π[] ] Πᴰ ρ (Aᴰ [ σᴰ ]Tᴰ) (Bᴰ [ σᴰ ↑ᴰ Aᴰ ]Tᴰ)
        lam[]ᴰ : ∀ {b} → (tᴰ : Tmᴰ (Δᴰ ▷ᴰ Aᴰ) Bᴰ b)
          → (lamᴰ {ρ = ρ} tᴰ) [ σᴰ ]ᴰ ≡[ ap-Tmᴰ Π[] Π[]ᴰ (lam[] b) ] lamᴰ (tᴰ [ σᴰ ↑ᴰ Aᴰ ]ᴰ)

  record ResSortsᴰ (sorts : BaseSorts) (sortsᴰ : BaseSortsᴰ sorts) (rsorts : ResSorts sorts) : Set where
    open BaseSorts sorts
    open BaseSortsᴰ sortsᴰ
    open ResSorts rsorts
    field
      Conᴿᴰ : ∀ {Γ} → Conᴰ Γ → Conᴿ Γ → Set
      Subᴿᴰ : ∀ {Γ Δ σ} {Γᴰ : Conᴰ Γ} {Δᴰ : Conᴰ Δ} {Γᴿ : Conᴿ Γ} {Δᴿ : Conᴿ Δ}
        → Conᴿᴰ Γᴰ Γᴿ → Conᴿᴰ Δᴰ Δᴿ → Subᴰ Γᴰ Δᴰ σ → Subᴿ Γᴿ Δᴿ σ → Prop
      Tmᴿᴰ  : ∀ {Γ A a μ} {Γᴰ : Conᴰ Γ} {Γᴿ : Conᴿ Γ} {Aᴰ : Tyᴰ Γᴰ A}
        → Conᴿᴰ Γᴰ Γᴿ → Tmᴰ Γᴰ Aᴰ a → Tmᴿ Γᴿ μ A a → Prop
      _+ᴿᴰ_ : ∀ {Γ} {Γᴰ : Conᴰ Γ} {Γᴿ Δᴿ : Conᴿ Γ} → Conᴿᴰ Γᴰ Γᴿ → Conᴿᴰ Γᴰ Δᴿ → Conᴿᴰ Γᴰ (Γᴿ +ᴿ Δᴿ)
      _*ᴿᴰ_ : ∀ {Γ} {Γᴰ : Conᴰ Γ} {Γᴿ : Conᴿ Γ} → (ρ : R) → Conᴿᴰ Γᴰ Γᴿ → Conᴿᴰ Γᴰ (ρ *ᴿ Γᴿ)

  module InResSortsᴰ
    {sorts : BaseSorts} (base : InBaseSorts.BaseCtors sorts) (sortsᴰ : BaseSortsᴰ sorts)
    (baseᴰ : InBaseSortsᴰ.BaseCtorsᴰ base sortsᴰ)
    (rsorts : ResSorts sorts) (resourced : InResSorts.ResCtors base rsorts)
    (rsortsᴰ : ResSortsᴰ sorts sortsᴰ rsorts)
    where
    open BaseSorts sorts
    open InBaseSorts sorts
    open InBaseSorts.BaseCtors base
    open BaseSortsᴰ sortsᴰ
    open InBaseSortsᴰ base sortsᴰ
    open BaseCtorsᴰ baseᴰ
    open ResSorts rsorts
    open InResSorts base rsorts
    open ResCtors resourced
    open ResSortsᴰ rsortsᴰ

    variable
      Γᴿᴰ Δᴿᴰ Θᴿᴰ : Conᴿᴰ Γᴰ Γᴿ
      σᴿ τᴿ : Subᴿ Γᴿ Δᴿ σ
      aᴿ : Tmᴿ Γᴿ μ A a

    opaque
      unfolding coe
      ap-Conᴿᴰ : Γᴿ ≡ Δᴿ → Conᴿᴰ Γᴰ Γᴿ ≡ Conᴿᴰ Γᴰ Δᴿ
      ap-Conᴿᴰ refl = refl

    record ResCtorsᴰ : Set where
      field
        0ᵗᴰ   : (aᴰ : Tmᴰ Γᴰ Aᴰ a) → (Γᴿᴰ : Conᴿᴰ Γᴰ Γᴿ) → Tmᴿᴰ Γᴿᴰ aᴰ (0ᵗ a)

        +ᴿ-commᴰ  : (Γᴿᴰ +ᴿᴰ Δᴿᴰ) ≡[ ap-Conᴿᴰ +ᴿ-comm ] (Δᴿᴰ +ᴿᴰ Γᴿᴰ)
        +ᴿ-assocᴰ : ((Γᴿᴰ +ᴿᴰ Δᴿᴰ) +ᴿᴰ Θᴿᴰ) ≡[ ap-Conᴿᴰ +ᴿ-assoc ] (Γᴿᴰ +ᴿᴰ (Δᴿᴰ +ᴿᴰ Θᴿᴰ))
        +ᴿ-0ᴰ     : ((0r *ᴿᴰ Γᴿᴰ) +ᴿᴰ Δᴿᴰ) ≡[ ap-Conᴿᴰ +ᴿ-0 ] Δᴿᴰ
        *ᴿ-assocᴰ : ((ρ *r π) *ᴿᴰ Γᴿᴰ) ≡[ ap-Conᴿᴰ *ᴿ-assoc ] (ρ *ᴿᴰ (π *ᴿᴰ Γᴿᴰ))
        idᴿᴰ   : Subᴿᴰ Γᴿᴰ Γᴿᴰ idᴰ idᴿ
        _∘ᴿᴰ_  : Subᴿᴰ Δᴿᴰ Θᴿᴰ σᴰ σᴿ → Subᴿᴰ Γᴿᴰ Δᴿᴰ τᴰ τᴿ → Subᴿᴰ Γᴿᴰ Θᴿᴰ (σᴰ ∘ᴰ τᴰ) (σᴿ ∘ᴿ τᴿ)

        ∙ᴿᴰ    : Conᴿᴰ ∙ᴰ ∙ᴿ
        +ᴿ-∙ᴰ  : (∙ᴿᴰ +ᴿᴰ ∙ᴿᴰ) ≡[ ap-Conᴿᴰ +ᴿ-∙ ] ∙ᴿᴰ
        *ᴿ-∙ᴰ  : (ρ *ᴿᴰ ∙ᴿᴰ) ≡[ ap-Conᴿᴰ (*ᴿ-∙ {ρ = ρ}) ] ∙ᴿᴰ
        ∃!∙ᴿᴰ  : (Γᴿᴰ : Conᴿᴰ ∙ᴰ Γᴿ) → Γᴿᴰ ≡[ ap-Conᴿᴰ (∃!∙ᴿ Γᴿ) ] ∙ᴿᴰ
        εᴿᴰ    : Subᴿᴰ (0r *ᴿᴰ Γᴿᴰ) ∙ᴿᴰ εᴰ εᴿ

        _[_]ᴿᴰ : Tmᴿᴰ Δᴿᴰ aᴰ aᴿ → Subᴿᴰ Γᴿᴰ Δᴿᴰ σᴰ σᴿ → Tmᴿᴰ Γᴿᴰ (aᴰ [ σᴰ ]ᴰ) (aᴿ [ σᴿ ]ᴿ)

        _▷ᴿᴰ[_]_ : Conᴿᴰ Γᴰ Γᴿ → (ρ : R) → (Aᴰ : Tyᴰ Γᴰ A) → Conᴿᴰ (Γᴰ ▷ᴰ Aᴰ) (Γᴿ ▷[ ρ ] A)
        ext+ᴰ   : ((Γᴿᴰ +ᴿᴰ Δᴿᴰ) ▷ᴿᴰ[ ρ +r π ] Aᴰ) ≡[ ap-Conᴿᴰ ext+ ] ((Γᴿᴰ ▷ᴿᴰ[ ρ ] Aᴰ) +ᴿᴰ (Δᴿᴰ ▷ᴿᴰ[ π ] Aᴰ))
        ext*ᴰ   : ((ρ *ᴿᴰ Γᴿᴰ) ▷ᴿᴰ[ ρ *r π ] Aᴰ) ≡[ ap-Conᴿᴰ ext* ] (ρ *ᴿᴰ (Γᴿᴰ ▷ᴿᴰ[ π ] Aᴰ))
        projᶜᴰ   : Conᴿᴰ (Γᴰ ▷ᴰ Aᴰ) Γᴿ → Conᴿᴰ Γᴰ (projᶜ Γᴿ)
        proj-ηᴰ  : (Γᴿᴰ : Conᴿᴰ (Γᴰ ▷ᴰ Aᴰ) Γᴿ)
          → Γᴿᴰ ≡[ ap-Conᴿᴰ (proj-η Γᴿ) ] (projᶜᴰ Γᴿᴰ ▷ᴿᴰ[ projʳ Γᴿ ] Aᴰ)
        projᶜ-βᴰ : {Γᴿᴰ : Conᴿᴰ Γᴰ Γᴿ}
          → projᶜᴰ (Γᴿᴰ ▷ᴿᴰ[ ρ ] Aᴰ) ≡[ ap-Conᴿᴰ projᶜ-β ] Γᴿᴰ
        pᴿᴰ    : Subᴿᴰ (Γᴿᴰ ▷ᴿᴰ[ 0r ] Aᴰ) Γᴿᴰ pᴰ pᴿ
        qᴿᴰ    : Tmᴿᴰ ((0r *ᴿᴰ Γᴿᴰ) ▷ᴿᴰ[ 1r ] Aᴰ) qᴰ qᴿ
        _,ᴿᴰ[_]_ : Subᴿᴰ Γᴿᴰ Δᴿᴰ σᴰ σᴿ → (ρ : R)
          → {aᴿ : Tmᴿ Θᴿ (mode ρ) (A [ σ ]T) a}
          → Tmᴿᴰ Θᴿᴰ aᴰ aᴿ
          → Subᴿᴰ (Γᴿᴰ +ᴿᴰ (ρ *ᴿᴰ Θᴿᴰ)) (Δᴿᴰ ▷ᴿᴰ[ ρ ] Aᴰ) (σᴰ ,ᴰ aᴰ) (σᴿ ,ᴿ[ ρ ] aᴿ)

        lamᴿᴰ  : Tmᴿᴰ (Γᴿᴰ ▷ᴿᴰ[ ρ ] Aᴰ) aᴰ aᴿ → Tmᴿᴰ Γᴿᴰ (lamᴰ aᴰ) (lamᴿ aᴿ)
        appᴿᴰ  : Tmᴿᴰ Γᴿᴰ aᴰ aᴿ → Tmᴿᴰ (Γᴿᴰ ▷ᴿᴰ[ ρ ] Aᴰ) (appᴰ aᴰ) (appᴿ aᴿ)

  record Totalᴰ (M : Total) : Set where
    open Total M
    open InBaseSorts sorts
    open InResSorts base rsorts
    field
      sortsᴰ : BaseSortsᴰ sorts
    open BaseSortsᴰ sortsᴰ public
    open InBaseSortsᴰ base sortsᴰ
    field
      baseᴰ : BaseCtorsᴰ
    open BaseCtorsᴰ baseᴰ public
    field
      rsortsᴰ : ResSortsᴰ sorts sortsᴰ rsorts
    open ResSortsᴰ rsortsᴰ public
    open InResSortsᴰ base sortsᴰ baseᴰ rsorts resourced rsortsᴰ
    field
      resourcedᴰ : ResCtorsᴰ
    open ResCtorsᴰ resourcedᴰ public
