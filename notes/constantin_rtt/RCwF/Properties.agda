{-# OPTIONS --type-in-type #-}
module RCwF.Properties where

open import Utils
open import Semiring
open import Data.Product using (_×_) renaming (_,_ to _,,_)
open import Data.Unit renaming (⊤ to 𝟙; tt to tt𝟙)
import RCwF.Model
import RCwF.Syntax
import RCwF.DisplayedModel

module Over {D : SemiringBase} {S : InSemiringBase.SemiringAxioms D} where
  open InSemiringBase D
  open SemiringAxioms S
  open RCwF.Model.Over S
  open RCwF.Syntax.Over {D} {S} public
  open RCwF.DisplayedModel.Over S
  open InBaseSorts sorts
  open InResSorts base rsorts

  -- Some extra module properties are derivable by induction on contexts:

  *ᴿ-distl : ρ *ᴿ (Γᴿ +ᴿ Δᴿ) ≡ (ρ *ᴿ Γᴿ) +ᴿ (ρ *ᴿ Δᴿ)
  *ᴿ-distl {ρ = ρ} {Γᴿ = Γᴿ} {Δᴿ = Δᴿ} = (RCwF.Syntax.ElimCon.⟦_⟧ {D} {S}
    (λ Γ → ∀ (ρ : R) (Γᴿ Δᴿ : Conᴿ Γ) → (ρ *ᴿ (Γᴿ +ᴿ Δᴿ) ≡ (ρ *ᴿ Γᴿ) +ᴿ (ρ *ᴿ Δᴿ)) true)
    (λ ρ Γᴿ Δᴿ → by (
      trans (cong (ρ *ᴿ_) (cong₂ _+ᴿ_ (∃!∙ᴿ Γᴿ) (∃!∙ᴿ Δᴿ)))
      (trans (cong (ρ *ᴿ_) +ᴿ-∙)
      (trans *ᴿ-∙
      (sym (trans (cong₂ _+ᴿ_ (trans (cong (ρ *ᴿ_) (∃!∙ᴿ Γᴿ)) *ᴿ-∙)
                                (trans (cong (ρ *ᴿ_) (∃!∙ᴿ Δᴿ)) *ᴿ-∙))
                  +ᴿ-∙))))))
    (λ Γ A ih ρ Γᴿ Δᴿ → by (
      let Γᴿ₀ = projᶜ Γᴿ; π₁ = projʳ Γᴿ; eΓ = proj-η Γᴿ
          Δᴿ₀ = projᶜ Δᴿ; π₂ = projʳ Δᴿ; eΔ = proj-η Δᴿ in
      trans (cong (ρ *ᴿ_) (cong₂ _+ᴿ_ eΓ eΔ))
      (trans (cong (ρ *ᴿ_) (sym ext+))
      (trans (sym ext*)
      (trans (ap-▷ᴿ (ih ρ Γᴿ₀ Δᴿ₀ .witness) distl)
      (trans ext+
      (cong₂ _+ᴿ_ (trans ext* (cong (ρ *ᴿ_) (sym eΓ)))
                    (trans ext* (cong (ρ *ᴿ_) (sym eΔ))))))))))
    _ ρ Γᴿ Δᴿ) .witness

  *ᴿ-distr : (ρ +r π) *ᴿ Γᴿ ≡ (ρ *ᴿ Γᴿ) +ᴿ (π *ᴿ Γᴿ)
  *ᴿ-distr {ρ = ρ} {π = π} {Γᴿ = Γᴿ} = (RCwF.Syntax.ElimCon.⟦_⟧ {D} {S}
    (λ Γ → ∀ (ρ π : R) (Γᴿ : Conᴿ Γ) → ((ρ +r π) *ᴿ Γᴿ ≡ (ρ *ᴿ Γᴿ) +ᴿ (π *ᴿ Γᴿ)) true)
    (λ ρ π Γᴿ → by (
      let e = ∃!∙ᴿ Γᴿ in
      trans (cong ((ρ +r π) *ᴿ_) e) (trans *ᴿ-∙
      (sym (trans (cong₂ _+ᴿ_ (trans (cong (ρ *ᴿ_) e) *ᴿ-∙)
                                (trans (cong (π *ᴿ_) e) *ᴿ-∙))
                  +ᴿ-∙)))))
    (λ Γ A ih ρ π Γᴿ → by (
      let Γᴿ₀ = projᶜ Γᴿ; ξ = projʳ Γᴿ; eΓ = proj-η Γᴿ in
      trans (cong ((ρ +r π) *ᴿ_) eΓ)
      (trans (sym ext*)
      (trans (ap-▷ᴿ (ih ρ π Γᴿ₀ .witness) distr)
      (trans ext+
      (cong₂ _+ᴿ_ (trans ext* (cong (ρ *ᴿ_) (sym eΓ)))
                    (trans ext* (cong (π *ᴿ_) (sym eΓ)))))))))
    _ ρ π Γᴿ) .witness

  *ᴿ-1 : 1r *ᴿ Γᴿ ≡ Γᴿ
  *ᴿ-1 {Γᴿ = Γᴿ} = (RCwF.Syntax.ElimCon.⟦_⟧ {D} {S}
    (λ Γ → ∀ (Γᴿ : Conᴿ Γ) → (1r *ᴿ Γᴿ ≡ Γᴿ) true)
    (λ Γᴿ → by (trans (cong (1r *ᴿ_) (∃!∙ᴿ Γᴿ)) (trans *ᴿ-∙ (sym (∃!∙ᴿ Γᴿ)))))
    (λ Γ A ih Γᴿ → by (
      let Γᴿ₀ = projᶜ Γᴿ; ξ = projʳ Γᴿ; eΓ = proj-η Γᴿ in
      trans (cong (1r *ᴿ_) eΓ)
      (trans (sym ext*)
      (trans (ap-▷ᴿ (ih Γᴿ₀ .witness) *r-1l)
      (sym eΓ)))))
    _ Γᴿ) .witness

  -- Shorthand for a trivial base displayed model
  private
    triv-sᴰ : BaseSortsᴰ sorts
    triv-sᴰ = record { Conᴰ = λ _ → 𝟙 ; Subᴰ = λ _ _ _ → 𝟙 ; Tyᴰ = λ _ _ → 𝟙 ; Tmᴰ = λ _ _ _ → 𝟙 }

    triv-bᴰ : InBaseSortsᴰ.BaseCtorsᴰ base triv-sᴰ
    triv-bᴰ = record
      { idᴰ    = tt𝟙 ; _∘ᴰ_   = λ _ _ → tt𝟙 ; id∘ᴰ = refl ; ∘idᴰ = refl ; assocᴰ = refl
      ; ∙ᴰ     = tt𝟙 ; εᴰ     = tt𝟙 ; ∃!εᴰ   = refl
      ; _[_]Tᴰ = λ _ _ → tt𝟙 ; [id]Tᴰ = refl ; [∘]Tᴰ  = refl
      ; _[_]ᴰ  = λ _ _ → tt𝟙 ; [id]ᴰ  = refl ; [∘]ᴰ   = refl
      ; _▷ᴰ_   = λ _ _ → tt𝟙 ; pᴰ = tt𝟙 ; qᴰ = tt𝟙 ; _,ᴰ_ = λ _ _ → tt𝟙
      ; p∘,ᴰ = refl ; ,∘ᴰ = refl ; p,qᴰ = refl ; q[,]ᴰ = refl
      ; Uᴰ = tt𝟙 ; Elᴰ = λ _ → tt𝟙 ; U[]ᴰ = refl ; El[]ᴰ = refl
      ; Πᴰ = λ _ _ _ → tt𝟙 ; lamᴰ = λ _ → tt𝟙 ; appᴰ = λ _ → tt𝟙
      ; Πβᴰ = λ _ → refl ; Πηᴰ = λ _ → refl ; Π[]ᴰ = refl ; lam[]ᴰ = λ _ → refl
      }

    triv-rdᴰ : InResSortsᴰ.ResCtorsᴰ base triv-sᴰ triv-bᴰ rsorts resourced
      (record { Conᴿᴰ = λ _ _ → 𝟙 ; Subᴿᴰ = λ _ _ _ _ → ⊤ ; Tmᴿᴰ = λ _ _ _ → ⊤
              ; _+ᴿᴰ_ = λ _ _ → tt𝟙 ; _*ᴿᴰ_ = λ _ _ → tt𝟙 })
    triv-rdᴰ = record
      { 0ᵗᴰ       = λ _ _ → tt
      ; +ᴿ-commᴰ  = refl ; +ᴿ-assocᴰ = refl ; +ᴿ-0ᴰ = refl ; *ᴿ-assocᴰ = refl
      ; idᴿᴰ      = tt ; _∘ᴿᴰ_     = λ _ _ → tt
      ; ∙ᴿᴰ       = tt𝟙 ; +ᴿ-∙ᴰ = refl ; *ᴿ-∙ᴰ = refl ; ∃!∙ᴿᴰ = λ _ → refl
      ; εᴿᴰ       = tt ; _[_]ᴿᴰ    = λ _ _ → tt
      ; _▷ᴿᴰ[_]_  = λ _ _ _ → tt𝟙
      ; ext+ᴰ = refl ; ext*ᴰ = refl
      ; projᶜᴰ = λ _ → tt𝟙 ; proj-ηᴰ = λ _ → refl ; projᶜ-βᴰ = refl
      ; pᴿᴰ       = tt ; qᴿᴰ = tt
      ; _,ᴿᴰ[_]_  = λ _ _ _ → tt
      ; lamᴿᴰ     = λ _ → tt ; appᴿᴰ = λ _ → tt
      }

  -- Some lemmas about modes of resourced terms.

  Tmᴿ-from-+₁ : Tmᴿ Γᴿ (mode (ρ +r π)) A a → Tmᴿ Γᴿ (mode ρ) A a
  Tmᴿ-from-+₁ {ρ = ρ} {π = π} = go (mode ρ) refl
    where go : ∀ μ → mode ρ ≡ μ → Tmᴿ _ (mode (ρ +r π)) _ _ → Tmᴿ _ μ _ _
          go 0m _ _ = 0ᵗ _
          go 1m eq x = substP (λ μ → Tmᴿ _ μ _ _) (mode-+r {π = π} eq) x

  Tmᴿ-from-+₂ : Tmᴿ Γᴿ (mode (ρ +r π)) A a → Tmᴿ Γᴿ (mode π) A a
  Tmᴿ-from-+₂ {ρ = ρ} {π = π} = go (mode π) refl
    where go : ∀ μ → mode π ≡ μ → Tmᴿ _ (mode (ρ +r π)) _ _ → Tmᴿ _ μ _ _
          go 0m _ _ = 0ᵗ _
          go 1m eq x = substP (λ μ → Tmᴿ _ μ _ _) (trans (cong mode +r-comm) (mode-+r eq)) x

  Tmᴿ-from-* : mode ρ ≡ 1m → Tmᴿ Γᴿ (mode (ρ *r π)) A a → Tmᴿ Γᴿ (mode π) A a
  Tmᴿ-from-* {ρ = ρ} {π = π} mρ = go (mode π) refl
    where go : ∀ μ → mode π ≡ μ → Tmᴿ _ (mode (ρ *r π)) _ _ → Tmᴿ _ μ _ _
          go 0m _ _ = 0ᵗ _
          go 1m eq x = substP (λ μ → Tmᴿ _ μ _ _) (mode-*r mρ eq) x

  -- Lemmas about substitutions:
  -- These must be proven by a full displayed model, it does not suffice to do
  -- induction over contexts.

  -- A substitution into a sum of contexts can be split into two substitutions
  -- by a split of the domain context.

  sub-split-+ : (σᴿ : Subᴿ Γᴿ Δᴿ σ)
    → (Δ₁ Δ₂ : Conᴿ _) → Δ₁ +ᴿ Δ₂ ≡ Δᴿ
    → ∃P (Conᴿ _ × Conᴿ _) λ { (Γ₁ ,, Γ₂) →
        ΣProp (Γ₁ +ᴿ Γ₂ ≡ Γᴿ) λ _ →
        ΣProp (Subᴿ Γ₁ Δ₁ σ) λ _ →
        Subᴿ Γ₂ Δ₂ σ }
  sub-split-+ σᴿ = SP.E.⟦ σᴿ ⟧ˢᴿ where
    module SP where
      rsᴰ : ResSortsᴰ sorts triv-sᴰ rsorts
      rsᴰ = record
        { Conᴿᴰ = λ _ _ → 𝟙
        ; Subᴿᴰ = λ {Γ} {Δ} {σ} {_} {_} {Γᴿ} {Δᴿ} _ _ _ _ →
            ∀ (Δ₁ Δ₂ : Conᴿ Δ) → Δ₁ +ᴿ Δ₂ ≡ Δᴿ →
            ∃P (Conᴿ Γ × Conᴿ Γ) λ { (Γ₁ ,, Γ₂) →
              ΣProp (Γ₁ +ᴿ Γ₂ ≡ Γᴿ) λ _ →
              ΣProp (Subᴿ Γ₁ Δ₁ σ) λ _ →
              Subᴿ Γ₂ Δ₂ σ }
        ; Tmᴿᴰ = λ _ _ _ → ⊤
        ; _+ᴿᴰ_ = λ _ _ → tt𝟙
        ; _*ᴿᴰ_ = λ _ _ → tt𝟙
        }

      open InResSortsᴰ base triv-sᴰ triv-bᴰ rsorts resourced rsᴰ

      rdᴰ : ResCtorsᴰ
      rdᴰ = record
        { 0ᵗᴰ       = λ _ _ → tt
        ; +ᴿ-commᴰ  = refl ; +ᴿ-assocᴰ = refl ; +ᴿ-0ᴰ = refl ; *ᴿ-assocᴰ = refl
        ; idᴿᴰ      = λ Δ₁ Δ₂ eq → (Δ₁ ,, Δ₂) ,∃ (eq ,P (idᴿ ,P idᴿ))
        ; _∘ᴿᴰ_     = λ sH tH Θ₁ Θ₂ eq →
            ∃P-elim (λ { (Δ₁ ,, Δ₂) (deq ,P (sᴿ₁ ,P sᴿ₂)) →
              ∃P-elim (λ { (Γ₁ ,, Γ₂) (geq ,P (tᴿ₁ ,P tᴿ₂)) →
                (Γ₁ ,, Γ₂) ,∃ (geq ,P ((sᴿ₁ ∘ᴿ tᴿ₁) ,P (sᴿ₂ ∘ᴿ tᴿ₂)))
              }) (tH Δ₁ Δ₂ deq)
            }) (sH Θ₁ Θ₂ eq)
        ; ∙ᴿᴰ       = tt𝟙 ; +ᴿ-∙ᴰ = refl ; *ᴿ-∙ᴰ = refl ; ∃!∙ᴿᴰ = λ _ → refl
        ; εᴿᴰ       = λ {_} {_} {Γᴿ} {_} Δ₁ Δ₂ _ →
            (0r *ᴿ Γᴿ ,, 0r *ᴿ Γᴿ) ,∃
              (trans (sym *ᴿ-distr) (cong (_*ᴿ Γᴿ) +r-0)
              ,P (substP (λ X → Subᴿ (0r *ᴿ Γᴿ) X ε) (sym (∃!∙ᴿ Δ₁)) εᴿ
              ,P  substP (λ X → Subᴿ (0r *ᴿ Γᴿ) X ε) (sym (∃!∙ᴿ Δ₂)) εᴿ))
        ; _[_]ᴿᴰ    = λ _ _ → tt
        ; _▷ᴿᴰ[_]_  = λ _ _ _ → tt𝟙
        ; ext+ᴰ = refl ; ext*ᴰ = refl
        ; projᶜᴰ = λ _ → tt𝟙 ; proj-ηᴰ = λ _ → refl ; projᶜ-βᴰ = refl
        ; pᴿᴰ       = λ {_} {_} {_} {_} Δ₁ Δ₂ eq →
            ((Δ₁ ▷[ 0r ] _) ,, (Δ₂ ▷[ 0r ] _)) ,∃
              (trans (sym ext+) (ap-▷ᴿ eq +r-0)
              ,P (pᴿ ,P pᴿ))
        ; qᴿᴰ       = tt
        ; _,ᴿᴰ[_]_  = λ σH ρ₀ {aᴿ} _ T₁ T₂ eq →
            let D₁ = projᶜ T₁; D₂ = projᶜ T₂; ρ₁ = projʳ T₁; ρ₂ = projʳ T₂
                combined = trans ext+ (trans (sym (ap-+ᴿ (proj-η T₁) (proj-η T₂))) eq)
                pΔ = trans (sym projᶜ-β) (trans (cong projᶜ combined) projᶜ-β)
                pρ = trans (sym projʳ-β) (trans (cong projʳ combined) projʳ-β)
            in ∃P-elim (λ { (G₁ ,, G₂) (geq ,P (σᴿ₁ ,P σᴿ₂)) →
              let aᴿ' = substP (λ r → Tmᴿ _ (mode r) _ _) (sym pρ) aᴿ
                  aᴿ₁ = Tmᴿ-from-+₁ aᴿ'
                  aᴿ₂ = Tmᴿ-from-+₂ aᴿ'
                  s₁ = ap-Subᴿ₂ (sym (proj-η T₁)) (σᴿ₁ ,ᴿ[ ρ₁ ] aᴿ₁)
                  s₂ = ap-Subᴿ₂ (sym (proj-η T₂)) (σᴿ₂ ,ᴿ[ ρ₂ ] aᴿ₂)
                  rearrange =
                    trans +ᴿ-assoc (trans (ap-+ᴿ refl
                      (trans (sym +ᴿ-assoc) (trans (ap-+ᴿ +ᴿ-comm refl) +ᴿ-assoc)))
                      (trans (sym +ᴿ-assoc) (ap-+ᴿ geq
                        (trans (sym *ᴿ-distr) (ap-*ᴿ pρ refl)))))
              in (_ ,, _) ,∃ (rearrange ,P (s₁ ,P s₂))
            }) (σH D₁ D₂ pΔ)
        ; lamᴿᴰ     = λ _ → tt ; appᴿᴰ = λ _ → tt
        }

      nᴰ : Totalᴰ syn
      nᴰ = record { sortsᴰ = triv-sᴰ ; baseᴰ = triv-bᴰ ; rsortsᴰ = rsᴰ ; resourcedᴰ = rdᴰ }

      module E = Elim nᴰ

  -- Same thing but for scaling.

  sub-split-* : (ξ : R) → mode ξ ≡ 1m → (σᴿ : Subᴿ Γᴿ Δᴿ σ)
    → (Δ' : Conᴿ _) → ξ *ᴿ Δ' ≡ Δᴿ
    → ∃P (Conᴿ _) λ Γ' →
        ΣProp (ξ *ᴿ Γ' ≡ Γᴿ) λ _ →
        Subᴿ Γ' Δ' σ
  sub-split-* ξ mξ σᴿ = SS.E.⟦ σᴿ ⟧ˢᴿ where
    module SS where
      rsᴰ : ResSortsᴰ sorts triv-sᴰ rsorts
      rsᴰ = record
        { Conᴿᴰ = λ _ _ → 𝟙
        ; Subᴿᴰ = λ {Γ} {Δ} {σ} {_} {_} {Γᴿ} {Δᴿ} _ _ _ _ →
            (Δ' : Conᴿ Δ) → ξ *ᴿ Δ' ≡ Δᴿ →
            ∃P (Conᴿ Γ) λ Γ' →
              ΣProp (ξ *ᴿ Γ' ≡ Γᴿ) λ _ →
              Subᴿ Γ' Δ' σ
        ; Tmᴿᴰ = λ _ _ _ → ⊤
        ; _+ᴿᴰ_ = λ _ _ → tt𝟙
        ; _*ᴿᴰ_ = λ _ _ → tt𝟙
        }

      open InResSortsᴰ base triv-sᴰ triv-bᴰ rsorts resourced rsᴰ

      rdᴰ : ResCtorsᴰ
      rdᴰ = record
        { 0ᵗᴰ       = λ _ _ → tt
        ; +ᴿ-commᴰ  = refl ; +ᴿ-assocᴰ = refl ; +ᴿ-0ᴰ = refl ; *ᴿ-assocᴰ = refl
        ; idᴿᴰ      = λ Δ' eq → Δ' ,∃ (eq ,P idᴿ)
        ; _∘ᴿᴰ_     = λ sH tH Θ' eq →
            ∃P-elim (λ Δ' (deq ,P sᴿ') →
              ∃P-elim (λ Γ' (geq ,P tᴿ') →
                Γ' ,∃ (geq ,P (sᴿ' ∘ᴿ tᴿ'))
              ) (tH Δ' deq)
            ) (sH Θ' eq)
        ; ∙ᴿᴰ       = tt𝟙 ; +ᴿ-∙ᴰ = refl ; *ᴿ-∙ᴰ = refl ; ∃!∙ᴿᴰ = λ _ → refl
        ; εᴿᴰ       = λ {_} {_} {Γᴿ} {_} Δ' eq →
            (0r *ᴿ Γᴿ) ,∃
              (trans (sym *ᴿ-assoc) (cong (_*ᴿ Γᴿ) *r-0r)
              ,P substP (λ X → Subᴿ (0r *ᴿ Γᴿ) X ε) (sym (∃!∙ᴿ Δ')) εᴿ)
        ; _[_]ᴿᴰ    = λ _ _ → tt
        ; _▷ᴿᴰ[_]_  = λ _ _ _ → tt𝟙
        ; ext+ᴰ = refl ; ext*ᴰ = refl
        ; projᶜᴰ = λ _ → tt𝟙 ; proj-ηᴰ = λ _ → refl ; projᶜ-βᴰ = refl
        ; pᴿᴰ       = λ {_} {_} {_} {_} Δ' eq →
            (Δ' ▷[ 0r ] _) ,∃
              (trans (sym ext*) (ap-▷ᴿ eq *r-0r)
              ,P pᴿ)
        ; qᴿᴰ       = tt
        ; _,ᴿᴰ[_]_  = λ σH ρ₀ {aᴿ} _ T' eq →
            let D' = projᶜ T'; π = projʳ T'
                combined = trans ext* (trans (cong (ξ *ᴿ_) (sym (proj-η T'))) eq)
                pΔ = trans (sym projᶜ-β) (trans (cong projᶜ combined) projᶜ-β)
                pρ = trans (sym projʳ-β) (trans (cong projʳ combined) projʳ-β)
            in ∃P-elim (λ G' (geq ,P σᴿ') →
              let aᴿ' = Tmᴿ-from-* mξ
                          (substP (λ r → Tmᴿ _ (mode r) _ _) (sym pρ) aᴿ)
                  s = ap-Subᴿ₂ (sym (proj-η T')) (σᴿ' ,ᴿ[ π ] aᴿ')
                  sum-eq =
                    trans *ᴿ-distl (ap-+ᴿ geq
                      (trans (sym *ᴿ-assoc) (ap-*ᴿ pρ refl)))
              in _ ,∃ (sum-eq ,P s)
            ) (σH D' pΔ)
        ; lamᴿᴰ     = λ _ → tt ; appᴿᴰ = λ _ → tt
        }

      nᴰ : Totalᴰ syn
      nᴰ = record { sortsᴰ = triv-sᴰ ; baseᴰ = triv-bᴰ ; rsortsᴰ = rsᴰ ; resourcedᴰ = rdᴰ }

      module E = Elim nᴰ

  -- A substitution into a zeroed context must also have a zeroed domain.

  sub-zero : (σᴿ : Subᴿ Γᴿ Δᴿ σ) → Δᴿ ≡ 0r *ᴿ Δᴿ → Γᴿ ≡ 0r *ᴿ Γᴿ
  sub-zero σᴿ = SZ.E.⟦ σᴿ ⟧ˢᴿ where
    module SZ where
      rsᴰ : ResSortsᴰ sorts triv-sᴰ rsorts
      rsᴰ = record
        { Conᴿᴰ = λ _ _ → 𝟙
        ; Subᴿᴰ = λ {Γ} {Δ} {σ} {_} {_} {Γᴿ} {Δᴿ} _ _ _ _ →
            Δᴿ ≡ 0r *ᴿ Δᴿ → Γᴿ ≡ 0r *ᴿ Γᴿ
        ; Tmᴿᴰ = λ _ _ _ → ⊤
        ; _+ᴿᴰ_ = λ _ _ → tt𝟙
        ; _*ᴿᴰ_ = λ _ _ → tt𝟙
        }

      open InResSortsᴰ base triv-sᴰ triv-bᴰ rsorts resourced rsᴰ

      rdᴰ : ResCtorsᴰ
      rdᴰ = record
        { 0ᵗᴰ       = λ _ _ → tt
        ; +ᴿ-commᴰ  = refl ; +ᴿ-assocᴰ = refl ; +ᴿ-0ᴰ = refl ; *ᴿ-assocᴰ = refl
        ; idᴿᴰ      = λ h → h
        ; _∘ᴿᴰ_     = λ sH tH h → tH (sH h)
        ; ∙ᴿᴰ       = tt𝟙 ; +ᴿ-∙ᴰ = refl ; *ᴿ-∙ᴰ = refl ; ∃!∙ᴿᴰ = λ _ → refl
        ; εᴿᴰ       = λ {_} {_} {Γᴿ} {_} _ →
            sym (trans (sym *ᴿ-assoc) (cong (_*ᴿ Γᴿ) *r-0l))
        ; _[_]ᴿᴰ    = λ _ _ → tt
        ; _▷ᴿᴰ[_]_  = λ _ _ _ → tt𝟙
        ; ext+ᴰ = refl ; ext*ᴰ = refl
        ; projᶜᴰ = λ _ → tt𝟙 ; proj-ηᴰ = λ _ → refl ; projᶜ-βᴰ = refl
        ; pᴿᴰ       = λ h →
            trans (ap-▷ᴿ h (sym *r-0l)) ext*
        ; qᴿᴰ       = tt
        ; _,ᴿᴰ[_]_  = λ σH ρ₀' {_} _ h →
            let step = trans h (sym ext*)
                dz = trans (sym projᶜ-β) (trans (cong projᶜ step) projᶜ-β)
                rz = trans (sym projʳ-β) (trans (cong projʳ step) projʳ-β)
                ρ0 = trans rz *r-0l
                gz = σH dz
            in trans (ap-+ᴿ gz (ap-*ᴿ ρ0 refl))
                     (sym (trans *ᴿ-distl (ap-+ᴿ refl
                       (trans (sym *ᴿ-assoc) (ap-*ᴿ *r-0l refl)))))
        ; lamᴿᴰ     = λ _ → tt ; appᴿᴰ = λ _ → tt
        }

      nᴰ : Totalᴰ syn
      nᴰ = record { sortsᴰ = triv-sᴰ ; baseᴰ = triv-bᴰ ; rsortsᴰ = rsᴰ ; resourcedᴰ = rdᴰ }

      module E = Elim nᴰ
