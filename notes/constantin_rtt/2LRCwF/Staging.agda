{-# OPTIONS --type-in-type --lossy-unification #-}
module 2LRCwF.Staging where

open import Utils
open import Data.Product using (Σ; _×_; proj₁; proj₂) renaming (_,_ to _,,_)
open import Data.Unit renaming (⊤ to 𝟙; tt to tt𝟙)
open import 2LRCwF.Model public
import RCwF.Model as RCwFM
import RCwF.Properties

-- Here we define a staging model for 2LRCwF.
--
-- In particular, we make a model of 2LRCwF in presheaves over the syntax of RCwF.
-- Since RCwF is a refinement of CwF (in the sense of functors as refinement type systems)
-- the base 2LCwF is just the usual staging model (presheaves over base object syntax).
--
-- The refinement functor for RCwF is injective, which means that the sorts of the refinements
-- are in Prop. So for the presheaf model, we implement resourced contexts
-- as displayed Prop-valued presheaves over the base presheaf contexts.
--
-- Overall, let O be the object RCwF syntax, consisting of Oᴮ base (CwF) and Oᴿ
-- resources (RCwF refinement).
--
-- Then, the 2LRCwF is implemented as:
--   Base = presheaves over Oᴮ
--   Resourced = presheaves over Oᴿ, displayed over the base
--
-- The resourced refinement involves some monoidal structure. In particular, the
-- RCwF definition requires that contexts form an R-module for a semiring R.
-- We must therefore mirror this structure in the presheaf model. We do this by:
--
-- 1. Making the model *contextual*, meaning that (base & resourced) semantic
--    contexts are always extensions of the empty context. This means that we
--    can define the semimodule operations by induction on semantic contexts.
--
-- 2. Using the universal property of the monoidal structure to inherit it in
--    the presheaf model. This looks kind of similar to a Day convolution, but not
--    really. (see the construction below for more details)


module StagingOver {D : SemiringBase} {S : InSemiringBase.SemiringAxioms D} where
  open InSemiringBase D
  open InSemiringBase.SemiringAxioms S
  open RCwF.Properties.Over {D} {S}
  private module QM = RCwFM.Over S
  open QM.InBaseSorts (QM.Total.sorts syn)
  open QM.InResSorts (QM.Total.base syn) (QM.Total.rsorts syn)

  -- Base contexts
  data ConP : Set

  variable
    ΓP ΔP ΘP ΞP : ConP

  -- Interpreting base contexts as sets
  ⟦_⟧ : ConP → Con → Set

  variable
    γ : ⟦ ΓP ⟧ Γ

  _⟪_⟫ : ⟦ ΓP ⟧ Δ → Sub Γ Δ → ⟦ ΓP ⟧ Γ
  ⟪id⟫ : (γ : ⟦ ΓP ⟧ Γ) → γ ⟪ id ⟫ ≡ γ
  ⟪∘⟫ : (γ : ⟦ ΓP ⟧ Θ) → γ ⟪ σ ∘ τ ⟫ ≡ (γ ⟪ σ ⟫) ⟪ τ ⟫

  -- Object-level types are just the Ty presheaf directly.
  record TyOP (ΓP : ConP) : Set where
    field
      ∣_∣ : ⟦ ΓP ⟧ Γ → Ty Γ
      nat : ∣ γ ⟪ σ ⟫ ∣ ≡ (∣ γ ∣ [ σ ]T)

  -- Meta-level types carry a base and a resourced component. Both are stable
  -- under their respective substitutions. The resourced type must be dependent
  -- on modes, such that mode 0 has a section over the base.
  record TyMP (ΓP : ConP) : Set where
    field
      ∣_∣  : ⟦ ΓP ⟧ Γ → Set
      _⟨_⟩ : ∣ γ ∣ → (σ : Sub Γ Δ) → ∣ γ ⟪ σ ⟫ ∣
      ⟨id⟩ : (a : ∣ γ ∣) → (a ⟨ id ⟩) ≡[ cong ∣_∣ (⟪id⟫ γ) ] a
      ⟨∘⟩  : (a : ∣ γ ∣) → (a ⟨ σ ∘ τ ⟩) ≡[ cong ∣_∣ (⟪∘⟫ γ) ] ((a ⟨ σ ⟩) ⟨ τ ⟩)

      ∣_∣ᴿ  : (γ : ⟦ ΓP ⟧ Γ) → Conᴿ Γ → Mode → ∣ γ ∣ → Prop
      ∣_∣ᴿ0 : (m : ∣ γ ∣) → ∣ γ ∣ᴿ Γᴿ 0m m
      ∣_∣ᴿ-sub : (σ : Sub Δ Γ) → Subᴿ Δᴿ Γᴿ σ → (m : ∣ γ ∣) → ∣ γ ∣ᴿ Γᴿ μ m → ∣ γ ⟪ σ ⟫ ∣ᴿ Δᴿ μ (m ⟨ σ ⟩)

  open TyOP public
  open TyMP public

  -- Object-level terms
  record TmOP (ΓP : ConP) (AOP : TyOP ΓP) : Set where
    field
      ∣_∣ : (γ : ⟦ ΓP ⟧ Γ) → Tm Γ (∣ AOP ∣ γ)
      nat : ∣ γ ⟪ σ ⟫ ∣ ≡[ ap-Tm (nat AOP) ] (∣ γ ∣ [ σ ])

  -- Meta-level base terms
  record TmMP (ΓP : ConP) (AMP : TyMP ΓP) : Set where
    field
      ∣_∣ : (γ : ⟦ ΓP ⟧ Γ) → ∣ AMP ∣ γ
      nat : ∣ γ ⟪ σ ⟫ ∣ ≡ (_⟨_⟩ AMP (∣ γ ∣) σ)

  variable
    AOP BOP : TyOP ΓP
    AMP BMP : TyMP ΓP
  
  -- @@Todo: cleanup substP usages and use this instead.
  ap-TmᴿMP-mode : ∀ {AMP} {a : ∣ AMP ∣ γ} {μ ν : Mode} → μ ≡ ν → ∣ AMP ∣ᴿ γ Γᴿ μ a → ∣ AMP ∣ᴿ γ Γᴿ ν a
  ap-TmᴿMP-mode refl x = x

  -- Base substitutions
  record SubP (ΓP ΔP : ConP) : Set where
    field
      ∣_∣ : ⟦ ΓP ⟧ Γ → ⟦ ΔP ⟧ Γ
      nat : (γ : ⟦ ΓP ⟧ Δ) → ∣ γ ⟪ σ ⟫ ∣ ≡ (∣ γ ∣) ⟪ σ ⟫

  open TmOP public
  open TmMP public
  open SubP public

  variable
    σP τP δP : SubP ΓP ΔP
    aOP : TmOP ΓP AOP
    aMP : TmMP ΓP AMP

  -- Inductive definition of contexts

  data ConP where
    ∙P    : ConP
    _▷P_  : (ΓP : ConP) → TyOP ΓP → ConP
    _▷MP_ : (ΓP : ConP) → TyMP ΓP → ConP

  ⟦ ∙P ⟧ _ = 𝟙
  ⟦ ΓP ▷P AOP ⟧ Γ = Σ (⟦ ΓP ⟧ Γ) (λ γ → Tm Γ (∣ AOP ∣ γ))
  ⟦ ΓP ▷MP AMP ⟧ Γ = Σ (⟦ ΓP ⟧ Γ) (λ γ → ∣ AMP ∣ γ)

  _⟪_⟫ {ΓP = ∙P} _ _ = tt𝟙
  _⟪_⟫ {ΓP = ΓP ▷P AOP} (γ ,, a) σ =
    (γ ⟪ σ ⟫ ,, coe (ap-Tm (sym (nat AOP))) (a [ σ ]))
  _⟪_⟫ {ΓP = ΓP ▷MP AMP} (γ ,, a) σ =
    (γ ⟪ σ ⟫ ,, _⟨_⟩ AMP a σ)

  ⟪id⟫ {∙P} tt𝟙 = refl
  ⟪id⟫ {ΓP ▷P AOP} (γ ,, a) = Σ≡ (⟪id⟫ γ) (trans (splitl refl) [id])
  ⟪id⟫ {ΓP ▷MP AMP} (γ ,, a) = Σ≡ (⟪id⟫ γ) (⟨id⟩ AMP a)

  ⟪∘⟫ {∙P} tt𝟙 = refl
  ⟪∘⟫ {ΓP ▷P AOP} {τ = τ} (γ ,, a) =
    let module AOPm = TyOP AOP
        pathR₂ = ap-Tm (cong (_[ τ ]T) (sym AOPm.nat))
        pathQ₃ = ap-Tm (sym AOPm.nat)
    in Σ≡ (⟪∘⟫ γ)
      (trans (splitl refl)
      (trans (sym (splitl refl))
      (trans (cong (coe (trans pathR₂ pathQ₃)) [∘])
      (trans (sym (splitl {p = pathR₂} refl))
             (cong (coe pathQ₃) (sym (undep (splitr (ap-[] refl refl (dep AOPm.nat) reflᴰ (splitl reflᴰ))))))))))
  ⟪∘⟫ {ΓP ▷MP AMP} (γ ,, a) = Σ≡ (⟪∘⟫ γ) (⟨∘⟩ AMP a)

  -- Resourced contexts
  -- These are basically vectors of values from R
  --
  -- The module operations are defined by induction,
  -- so they all hold definitionally

  data ConᴿP : ConP → Set where
    ∙ᴿP      : ConᴿP ∙P
    _▷ᴿP[_]  : ConᴿP ΓP → R → ConᴿP (ΓP ▷P AOP)
    _▷ᴿMP[_] : ConᴿP ΓP → R → ConᴿP (ΓP ▷MP AMP)

  variable
    ΓᴿP ΔᴿP ΘᴿP : ConᴿP ΓP

  _+ᴿP_ : ConᴿP ΓP → ConᴿP ΓP → ConᴿP ΓP
  ∙ᴿP +ᴿP ∙ᴿP = ∙ᴿP
  (ΓᴿP ▷ᴿP[ ρ ]) +ᴿP (ΔᴿP ▷ᴿP[ π ]) = (ΓᴿP +ᴿP ΔᴿP) ▷ᴿP[ ρ +r π ]
  (ΓᴿP ▷ᴿMP[ ρ ]) +ᴿP (ΔᴿP ▷ᴿMP[ π ]) = (ΓᴿP +ᴿP ΔᴿP) ▷ᴿMP[ ρ +r π ]

  _*ᴿP_ : R → ConᴿP ΓP → ConᴿP ΓP
  ρ *ᴿP ∙ᴿP = ∙ᴿP
  ρ *ᴿP (ΓᴿP ▷ᴿP[ π ]) = (ρ *ᴿP ΓᴿP) ▷ᴿP[ ρ *r π ]
  ρ *ᴿP (ΓᴿP ▷ᴿMP[ π ]) = (ρ *ᴿP ΓᴿP) ▷ᴿMP[ ρ *r π ]

  +ᴿP-assoc : (ΓᴿP ΔᴿP ΘᴿP : ConᴿP ΓP) → (ΓᴿP +ᴿP ΔᴿP) +ᴿP ΘᴿP ≡ ΓᴿP +ᴿP (ΔᴿP +ᴿP ΘᴿP)
  +ᴿP-assoc ∙ᴿP ∙ᴿP ∙ᴿP = refl
  +ᴿP-assoc (ΓᴿP ▷ᴿP[ ρ ]) (ΔᴿP ▷ᴿP[ π ]) (ΘᴿP ▷ᴿP[ ξ ]) =
    cong₂ _▷ᴿP[_] (+ᴿP-assoc ΓᴿP ΔᴿP ΘᴿP) +r-assoc
  +ᴿP-assoc (ΓᴿP ▷ᴿMP[ ρ ]) (ΔᴿP ▷ᴿMP[ π ]) (ΘᴿP ▷ᴿMP[ ξ ]) =
    cong₂ _▷ᴿMP[_] (+ᴿP-assoc ΓᴿP ΔᴿP ΘᴿP) +r-assoc

  +ᴿP-comm : (ΓᴿP ΔᴿP : ConᴿP ΓP) → ΓᴿP +ᴿP ΔᴿP ≡ ΔᴿP +ᴿP ΓᴿP
  +ᴿP-comm ∙ᴿP ∙ᴿP = refl
  +ᴿP-comm (ΓᴿP ▷ᴿP[ ρ ]) (ΔᴿP ▷ᴿP[ π ]) =
    cong₂ _▷ᴿP[_] (+ᴿP-comm ΓᴿP ΔᴿP) +r-comm
  +ᴿP-comm (ΓᴿP ▷ᴿMP[ ρ ]) (ΔᴿP ▷ᴿMP[ π ]) =
    cong₂ _▷ᴿMP[_] (+ᴿP-comm ΓᴿP ΔᴿP) +r-comm

  +ᴿP-0 : (ΓᴿP ΔᴿP : ConᴿP ΓP) → (0r *ᴿP ΓᴿP) +ᴿP ΔᴿP ≡ ΔᴿP
  +ᴿP-0 ∙ᴿP ∙ᴿP = refl
  +ᴿP-0 (ΓᴿP ▷ᴿP[ ρ ]) (ΔᴿP ▷ᴿP[ π ]) = cong₂ _▷ᴿP[_] (+ᴿP-0 ΓᴿP ΔᴿP) (trans (cong (_+r π) *r-0l) +r-0)
  +ᴿP-0 (ΓᴿP ▷ᴿMP[ ρ ]) (ΔᴿP ▷ᴿMP[ π ]) = cong₂ _▷ᴿMP[_] (+ᴿP-0 ΓᴿP ΔᴿP) (trans (cong (_+r π) *r-0l) +r-0)

  *ᴿP-assoc : (ρ π : R) (ΓᴿP : ConᴿP ΓP) → (ρ *r π) *ᴿP ΓᴿP ≡ ρ *ᴿP (π *ᴿP ΓᴿP)
  *ᴿP-assoc ρ π ∙ᴿP = refl
  *ᴿP-assoc ρ π (ΓᴿP ▷ᴿP[ ξ ]) = cong₂ _▷ᴿP[_] (*ᴿP-assoc ρ π ΓᴿP) *r-assoc
  *ᴿP-assoc ρ π (ΓᴿP ▷ᴿMP[ ξ ]) = cong₂ _▷ᴿMP[_] (*ᴿP-assoc ρ π ΓᴿP) *r-assoc

  projᶜP : ConᴿP (ΓP ▷P AOP) → ConᴿP ΓP
  projᶜP (ΓᴿP ▷ᴿP[ _ ]) = ΓᴿP

  projʳP : ConᴿP (ΓP ▷P AOP) → R
  projʳP (_ ▷ᴿP[ ρ ]) = ρ

  proj-ηP : (Γᴿ : ConᴿP (ΓP ▷P AOP)) → Γᴿ ≡ projᶜP Γᴿ ▷ᴿP[ projʳP Γᴿ ]
  proj-ηP (_ ▷ᴿP[ _ ]) = refl

  projᶜMP : ConᴿP (ΓP ▷MP AMP) → ConᴿP ΓP
  projᶜMP (ΓᴿP ▷ᴿMP[ _ ]) = ΓᴿP

  projʳMP : ConᴿP (ΓP ▷MP AMP) → R
  projʳMP (_ ▷ᴿMP[ ρ ]) = ρ

  proj-ηMP : (Γᴿ : ConᴿP (ΓP ▷MP AMP)) → Γᴿ ≡ projᶜMP Γᴿ ▷ᴿMP[ projʳMP Γᴿ ]
  proj-ηMP (_ ▷ᴿMP[ _ ]) = refl

  ∃!∙ᴿP : (Γᴿ : ConᴿP ∙P) → Γᴿ ≡ ∙ᴿP
  ∃!∙ᴿP ∙ᴿP = refl

  -- Interpreting resourced contexts as propositions
  --
  -- The propositions encode what object resource constraints must hold at each
  -- presheaf context. i.e. the empty context needs no resources, an extended
  -- context needs a split of resources, one for the tail substitution and one
  -- for the term.
  --
  -- This is a semantic version of the universal property of resourced context extension:
  --
  --    Subᴿ Γᴿ (Δᴿ ▷[ρ] A) (σ,a) ≃ ∃ Γᴿ₁ Γᴿ₂ . Γᴿ = Γᴿ₁ + ρ*Γᴿ₂ ∧ Subᴿ Γᴿ₁ Δᴿ σ ∧ Tmᴿ Γᴿ₂ A[σ] a 
  --
  -- This is admissible in the syntax, though we do not explicitly include it because
  -- it makes the presheaf model simpler. Since this isomorphism is Prop-valued,
  -- the coherences are trivial.

  ⟦_⟧ᴿ : ConᴿP ΓP → ⟦ ΓP ⟧ Γ → Conᴿ Γ → Prop

  ⟦ ∙ᴿP ⟧ᴿ tt𝟙 Γᴿ = (Γᴿ ≡ 0r *ᴿ Γᴿ)

  -- @@Todo: cleanup usage of ∃..

  ⟦ _▷ᴿP[_] {AOP = AOP} ΓᴿP ρ ⟧ᴿ (γ ,, a) Γᴿ =
    ∃P (Conᴿ _ × Conᴿ _) λ { (Γᴿ₁ ,, Γᴿ₂) →
      ΣProp ((Γᴿ₁ +ᴿ (ρ *ᴿ Γᴿ₂)) ≡ Γᴿ) λ _ →
      ΣProp (⟦ ΓᴿP ⟧ᴿ γ Γᴿ₁) λ _ →
      Tmᴿ Γᴿ₂ (mode ρ) (∣ AOP ∣ γ) a }

  ⟦ _▷ᴿMP[_] {AMP = AMP} ΓᴿP ρ ⟧ᴿ (γ ,, a) Γᴿ =
    ∃P (Conᴿ _ × Conᴿ _) λ { (Γᴿ₁ ,, Γᴿ₂) →
      ΣProp ((Γᴿ₁ +ᴿ (ρ *ᴿ Γᴿ₂)) ≡ Γᴿ) λ _ →
      ΣProp (⟦ ΓᴿP ⟧ᴿ γ Γᴿ₁) λ _ →
      ∣ AMP ∣ᴿ γ Γᴿ₂ (mode ρ) a }

  -- Some lemmas about resourced contexts

  -- Any zeroed context needs no resources

  0ᴿP-is-∙ᴿ : (γ : ⟦ ΓP ⟧ Γ) (Γᴿ : Conᴿ Γ)
             → ⟦ 0r *ᴿP ΓᴿP ⟧ᴿ γ Γᴿ → Γᴿ ≡ 0r *ᴿ Γᴿ
  0ᴿP-is-∙ᴿ {∙P} {ΓᴿP = ∙ᴿP} tt𝟙 Γᴿ h = h
  0ᴿP-is-∙ᴿ {ΓP ▷P AOP} {ΓᴿP = ΓᴿP ▷ᴿP[ ρ ]} (γ ,, a) Γᴿ h =
    ∃P-elim (λ { (Γᴿ₁ ,, Γᴿ₂) (eq ,P (tail ,P _)) →
      let ih = 0ᴿP-is-∙ᴿ γ Γᴿ₁ tail
          fwd : Γᴿ ≡ (0r *ᴿ Γᴿ₁) +ᴿ (0r *ᴿ Γᴿ₂)
          fwd = trans (sym eq) (cong₂ _+ᴿ_ ih (cong (_*ᴿ Γᴿ₂) *r-0l))
          bwd : 0r *ᴿ Γᴿ ≡ (0r *ᴿ Γᴿ₁) +ᴿ (0r *ᴿ Γᴿ₂)
          bwd = trans (cong (0r *ᴿ_) (sym eq))
                (trans *ᴿ-distl
                (cong ((0r *ᴿ Γᴿ₁) +ᴿ_) (trans (sym *ᴿ-assoc) (cong (_*ᴿ Γᴿ₂) *r-0l))))
      in trans fwd (sym bwd)
    }) h
  0ᴿP-is-∙ᴿ {ΓP ▷MP AMP} {ΓᴿP = ΓᴿP ▷ᴿMP[ ρ ]} (γ ,, a) Γᴿ h =
    ∃P-elim (λ { (Γᴿ₁ ,, Γᴿ₂) (eq ,P (tail ,P _)) →
      let ih = 0ᴿP-is-∙ᴿ γ Γᴿ₁ tail
          fwd : Γᴿ ≡ (0r *ᴿ Γᴿ₁) +ᴿ (0r *ᴿ Γᴿ₂)
          fwd = trans (sym eq) (cong₂ _+ᴿ_ ih (cong (_*ᴿ Γᴿ₂) *r-0l))
          bwd : 0r *ᴿ Γᴿ ≡ (0r *ᴿ Γᴿ₁) +ᴿ (0r *ᴿ Γᴿ₂)
          bwd = trans (cong (0r *ᴿ_) (sym eq))
                (trans *ᴿ-distl
                (cong ((0r *ᴿ Γᴿ₁) +ᴿ_) (trans (sym *ᴿ-assoc) (cong (_*ᴿ Γᴿ₂) *r-0l))))
      in trans fwd (sym bwd)
    }) h


  -- Resourced object substitution action on resourced contexts
  ⟦⟧ᴿ-base-sub : (ΓᴿP : ConᴿP ΓP) {γ : ⟦ ΓP ⟧ Δ} 
    → ⟦ ΓᴿP ⟧ᴿ γ Γᴿ → {Δᴿ : Conᴿ Γ} (σ : Sub Γ Δ) → Subᴿ Δᴿ Γᴿ σ
    → ⟦ ΓᴿP ⟧ᴿ (γ ⟪ σ ⟫) Δᴿ
  ⟦⟧ᴿ-base-sub ∙ᴿP h σ σᴿ = sub-zero σᴿ h
  ⟦⟧ᴿ-base-sub (_▷ᴿP[_] {AOP = AOP} ΓᴿP ρ) {γ = γ ,, a} h {Δᴿ} σ σᴿ =
    ∃P-elim (λ { (Γᴿ₁ ,, Γᴿ₂) (eq ,P (tail ,P aᴿ)) →
      ∃P-elim (λ { (Δ₁ ,, Δ₂) (Δeq ,P (σᴿ₁ ,P σᴿ₂)) →
        go (mode ρ) refl Γᴿ₂ Δ₁ Δ₂ Δeq σᴿ₂ (⟦⟧ᴿ-base-sub ΓᴿP tail σ σᴿ₁) aᴿ
      }) (sub-split-+ σᴿ Γᴿ₁ (ρ *ᴿ Γᴿ₂) eq)
    }) h
    where
      go : ∀ μ → mode ρ ≡ μ
        → ∀ Γᴿ₂ Δ₁ Δ₂ → Δ₁ +ᴿ Δ₂ ≡ Δᴿ → Subᴿ Δ₂ (ρ *ᴿ Γᴿ₂) σ
        → ⟦ ΓᴿP ⟧ᴿ (γ ⟪ σ ⟫) Δ₁ → Tmᴿ Γᴿ₂ μ (∣ AOP ∣ γ) a
        → ⟦ _▷ᴿP[_] {AOP = AOP} ΓᴿP ρ ⟧ᴿ ((γ ,, a) ⟪ σ ⟫) Δᴿ
      go 0m m0 Γᴿ₂ Δ₁ Δ₂ Δeq σᴿ₂ ih _ =
        let m0inv = mode-0-inj m0
            h0 = trans (ap-*ᴿ m0inv refl)
                       (sym (trans (sym *ᴿ-assoc) (ap-*ᴿ *r-0l refl)))
            sz = sub-zero σᴿ₂ h0
            ρeq = trans (ap-*ᴿ m0inv refl) (sym sz)
        in (Δ₁ ,, Δ₂) ,∃
          (trans (ap-+ᴿ refl ρeq) Δeq
          ,P (ih
          ,P ap-Tmᴿ-mode (sym m0) (0ᵗ _)))
      go 1m mρ Γᴿ₂ Δ₁ Δ₂ Δeq σᴿ₂ ih aᴿ =
        ∃P-elim (λ Δ₂' (star-eq ,P σᴿ₂') →
          (Δ₁ ,, Δ₂') ,∃
            (trans (ap-+ᴿ refl star-eq) Δeq
            ,P (ih
            ,P ap-Tmᴿ-mode (sym mρ)
                 (ap-Tmᴿ (sym (TyOP.nat AOP)) (aᴿ [ σᴿ₂' ]ᴿ))))
        ) (sub-split-* ρ mρ σᴿ₂ Γᴿ₂ refl)
  ⟦⟧ᴿ-base-sub (_▷ᴿMP[_] {AMP = AMP} ΓᴿP ρ) {γ = γ ,, a} h {Δᴿ} σ σᴿ =
    ∃P-elim (λ { (Γᴿ₁ ,, Γᴿ₂) (eq ,P (tail ,P aᴿ)) →
      ∃P-elim (λ { (Δ₁ ,, Δ₂) (Δeq ,P (σᴿ₁ ,P σᴿ₂)) →
        goM (mode ρ) refl Γᴿ₂ Δ₁ Δ₂ Δeq σᴿ₂ (⟦⟧ᴿ-base-sub ΓᴿP tail σ σᴿ₁) aᴿ
      }) (sub-split-+ σᴿ Γᴿ₁ (ρ *ᴿ Γᴿ₂) eq)
    }) h
    where
      goM : ∀ μ → mode ρ ≡ μ
        → ∀ Γᴿ₂ Δ₁ Δ₂ → Δ₁ +ᴿ Δ₂ ≡ Δᴿ → Subᴿ Δ₂ (ρ *ᴿ Γᴿ₂) σ
        → ⟦ ΓᴿP ⟧ᴿ (γ ⟪ σ ⟫) Δ₁ → ∣ AMP ∣ᴿ γ Γᴿ₂ μ a
        → ⟦ _▷ᴿMP[_] {AMP = AMP} ΓᴿP ρ ⟧ᴿ ((γ ,, a) ⟪ σ ⟫) Δᴿ
      goM 0m m0 Γᴿ₂ Δ₁ Δ₂ Δeq σᴿ₂ ih _ =
        let m0inv = mode-0-inj m0
            h0 = trans (ap-*ᴿ m0inv refl)
                       (sym (trans (sym *ᴿ-assoc) (ap-*ᴿ *r-0l refl)))
            sz = sub-zero σᴿ₂ h0
            ρeq = trans (ap-*ᴿ m0inv refl) (sym sz)
        in (Δ₁ ,, Δ₂) ,∃
          (trans (ap-+ᴿ refl ρeq) Δeq
          ,P (ih
          ,P ap-TmᴿMP-mode {AMP = AMP} (sym m0) (TyMP.∣ AMP ∣ᴿ0 _)))
      goM 1m mρ Γᴿ₂ Δ₁ Δ₂ Δeq σᴿ₂ ih aᴿ =
        ∃P-elim (λ Δ₂' (star-eq ,P σᴿ₂') →
          (Δ₁ ,, Δ₂') ,∃
            (trans (ap-+ᴿ refl star-eq) Δeq
            ,P (ih
            ,P ap-TmᴿMP-mode {AMP = AMP} (sym mρ)
                 (TyMP.∣ AMP ∣ᴿ-sub σ σᴿ₂' a aᴿ)))
        ) (sub-split-* ρ mρ σᴿ₂ Γᴿ₂ refl)

  -- Lemmas about meta-level terms:
  -- It says that e.g. if we have a term at the mode corresponding to resources
  -- ρ+π, then we have the term at a mode for resources ρ. In other words, + is
  -- monotonic, we can never get to 0 by adding together non-zero resources.

  metᴿ-from-+₁ : ∀ {a} (ρ π : R) → ∣ AMP ∣ᴿ γ Γᴿ (mode (ρ +r π)) a → ∣ AMP ∣ᴿ γ Γᴿ (mode ρ) a
  metᴿ-from-+₁ {AMP = AMP} {γ = γ} {Γᴿ = Γᴿ} {a = a} ρ π = go (mode ρ) refl
    where go : ∀ μ → mode ρ ≡ μ → ∣ AMP ∣ᴿ γ Γᴿ (mode (ρ +r π)) a → ∣ AMP ∣ᴿ γ Γᴿ μ a
          go 0m _ _ = ∣ AMP ∣ᴿ0 a
          go 1m eq x = ap-TmᴿMP-mode {AMP = AMP} (mode-+r {π = π} eq)  x

  metᴿ-from-+₂ : ∀ {a} (ρ π : R) → ∣ AMP ∣ᴿ γ Γᴿ (mode (ρ +r π)) a → ∣ AMP ∣ᴿ γ Γᴿ (mode π) a
  metᴿ-from-+₂ {AMP = AMP} {γ = γ} {Γᴿ = Γᴿ} {a = a} ρ π = go (mode π) refl
    where go : ∀ μ → mode π ≡ μ → ∣ AMP ∣ᴿ γ Γᴿ (mode (ρ +r π)) a → ∣ AMP ∣ᴿ γ Γᴿ μ a
          go 0m _ _ = ∣ AMP ∣ᴿ0 a
          go 1m eq x = ap-TmᴿMP-mode {AMP = AMP} (trans (cong mode +r-comm) (mode-+r eq)) x

  metᴿ-from-* : ∀ {a} (ρ π : R) → mode ρ ≡ 1m → ∣ AMP ∣ᴿ γ Γᴿ (mode (ρ *r π)) a → ∣ AMP ∣ᴿ γ Γᴿ (mode π) a
  metᴿ-from-* {AMP = AMP} {γ = γ} {Γᴿ = Γᴿ} {a = a} ρ π mρ = go (mode π) refl
    where go : ∀ μ → mode π ≡ μ → ∣ AMP ∣ᴿ γ Γᴿ (mode (ρ *r π)) a → ∣ AMP ∣ᴿ γ Γᴿ μ a
          go 0m _ _ = ∣ AMP ∣ᴿ0 a
          go 1m eq x = ap-TmᴿMP-mode {AMP = AMP} (mode-*r mρ eq) x

  -- Lemmas about semantic contexts:
  -- If we have a semantic context that is the sum of two contexts, then the
  -- object-level resourced context that provides it with resources can itself
  -- be split into two.

  bwd-+ : (ΓᴿP₁ ΓᴿP₂ : ConᴿP ΓP)
         → (γ : ⟦ ΓP ⟧ Γ) → (Γᴿ : Conᴿ Γ)
         → ⟦ ΓᴿP₁ +ᴿP ΓᴿP₂ ⟧ᴿ γ Γᴿ
         → ∃P (Conᴿ Γ × Conᴿ Γ) λ { (Γᴿ₁ ,, Γᴿ₂) →
             ΣProp ((Γᴿ₁ +ᴿ Γᴿ₂) ≡ Γᴿ) λ _ →
             ΣProp (⟦ ΓᴿP₁ ⟧ᴿ γ Γᴿ₁) λ _ →
             ⟦ ΓᴿP₂ ⟧ᴿ γ Γᴿ₂ }

  bwd-+ ∙ᴿP ∙ᴿP tt𝟙 Γᴿ h =
    (Γᴿ ,, Γᴿ) ,∃ (trans (cong (_+ᴿ Γᴿ) h) +ᴿ-0 ,P (h ,P h))

  bwd-+ (_▷ᴿP[_] {AOP = AOP} ΓᴿP₁ ρ) (_▷ᴿP[_] ΓᴿP₂ π) (γ ,, a) Γᴿ
    ((t ,, v) ,∃ (eq ,P (tail ,P tmr))) with bwd-+ ΓᴿP₁ ΓᴿP₂ γ t tail
  ... | ((t₁ ,, t₂) ,∃ (teq ,P (h₁ ,P h₂))) =
    let rearrange : (t₁ +ᴿ (ρ *ᴿ v)) +ᴿ (t₂ +ᴿ (π *ᴿ v)) ≡ Γᴿ
        rearrange =
          trans +ᴿ-assoc (trans (cong (t₁ +ᴿ_)
            (trans (sym +ᴿ-assoc) (trans (cong (_+ᴿ (π *ᴿ v)) +ᴿ-comm) +ᴿ-assoc)))
            (trans (sym +ᴿ-assoc) (trans (cong (_+ᴿ ((ρ *ᴿ v) +ᴿ (π *ᴿ v))) teq)
              (trans (cong (t +ᴿ_) (sym *ᴿ-distr)) eq))))
    in ((t₁ +ᴿ (ρ *ᴿ v)) ,, (t₂ +ᴿ (π *ᴿ v))) ,∃
      (rearrange
      ,P (((t₁ ,, v) ,∃ (refl ,P (h₁ ,P Tmᴿ-from-+₁ tmr)))
      ,P  ((t₂ ,, v) ,∃ (refl ,P (h₂ ,P Tmᴿ-from-+₂ tmr)))))

  bwd-+ (_▷ᴿMP[_] {AMP = AMP} ΓᴿP₁ ρ) (_▷ᴿMP[_] ΓᴿP₂ π) (γ ,, a) Γᴿ
    ((t ,, v) ,∃ (eq ,P (tail ,P tmr))) with bwd-+ ΓᴿP₁ ΓᴿP₂ γ t tail
  ... | ((t₁ ,, t₂) ,∃ (teq ,P (h₁ ,P h₂))) =
    let rearrange : (t₁ +ᴿ (ρ *ᴿ v)) +ᴿ (t₂ +ᴿ (π *ᴿ v)) ≡ Γᴿ
        rearrange =
          trans +ᴿ-assoc (trans (cong (t₁ +ᴿ_)
            (trans (sym +ᴿ-assoc) (trans (cong (_+ᴿ (π *ᴿ v)) +ᴿ-comm) +ᴿ-assoc)))
            (trans (sym +ᴿ-assoc) (trans (cong (_+ᴿ ((ρ *ᴿ v) +ᴿ (π *ᴿ v))) teq)
              (trans (cong (t +ᴿ_) (sym *ᴿ-distr)) eq))))
    in ((t₁ +ᴿ (ρ *ᴿ v)) ,, (t₂ +ᴿ (π *ᴿ v))) ,∃
      (rearrange
      ,P (((t₁ ,, v) ,∃ (refl ,P (h₁ ,P metᴿ-from-+₁ {AMP = AMP} ρ π tmr)))
      ,P  ((t₂ ,, v) ,∃ (refl ,P (h₂ ,P metᴿ-from-+₂ {AMP = AMP} ρ π tmr)))))

  -- Similar lemma for scaling

  bwd-* : (ρ : R) (mρ : mode ρ ≡ 1m) (ΓᴿP : ConᴿP ΓP)
         → (γ : ⟦ ΓP ⟧ Γ) → (Γᴿ : Conᴿ Γ)
         → ⟦ ρ *ᴿP ΓᴿP ⟧ᴿ γ Γᴿ
         → ∃P (Conᴿ Γ) λ Γᴿ' →
             ΣProp ((ρ *ᴿ Γᴿ') ≡ Γᴿ) λ _ →
             ⟦ ΓᴿP ⟧ᴿ γ Γᴿ'

  bwd-* ρ mρ ∙ᴿP tt𝟙 Γᴿ h =
    Γᴿ ,∃ (trans (cong (ρ *ᴿ_) h) (trans (sym *ᴿ-assoc) (trans (cong (_*ᴿ Γᴿ) *r-0r) (sym h))) ,P h)

  bwd-* ρ mρ (_▷ᴿP[_] {AOP = AOP} ΓᴿP π) (γ ,, a) Γᴿ
    ((t ,, v) ,∃ (eq ,P (tail ,P tmr))) with bwd-* ρ mρ ΓᴿP γ t tail
  ... | (tOP ,∃ (teq ,P h')) =
    let rearrange : ρ *ᴿ (tOP +ᴿ (π *ᴿ v)) ≡ Γᴿ
        rearrange =
          trans *ᴿ-distl (trans (cong (_+ᴿ (ρ *ᴿ (π *ᴿ v))) teq)
            (trans (cong (t +ᴿ_) (sym *ᴿ-assoc)) eq))
    in (tOP +ᴿ (π *ᴿ v)) ,∃
      (rearrange
      ,P ((tOP ,, v) ,∃ (refl ,P (h' ,P Tmᴿ-from-* mρ tmr))))

  bwd-* ρ mρ (_▷ᴿMP[_] {AMP = AMP} ΓᴿP π) (γ ,, a) Γᴿ
    ((t ,, v) ,∃ (eq ,P (tail ,P tmr))) with bwd-* ρ mρ ΓᴿP γ t tail
  ... | (tOP ,∃ (teq ,P h')) =
    let rearrange : ρ *ᴿ (tOP +ᴿ (π *ᴿ v)) ≡ Γᴿ
        rearrange =
          trans *ᴿ-distl (trans (cong (_+ᴿ (ρ *ᴿ (π *ᴿ v))) teq)
            (trans (cong (t +ᴿ_) (sym *ᴿ-assoc)) eq))
    in (tOP +ᴿ (π *ᴿ v)) ,∃
      (rearrange
      ,P ((tOP ,, v) ,∃ (refl ,P (h' ,P metᴿ-from-* {AMP = AMP} ρ π mρ tmr))))

  -- We can conclude the same thing if we relax the mode=1 requirement, but then
  -- we don't get any semantic context out.

  bwd-*-res : (ρ : R) (ΓᴿP : ConᴿP ΓP)
             → (γ : ⟦ ΓP ⟧ Γ) → (Γᴿ : Conᴿ Γ)
             → ⟦ ρ *ᴿP ΓᴿP ⟧ᴿ γ Γᴿ
             → ∃P (Conᴿ Γ) λ Γᴿ' →
                 (ρ *ᴿ Γᴿ') ≡ Γᴿ

  bwd-*-res ρ ∙ᴿP tt𝟙 Γᴿ h =
    Γᴿ ,∃ trans (cong (ρ *ᴿ_) h) (trans (sym *ᴿ-assoc) (trans (cong (_*ᴿ Γᴿ) *r-0r) (sym h)))

  bwd-*-res ρ (_▷ᴿP[_] ΓᴿP π) (γ ,, a) Γᴿ
    ((t ,, v) ,∃ (eq ,P (tail ,P tmr))) with bwd-*-res ρ ΓᴿP γ t tail
  ... | (tOP ,∃ teq) =
    (tOP +ᴿ (π *ᴿ v)) ,∃
      trans *ᴿ-distl (trans (cong (_+ᴿ (ρ *ᴿ (π *ᴿ v))) teq)
        (trans (cong (t +ᴿ_) (sym *ᴿ-assoc)) eq))

  bwd-*-res ρ (_▷ᴿMP[_] ΓᴿP π) (γ ,, a) Γᴿ
    ((t ,, v) ,∃ (eq ,P (tail ,P tmr))) with bwd-*-res ρ ΓᴿP γ t tail
  ... | (tOP ,∃ teq) =
    (tOP +ᴿ (π *ᴿ v)) ,∃
      trans *ᴿ-distl (trans (cong (_+ᴿ (ρ *ᴿ (π *ᴿ v))) teq)
        (trans (cong (t +ᴿ_) (sym *ᴿ-assoc)) eq))

  -- Resourced sorts: substitutions, object & meta terms
  -- Defined as usual

  record SubᴿP (ΓᴿP : ConᴿP ΓP) (ΔᴿP : ConᴿP ΔP) (σP : SubP ΓP ΔP) : Prop where
    field
      ∣_∣ : ⟦ ΓᴿP ⟧ᴿ γ Γᴿ → ⟦ ΔᴿP ⟧ᴿ (∣ σP ∣ γ) Γᴿ

  record TmᴿOP (ΓᴿP : ConᴿP ΓP) (μ : Mode) (AOP : TyOP ΓP) (aOP : TmOP ΓP AOP) : Prop where
    field
      ∣_∣ : ⟦ ΓᴿP ⟧ᴿ γ Γᴿ → Tmᴿ Γᴿ μ (∣ AOP ∣ γ) (∣ aOP ∣ γ)

  record TmᴿMP (ΓᴿP : ConᴿP ΓP) (μ : Mode) (AMP : TyMP ΓP) (aMP : TmMP ΓP AMP) : Prop where
    field
      ∣_∣ : ⟦ ΓᴿP ⟧ᴿ γ Γᴿ → ∣ AMP ∣ᴿ γ Γᴿ μ (∣ aMP ∣ γ)

  -- Some equality helpers

  private module TL = Over S

  opaque
    unfolding coe
    []-natural : ∀ {A B : Ty Δ} (p : A ≡ B) (a : Tm Δ A) (τ : Sub Γ Δ)
               → coe (ap-Tm p) a [ τ ] ≡ coe (ap-Tm (cong (_[ τ ]T) p)) (a [ τ ])
    []-natural refl a τ = refl

  opaque
    unfolding coe
    ap-metᴿ : {AMP : TyMP ΓP} {δ₁ δ₂ : ⟦ ΓP ⟧ Γ} {Γᴿ₁ Γᴿ₂ : Conᴿ Γ} {μ : Mode}
              {m : ∣ AMP ∣ δ₁}
            → (p : δ₁ ≡ δ₂) → (q : Γᴿ₁ ≡ Γᴿ₂)
            → ∣ AMP ∣ᴿ δ₁ Γᴿ₁ μ m
            → ∣ AMP ∣ᴿ δ₂ Γᴿ₂ μ (coe (cong (∣ AMP ∣) p) m)
    ap-metᴿ refl refl x = x


  -- Pointwise equality for each sort.
  -- Could turn this into OTT-style equality?

  record SubP-≡ {ΓP ΔP} (σ τ : SubP ΓP ΔP) : Set where
    field
      ∣_∣-≡ : ∀ {Γ} (γ : ⟦ ΓP ⟧ Γ) → SubP.∣ σ ∣ γ ≡ SubP.∣ τ ∣ γ

  record TyOP-≡ {ΓP} (A B : TyOP ΓP) : Set where
    field
      ∣_∣-≡ : ∀ {Γ} (γ : ⟦ ΓP ⟧ Γ) → ∣ A ∣ γ ≡ ∣ B ∣ γ

  record TmOP-≡ {ΓP AOP} (a b : TmOP ΓP AOP) : Set where
    field
      ∣_∣-≡ : ∀ {Γ} (γ : ⟦ ΓP ⟧ Γ) → TmOP.∣ a ∣ γ ≡ TmOP.∣ b ∣ γ

  record TmMP-≡ {ΓP} {AMP : TyMP ΓP} (a b : TmMP ΓP AMP) : Set where
    field
      ∣_∣-≡ : ∀ {Γ} (γ : ⟦ ΓP ⟧ Γ) → TmMP.∣ a ∣ γ ≡ TmMP.∣ b ∣ γ

  record TyMP-≡ {ΓP} (A B : TyMP ΓP) : Set where
    field
      ∣_∣-≡ : ∀ {Γ} (γ : ⟦ ΓP ⟧ Γ) → ∣ A ∣ γ ≡ ∣ B ∣ γ
      ⟨⟩-≡  : ∀ {Δ Γ} {γ : ⟦ ΓP ⟧ Δ} (a : ∣ A ∣ γ) (σ : Sub Γ Δ)
             → _⟨_⟩ A a σ ≡[ ∣_∣-≡ (γ ⟪ σ ⟫) ] _⟨_⟩ B (coe (∣_∣-≡ γ) a) σ
      ∣ᴿ-≡  : ∀ {Γ} (γ : ⟦ ΓP ⟧ Γ) (Γᴿ : Conᴿ Γ) (μ : Mode) (m : ∣ A ∣ γ)
             → ∣ A ∣ᴿ γ Γᴿ μ m ≡ ∣ B ∣ᴿ γ Γᴿ μ (coe (∣_∣-≡ γ) m)

  -- Conversion from equality records to propositional equality
  opaque
    unfolding coe

    fromSubP-≡ : {σ τ : SubP ΓP ΔP} → SubP-≡ σ τ → σ ≡ τ
    fromSubP-≡ {σ = σ} {τ = τ} e with ifunext (λ Γ → funext (SubP-≡.∣_∣-≡ e {Γ}))
    ... | refl = refl

    fromTyOP-≡ : {A B : TyOP ΓP} → TyOP-≡ A B → A ≡ B
    fromTyOP-≡ {A = A} {B = B} e with ifunext (λ Γ → funext (TyOP-≡.∣_∣-≡ e {Γ}))
    ... | refl = refl

    fromTmOP-≡ : {a b : TmOP ΓP AOP} → TmOP-≡ a b → a ≡ b
    fromTmOP-≡ {a = a} {b = b} e with ifunext (λ Γ → funext (TmOP-≡.∣_∣-≡ e {Γ}))
    ... | refl = refl

    fromTmMP-≡ : {AMP : TyMP ΓP} {a b : TmMP ΓP AMP} → TmMP-≡ a b → a ≡ b
    fromTmMP-≡ {a = a} {b = b} e with ifunext (λ Γ → funext (TmMP-≡.∣_∣-≡ e {Γ}))
    ... | refl = refl

    postulate fromTyMP-≡ : {A B : TyMP ΓP} → TyMP-≡ A B → A ≡ B

    ap-TmOP : AOP ≡ BOP → TmOP ΓP AOP ≡ TmOP ΓP BOP
    ap-TmOP refl = refl

    ap-TmMP : {AMP BMP : TyMP ΓP} → AMP ≡ BMP → TmMP ΓP AMP ≡ TmMP ΓP BMP
    ap-TmMP refl = refl

    TmOP-coe-∣∣ : (p : AOP ≡ BOP) (a : TmOP ΓP AOP)
      → ∀ {Γ} (γ : ⟦ ΓP ⟧ Γ)
      → TmOP.∣ a ∣ γ ≡[ ap-Tm (cong (λ T → ∣ T ∣ γ) p) ] TmOP.∣ coe (ap-TmOP p) a ∣ γ
    TmOP-coe-∣∣ refl a γ = refl

    TmMP-coe-∣∣ : {A B : TyMP ΓP}
      → (p : A ≡ B) (a : TmMP ΓP A)
      → ∀ {Γ} (γ : ⟦ ΓP ⟧ Γ)
      → TmMP.∣ a ∣ γ ≡[ cong (λ T → ∣ T ∣ γ) p ] TmMP.∣ coe (ap-TmMP p) a ∣ γ
    TmMP-coe-∣∣ refl a γ = refl

    TmMP-het-≡ : {A B : TyMP ΓP}
      → (p : A ≡ B) (a : TmMP ΓP A) (b : TmMP ΓP B)
      → (∀ {Γ} (γ : ⟦ ΓP ⟧ Γ) → TmMP.∣ a ∣ γ ≡[ cong (λ T → ∣ T ∣ γ) p ] TmMP.∣ b ∣ γ)
      → coe (ap-TmMP p) a ≡ b
    TmMP-het-≡ refl a b h = fromTmMP-≡ record { ∣_∣-≡ = λ γ → h γ }

    TmOP-het-≡ : (p : AOP ≡ BOP) (a : TmOP ΓP AOP) (b : TmOP ΓP BOP)
      → (∀ {Γ} (γ : ⟦ ΓP ⟧ Γ) → TmOP.∣ a ∣ γ ≡[ ap-Tm (cong (λ T → ∣ T ∣ γ) p) ] TmOP.∣ b ∣ γ)
      → coe (ap-TmOP p) a ≡ b
    TmOP-het-≡ refl a b h = fromTmOP-≡ record { ∣_∣-≡ = λ γ → h γ }

    ⟨⟩-natural :
      ∀ {ΔP : ConP} (AMP : TyMP ΔP)
      → ∀ {δ₁ δ₂ : ⟦ ΔP ⟧ Δ}
        (p : δ₁ ≡ δ₂) (a : ∣ AMP ∣ δ₁) (τ : Sub Γ Δ)
      → _⟨_⟩ AMP (coe (cong (∣ AMP ∣) p) a) τ
      ≡ coe (cong (λ δ → ∣ AMP ∣ (δ ⟪ τ ⟫)) p) (_⟨_⟩ AMP a τ)
    ⟨⟩-natural AMP refl a τ = refl

    ap-⟨⟩ : {A B : TyMP ΓP}
      → (p : ∀ {Γ} (γ : ⟦ ΓP ⟧ Γ) → ∣ A ∣ γ ≡ ∣ B ∣ γ)
      → (∀ {Δ Γ} {γ : ⟦ ΓP ⟧ Δ} (a : ∣ A ∣ γ) (σ : Sub Γ Δ)
         → coe (p (γ ⟪ σ ⟫)) (_⟨_⟩ A a σ) ≡ _⟨_⟩ B (coe (p γ) a) σ)
      → ∀ {Δ Γ} {γ : ⟦ ΓP ⟧ Δ} (a : ∣ A ∣ γ) (σ : Sub Γ Δ)
      → _⟨_⟩ A a σ ≡[ p (γ ⟪ σ ⟫) ] _⟨_⟩ B (coe (p γ) a) σ
    ap-⟨⟩ p h a σ = h a σ

  -- Meta type substitution coherence helpers

  opaque
    unfolding coe
    TmMP-sub-⟨id⟩ :
      ∀ {ΓP ΔP : ConP} (σP : SubP ΓP ΔP) (AMP : TyMP ΔP)
      → ∀ {Γ} (γ : ⟦ ΓP ⟧ Γ) (a : ∣ AMP ∣ (SubP.∣ σP ∣ γ)) →
        coe (cong (λ γ' → ∣ AMP ∣ (SubP.∣ σP ∣ γ')) (⟪id⟫ γ))
            (coe (cong (∣ AMP ∣) (sym (SubP.nat σP γ))) (_⟨_⟩ AMP a id))
        ≡ a
    TmMP-sub-⟨id⟩ σP AMP γ a =
      trans (splitl refl) (⟨id⟩ AMP a)

    TmMP-sub-⟨∘⟩ :
      ∀ {ΓP ΔP : ConP} (σP : SubP ΓP ΔP) (AMP : TyMP ΔP)
      → ∀ {Θ Δ} {σ : Sub Δ Θ} {Γ} {τ : Sub Γ Δ}
        (γ : ⟦ ΓP ⟧ Θ) (a : ∣ AMP ∣ (SubP.∣ σP ∣ γ)) →
        coe (cong (λ γ' → ∣ AMP ∣ (SubP.∣ σP ∣ γ')) (⟪∘⟫ γ))
            (coe (cong (∣ AMP ∣) (sym (SubP.nat σP γ))) (_⟨_⟩ AMP a (σ ∘ τ)))
        ≡ coe (cong (∣ AMP ∣) (sym (SubP.nat σP (γ ⟪ σ ⟫))))
              (_⟨_⟩ AMP (coe (cong (∣ AMP ∣) (sym (SubP.nat σP γ))) (_⟨_⟩ AMP a σ)) τ)
    TmMP-sub-⟨∘⟩ {ΓP} {ΔP} σP AMP {σ = σ} {τ = τ} γ a =
      let module σPm = SubP σP ; module AMPm = TyMP AMP
          pathR₂ = cong (λ δ → AMPm.∣_∣ (δ ⟪ τ ⟫)) (sym (σPm.nat γ))
          pathQ₃ = cong AMPm.∣_∣ (sym (σPm.nat (γ ⟪ σ ⟫)))
      in
      (trans (splitl refl)
      (trans (sym (splitl refl))
      (trans (cong (coe (trans pathR₂ pathQ₃)) (AMPm.⟨∘⟩ a))
      (trans (sym (splitl refl))
             (cong (coe pathQ₃) (sym (⟨⟩-natural AMP (sym (σPm.nat γ)) (AMPm._⟨_⟩ a σ) τ)))))))


  -- The sorts of the 2LRCwF object base.
  -- Basically the Yoneda embedding of object base syntax.
  objectSorts : QM.BaseSorts
  objectSorts = record { Con = ConP ; Sub = SubP ; Ty = TyOP ; Tm = TmOP }

  -- All the usual CwF stuff:

  idP : SubP ΓP ΓP
  idP = record { ∣_∣ = λ γ → γ ; nat = λ _ → refl }

  _∘P_ : SubP ΔP ΘP → SubP ΓP ΔP → SubP ΓP ΘP
  σ ∘P τ = record
    { ∣_∣ = λ γ → SubP.∣ σ ∣ (SubP.∣ τ ∣ γ)
    ; nat = λ γ → trans (cong (SubP.∣ σ ∣) (SubP.nat τ γ)) (SubP.nat σ _)
    }

  εP : SubP ΓP ∙P
  εP = record { ∣_∣ = λ _ → tt𝟙 ; nat = λ _ → refl }

  _[_]TP : TyOP ΔP → SubP ΓP ΔP → TyOP ΓP
  AOP [ σ ]TP = record
    { ∣_∣ = λ γ → ∣ AOP ∣ (SubP.∣ σ ∣ γ)
    ; nat = trans (cong (∣ AOP ∣) (SubP.nat σ _)) (nat AOP)
    }

  _[_]P : ∀ {ΔP ΓP} {AOP : TyOP ΔP} → TmOP ΔP AOP → (σ : SubP ΓP ΔP) → TmOP ΓP (AOP [ σ ]TP)
  _[_]P {AOP = AOP} a σ = record
    { ∣_∣ = λ γ → TmOP.∣ a ∣ (SubP.∣ σ ∣ γ)
    ; nat = transᴰ (congᴰ _ (λ δ → TmOP.∣ a ∣ δ) (SubP.nat σ _)) (TmOP.nat a)
    }

  pP : SubP (ΓP ▷P AOP) ΓP
  pP = record { ∣_∣ = λ (γ ,, a) → γ ; nat = λ _ → refl }

  qP : TmOP (ΓP ▷P AOP) (AOP [ pP ]TP)
  qP = record
    { ∣_∣ = λ (γ ,, a) → a
    ; nat = movel refl
    }

  _,,P_ : ∀ {ΓP ΔP} {AOP : TyOP ΔP} → (σ : SubP ΓP ΔP) → TmOP ΓP (AOP [ σ ]TP) → SubP ΓP (ΔP ▷P AOP)
  _,,P_ {AOP = AOP} σ a = record
    { ∣_∣ = λ γ → (SubP.∣ σ ∣ γ ,, TmOP.∣ a ∣ γ)
    ; nat = λ γ →
        Σ≡ (SubP.nat σ γ)
           (sym (symᴰ {p = ap-Tm (nat AOP)}
             (trans (splitl refl) (TmOP.nat a))))
    }

  UP : TyOP ΓP
  ∣ UP ∣ _ = U
  nat UP = sym U[]

  ElP : TmOP ΓP UP → TyOP ΓP
  ∣ ElP aOP ∣ γ = El (TmOP.∣ aOP ∣ γ)
  nat (ElP aOP) =
    trans (cong El (sym (symᴰ {p = sym (ap-Tm U[])} (TmOP.nat aOP)))) (sym El[])

  ΠP : R → (AOP : TyOP ΓP) → TyOP (ΓP ▷P AOP) → TyOP ΓP
  ∣ ΠP ρ AOP BOP ∣ γ =
    Π ρ (∣ AOP ∣ γ) (∣ BOP ∣ (γ ⟪ p ⟫ ,, coe (ap-Tm (sym (nat AOP))) q))
  nat (ΠP ρ AOP BOP) = trans (undep (ap-Π refl refl (dep (nat AOP))
    {! !})) (sym Π[])

  lamP : TmOP (ΓP ▷P AOP) BOP → TmOP ΓP (ΠP ρ AOP BOP)
  TmOP.∣ lamP {AOP = AOP} tOP ∣ γ =
    lam (TmOP.∣ tOP ∣ (γ ⟪ p ⟫ ,, coe (ap-Tm (sym (nat AOP))) q))
  TmOP.nat (lamP tOP) = {! !}

  appP : TmOP ΓP (ΠP ρ AOP BOP) → TmOP (ΓP ▷P AOP) BOP
  TmOP.∣ appP {AOP = AOP} {BOP = BOP} fOP ∣ {Γ} (γ ,, a) =
    let A = ∣ AOP ∣ γ
        sub : Sub Γ (Γ ▷ A)
        sub = id , coe (ap-Tm (sym [id]T)) a
        natA = TyOP.nat AOP
        fst-eq = trans (sym (⟪∘⟫ γ)) (trans (cong (γ ⟪_⟫) p∘,) (⟪id⟫ γ))
        step1 = []-natural (sym natA) q sub
        step2 = q[,] {_} {_} {id} {A} {coe (ap-Tm (sym [id]T)) a}
        step3 = transᴰ (dep (symᴰ [id])) [id]
        inner = splitl {p = ap-Tm (cong (_[ sub ]T) (sym natA))} (transᴰ step2 step3)
        snd-eq = splitl {p = ap-Tm (sym natA)} (substP (λ x → x ≡[ ap-Tm (trans (sym natA) (cong (∣ AOP ∣) fst-eq)) ] a) (sym step1) inner)
        ctx-eq : (γ ⟪ p ⟫ ,, coe (ap-Tm (sym natA)) q) ⟪ sub ⟫
               ≡ (γ ,, a)
        ctx-eq = Σ≡ fst-eq snd-eq
    in coe (ap-Tm (trans (sym (nat BOP)) (cong (∣ BOP ∣) ctx-eq)))
         (app (TmOP.∣ fOP ∣ γ) [ sub ])
  TmOP.nat (appP fOP) = {!!}

  -- Object laws

  opaque
    unfolding coe

    id∘P : idP ∘P σP ≡ σP
    id∘P = refl

    ∘idP : σP ∘P idP ≡ σP
    ∘idP = refl

    assocP : δP ∘P (σP ∘P τP) ≡ (δP ∘P σP) ∘P τP
    assocP = refl

    ∃!εP : εP ≡ σP
    ∃!εP = refl

    [id]TP : AOP [ idP ]TP ≡ AOP
    [id]TP = refl

    [∘]TP : AOP [ σP ∘P τP ]TP ≡ (AOP [ σP ]TP) [ τP ]TP
    [∘]TP = refl

    [id]OP : coe (ap-TmOP [id]TP) (aOP [ idP ]P) ≡ aOP
    [id]OP = refl

    [∘]OP : coe (ap-TmOP [∘]TP) (aOP [ σP ∘P τP ]P) ≡ (aOP [ σP ]P) [ τP ]P
    [∘]OP = refl

    p∘,P : pP ∘P (σP ,,P aOP) ≡ σP
    p∘,P = refl

    ,∘P : (σP ,,P aOP) ∘P τP ≡ ((σP ∘P τP) ,,P coe (ap-TmOP (sym [∘]TP)) (aOP [ τP ]P))
    ,∘P = refl

    p,qP : _,,P_ {AOP = AOP} pP qP ≡ idP
    p,qP = refl

    q[,]P : let ap-[]TP' = QM.InBaseSorts.BaseUtils.ap-[]T-impl objectSorts _[_]TP
            in coe (ap-TmOP (trans (sym [∘]TP) (ap-[]TP' p∘,P))) (qP [ σP ,,P aOP ]P) ≡ aOP -- ugly, fixme
    q[,]P = refl

    U[]P : UP [ σP ]TP ≡ UP
    U[]P = refl

    El[]P : (ElP aOP) [ σP ]TP ≡ ElP (coe (ap-TmOP U[]P) (aOP [ σP ]P))
    El[]P = refl

    ΠβP : (tOP : TmOP (ΓP ▷P AOP) BOP) → appP {ρ = ρ} (lamP tOP) ≡ tOP
    ΠβP {AOP = AOP} {BOP = BOP} tOP = fromTmOP-≡ record
      { ∣_∣-≡ = λ { {Γ} (γ ,, a) →
          let ctx = (γ ⟪ p ⟫ ,, coe (ap-Tm (sym (nat AOP))) q)
              sub : Sub Γ (Γ ▷ ∣ AOP ∣ γ)
              sub = id , coe (ap-Tm (sym [id]T)) a
              natA = TyOP.nat AOP
              fst-eq = trans (sym (⟪∘⟫ γ)) (trans (cong (γ ⟪_⟫) p∘,) (⟪id⟫ γ))
              step1 = []-natural (sym natA) q sub
              step2 = q[,] {_} {_} {id} {∣ AOP ∣ γ} {coe (ap-Tm (sym [id]T)) a}
              step3 = transᴰ (dep (symᴰ [id])) [id]
              inner = splitl {p = ap-Tm (cong (_[ sub ]T) (sym natA))} (transᴰ step2 step3)
              snd-eq = splitl {p = ap-Tm (sym natA)}
                (substP (λ x → x ≡[ ap-Tm (trans (sym natA) (cong (∣ AOP ∣) fst-eq)) ] a)
                  (sym step1) inner)
              ctx-eq = Σ≡ fst-eq snd-eq
          in trans (cong (coe _) (cong (_[ sub ]) (Πβ (TmOP.∣ tOP ∣ ctx))))
             (trans (cong (coe _) (sym (TmOP.nat tOP)))
             (trans (splitl (splitr refl))
                    (congᴰ _ (TmOP.∣ tOP ∣) ctx-eq)))
      } }

    ΠηP : (fOP : TmOP ΓP (ΠP ρ AOP BOP)) → lamP (appP fOP) ≡ fOP
    ΠηP fOP = {!!}

    Π[]P : (ΠP ρ AOP BOP) [ σP ]TP
         ≡ ΠP ρ (AOP [ σP ]TP) (BOP [ ((σP ∘P pP) ,,P coe (ap-TmOP (sym [∘]TP)) qP) ]TP)
    Π[]P {AOP = A₁} {BOP = B₁} {σP = σ₁} = fromTyOP-≡ record
      { ∣_∣-≡ = λ γ → cong (Π _ _) (cong (TyOP.∣ B₁ ∣)
          (Σ≡ (sym (SubP.nat σ₁ γ)) (splitl (splitr refl)))) }

    lam[]P : (tOP : TmOP (ΔP ▷P AOP) BOP)
           → (lamP {ρ = ρ} tOP) [ σP ]P ≡[ ap-TmOP Π[]P ]
             lamP (tOP [ ((σP ∘P pP) ,,P coe (ap-TmOP (sym [∘]TP)) qP) ]P)
    lam[]P {AOP = A₂} {BOP = B₂} {σP = σ₂} tOP =
      TmOP-het-≡ Π[]P _ _ (λ γ →
        let ceq = Σ≡ (sym (SubP.nat σ₂ γ)) (splitl (splitr refl))
        in ap-lam refl refl refl (dep (cong (TyOP.∣ B₂ ∣) ceq))
             (congᴰ _ (TmOP.∣ tOP ∣) ceq))

  -- Object constructors (Yoneda)

  objectBase : QM.InBaseSorts.BaseCtors objectSorts
  objectBase = record
    { id    = idP
    ; _∘_   = _∘P_
    ; id∘   = id∘P
    ; ∘id   = ∘idP
    ; assoc = assocP
    ; ∙     = ∙P
    ; ε     = εP
    ; ∃!ε   = ∃!εP
    ; _[_]T = _[_]TP
    ; [id]T = [id]TP
    ; [∘]T  = [∘]TP
    ; _[_]  = _[_]P
    ; [id]  = [id]OP
    ; [∘]   = [∘]OP
    ; _▷_   = λ ΓP AOP → ΓP ▷P AOP
    ; p     = pP
    ; q     = qP
    ; _,_   = _,,P_
    ; p∘,   = p∘,P
    ; ,∘    = ,∘P
    ; p,q   = p,qP
    ; q[,]  = q[,]P
    ; U     = UP
    ; El    = ElP
    ; U[]   = U[]P
    ; El[]  = El[]P
    ; Π     = ΠP
    ; lam   = lamP
    ; app   = appP
    ; Πβ    = ΠβP
    ; Πη    = ΠηP
    ; Π[]   = Π[]P
    ; lam[] = lam[]P
    }

  -- Now the resourced object sorts

  objectRSorts : QM.ResSorts objectSorts
  objectRSorts = record
    { Conᴿ = ConᴿP
    ; Subᴿ = SubᴿP
    ; Tmᴿ  = TmᴿOP
    ; _+ᴿ_ = _+ᴿP_
    ; _*ᴿ_ = _*ᴿP_
    }

  -- Resourced object constructors

  private module ObjRS = QM.InResSorts objectBase objectRSorts

  -- Define context extension by induction on mode, since 0 context extension
  -- really is different from non-0.
  ,ᴿ-helper : ∀ {AOP : TyOP ΔP} {σP : SubP ΓP ΔP} {aOP : TmOP ΓP (AOP [ σP ]TP)}
            {ΓᴿP : ConᴿP ΓP} {ΔᴿP : ConᴿP ΔP} {ΘᴿP : ConᴿP ΓP}
            → SubᴿP ΓᴿP ΔᴿP σP → (ρ : R)
            → TmᴿOP ΘᴿP (mode ρ) (AOP [ σP ]TP) aOP
            → SubᴿP (ΓᴿP +ᴿP (ρ *ᴿP ΘᴿP)) (ΔᴿP ▷ᴿP[ ρ ]) (σP ,,P aOP)
  ,ᴿ-helper {AOP = AOP} {σP = σP} {aOP = aOP} {ΓᴿP = ΓᴿP} {ΔᴿP = ΔᴿP} {ΘᴿP = ΘᴿP} σᴿ ρ tᴿ = record
    { ∣_∣ = λ {_} {γ} {Γᴿ} h →
        ∃P-elim (λ { (Γᴿ₁ ,, Γᴿ₂) (eq₁ ,P (h₁ ,P h₂)) →
          go (mode ρ) refl γ Γᴿ Γᴿ₁ Γᴿ₂ eq₁ h₁ h₂
        }) (bwd-+ ΓᴿP (ρ *ᴿP ΘᴿP) γ Γᴿ h)
    }
    where
      go : ∀ μ → mode ρ ≡ μ → ∀ {Γ} (γ : ⟦ _ ⟧ Γ) (Γᴿ : Conᴿ Γ) Γᴿ₁ Γᴿ₂
         → (Γᴿ₁ +ᴿ Γᴿ₂) ≡ Γᴿ → ⟦ ΓᴿP ⟧ᴿ γ Γᴿ₁ → ⟦ ρ *ᴿP ΘᴿP ⟧ᴿ γ Γᴿ₂
         → ⟦ _▷ᴿP[_] {AOP = AOP} ΔᴿP ρ ⟧ᴿ (SubP.∣ σP ∣ γ ,, TmOP.∣ aOP ∣ γ) Γᴿ
      go 0m meq γ Γᴿ Γᴿ₁ Γᴿ₂ eq₁ h₁ h₂ =
        ∃P-elim (λ { Γᴿ₂' eq₂ →
          (Γᴿ₁ ,, Γᴿ₂') ,∃
            (trans (cong (Γᴿ₁ +ᴿ_) eq₂) eq₁
            ,P (SubᴿP.∣ σᴿ ∣ h₁ ,P substP (λ μ → Tmᴿ Γᴿ₂' μ (∣ AOP ∣ (SubP.∣ σP ∣ γ)) (TmOP.∣ aOP ∣ γ)) (sym meq) (0ᵗ _)))
        }) (bwd-*-res ρ ΘᴿP γ Γᴿ₂ h₂)
      go 1m meq γ Γᴿ Γᴿ₁ Γᴿ₂ eq₁ h₁ h₂ =
        ∃P-elim (λ { Γᴿ₂' (eq₂ ,P h₂') →
          (Γᴿ₁ ,, Γᴿ₂') ,∃
            (trans (cong (Γᴿ₁ +ᴿ_) eq₂) eq₁
            ,P (SubᴿP.∣ σᴿ ∣ h₁ ,P TmᴿOP.∣ tᴿ ∣ h₂'))
        }) (bwd-* ρ meq ΘᴿP γ Γᴿ₂ h₂)

  pᴿP : ∀ {AOP : TyOP ΓP} → SubᴿP (_▷ᴿP[_] {AOP = AOP} ΓᴿP 0r) ΓᴿP pP
  SubᴿP.∣ pᴿP ∣ {γ = γ ,, a} h =
    ∃P-elim (λ { (Γᴿ₁ ,, Γᴿ₂) (eq ,P (tail ,P _)) →
      substP (⟦ _ ⟧ᴿ γ)
        (trans (sym +ᴿ-0) (trans +ᴿ-comm eq))
        tail }) h

  qᴿP : TmᴿOP (_▷ᴿP[_] {AOP = AOP} (0r *ᴿP ΓᴿP) 1r) 1m (AOP [ pP ]TP) qP
  TmᴿOP.∣ qᴿP ∣ {γ = γ ,, a} h =
    ∃P-elim (λ { (Γᴿ₁ ,, Γᴿ₂) (eq ,P (tail ,P tmr)) →
      substP (λ Γᴿ → Tmᴿ Γᴿ _ _ a)
        (trans (sym (trans (cong (_+ᴿ (1r *ᴿ Γᴿ₂)) (0ᴿP-is-∙ᴿ γ Γᴿ₁ tail))
          (trans (cong ((0r *ᴿ Γᴿ₁) +ᴿ_) *ᴿ-1) +ᴿ-0))) eq)
        (substP (λ μ → Tmᴿ Γᴿ₂ μ _ a) mode-1r tmr) }) h

  0ᵗP : (a : TmOP ΓP AOP) → TmᴿOP ΓᴿP 0m AOP a
  TmᴿOP.∣ 0ᵗP a ∣ _ = 0ᵗ _

  idᴿP : SubᴿP ΓᴿP ΓᴿP idP
  SubᴿP.∣ idᴿP ∣ h = h

  _∘ᴿP_ : SubᴿP ΓᴿP ΔᴿP σP → SubᴿP ΘᴿP ΓᴿP τP → SubᴿP ΘᴿP ΔᴿP (σP ∘P τP)
  SubᴿP.∣ σᴿ ∘ᴿP τᴿ ∣ h = SubᴿP.∣ σᴿ ∣ (SubᴿP.∣ τᴿ ∣ h)

  εᴿP : SubᴿP (0r *ᴿP ΓᴿP) ∙ᴿP εP
  SubᴿP.∣ εᴿP ∣ {γ = γ} h = 0ᴿP-is-∙ᴿ γ _ h

  _[_]ᴿP : TmᴿOP ΔᴿP μ AOP aOP → SubᴿP ΓᴿP ΔᴿP σP → TmᴿOP ΓᴿP μ (AOP [ σP ]TP) (aOP [ σP ]P)
  TmᴿOP.∣ tᴿ [ σᴿ ]ᴿP ∣ h = TmᴿOP.∣ tᴿ ∣ (SubᴿP.∣ σᴿ ∣ h)

  lamᴿP : ∀ {bOP : TmOP (ΓP ▷P AOP) BOP} → TmᴿOP (ΓᴿP ▷ᴿP[ ρ ]) 1m BOP bOP → TmᴿOP ΓᴿP 1m (ΠP ρ AOP BOP) (lamP bOP)
  TmᴿOP.∣ lamᴿP {AOP = AOP} {ρ = ρ} tᴿ ∣ {γ = γ} {Γᴿ = Γᴿ} h =
    let A = ∣ AOP ∣ γ
        Γᴿ₁ = Γᴿ ▷[ 0r ] A
        Γᴿ₂ = (0r *ᴿ Γᴿ) ▷[ 1r ] A
        tail' = ⟦⟧ᴿ-base-sub _ h p pᴿ
        tmr' = lower (ap-Tmᴿ (sym (TyOP.nat AOP)) (qᴿ {Γᴿ = Γᴿ})) (mode ρ)
        p1 = trans (sym ext*) (ap-▷ᴿ (trans (sym *ᴿ-assoc) (cong (_*ᴿ Γᴿ) *r-0r)) *r-1r)
        eq = trans (cong (Γᴿ₁ +ᴿ_) p1) (trans (sym ext+) (ap-▷ᴿ (trans +ᴿ-comm +ᴿ-0) +r-0))
        ext-h = (Γᴿ₁ ,, Γᴿ₂) ,∃ (eq ,P (tail' ,P tmr'))
    in lamᴿ (TmᴿOP.∣ tᴿ ∣ ext-h)

  appᴿP : ∀ {fOP : TmOP ΓP (ΠP ρ AOP BOP)} → TmᴿOP ΓᴿP 1m (ΠP ρ AOP BOP) fOP → TmᴿOP (ΓᴿP ▷ᴿP[ ρ ]) 1m BOP (appP fOP)
  TmᴿOP.∣ appᴿP {AOP = AOP} {BOP = BOP} fᴿ ∣ {γ = γ ,, a} {Γᴿ = Γᴿ}
    ((Γᴿ₁ ,, Γᴿ₂) ,∃ (eq ,P (tail ,P tmr))) =
    let A = ∣ AOP ∣ γ
        natA = TyOP.nat AOP
        sub = id , coe (ap-Tm (sym [id]T)) a
        fst-eq = trans (sym (⟪∘⟫ γ)) (trans (cong (γ ⟪_⟫) p∘,) (⟪id⟫ γ))
        step1' = []-natural (sym natA) q sub
        step2' = q[,] {_} {_} {id} {A} {coe (ap-Tm (sym [id]T)) a}
        step3' = transᴰ (dep (symᴰ [id])) [id]
        inner' = splitl {p = ap-Tm (cong (_[ sub ]T) (sym natA))} (transᴰ step2' step3')
        snd-eq = splitl {p = ap-Tm (sym natA)} (substP (λ x → x ≡[ ap-Tm (trans (sym natA) (cong (∣ AOP ∣) fst-eq)) ] a) (sym step1') inner')
        ctx-eq : (γ ⟪ p ⟫ ,, coe (ap-Tm (sym (TyOP.nat AOP))) q) ⟪ sub ⟫
               ≡ (γ ,, a)
        ctx-eq = Σ≡ fst-eq snd-eq
        fᴿ-result = TmᴿOP.∣ fᴿ ∣ tail
        app-result = appᴿ fᴿ-result
        subᴿ = ap-Subᴿ₁ eq (idᴿ ,ᴿ[ _ ] ap-Tmᴿ (sym [id]T) tmr)
        result = app-result [ subᴿ ]ᴿ
        eq-ty = trans (sym (TyOP.nat BOP)) (cong (∣ BOP ∣) ctx-eq)
    in ap-Tmᴿ eq-ty result

  -- Full object resourced CwF
  -- This should also be some kind of Yoneda embedding, but I'm not sure of the
  -- fully correct way to characterise it.

  objectResourced : ObjRS.ResCtors
  objectResourced = record
    { 0ᵗ        = 0ᵗP
    ; +ᴿ-comm   = +ᴿP-comm _ _
    ; +ᴿ-assoc  = +ᴿP-assoc _ _ _
    ; +ᴿ-0      = +ᴿP-0 _ _
    ; *ᴿ-assoc  = *ᴿP-assoc _ _ _
    ; idᴿ       = idᴿP
    ; _∘ᴿ_      = _∘ᴿP_
    ; ∙ᴿ        = ∙ᴿP
    ; +ᴿ-∙      = refl
    ; *ᴿ-∙      = refl
    ; ∃!∙ᴿ      = ∃!∙ᴿP
    ; εᴿ        = εᴿP
    ; _[_]ᴿ     = _[_]ᴿP
    ; _▷[_]_    = λ ΓᴿP ρ AOP → ΓᴿP ▷ᴿP[ ρ ]
    ; ext+      = refl
    ; ext*      = refl
    ; projᶜ     = projᶜP
    ; projʳ     = projʳP
    ; proj-η    = proj-ηP
    ; projᶜ-β   = refl
    ; projʳ-β   = refl
    ; pᴿ        = pᴿP
    ; qᴿ        = qᴿP
    ; _,ᴿ[_]_   = λ σᴿ ρ tᴿ → ,ᴿ-helper σᴿ ρ tᴿ
    ; lamᴿ      = lamᴿP
    ; appᴿ      = appᴿP
    }

  -- Now for the meta level

  metaSorts : TL.MetaSorts objectSorts
  metaSorts = record { TyM = TyMP ; TmM = TmMP }

  _[_]TM : TyMP ΔP → SubP ΓP ΔP → TyMP ΓP
  _[_]TM AMP σP =
      let module σPm = SubP σP ; module AMPm = TyMP AMP
      in record
      { ∣_∣   = λ γ → AMPm.∣_∣ (σPm.∣ γ ∣)
      ; _⟨_⟩  = λ a σ → coe (cong AMPm.∣_∣ (sym (σPm.nat _))) (AMPm._⟨_⟩ a σ)
      ; ⟨id⟩  = λ {_} {γ} a → TmMP-sub-⟨id⟩ σP AMP γ a
      ; ⟨∘⟩   = λ a → TmMP-sub-⟨∘⟩ σP AMP _ a
      ; ∣_∣ᴿ  = λ γ Γᴿ μ → AMPm.∣_∣ᴿ (σPm.∣ γ ∣) Γᴿ μ
      ; ∣_∣ᴿ0 = AMPm.∣_∣ᴿ0
      ; ∣_∣ᴿ-sub = λ σ σᴿ m mᴿ →
          ap-metᴿ {AMP = AMP} (sym (σPm.nat _)) refl (AMPm.∣_∣ᴿ-sub σ σᴿ m mᴿ)
      }

  _[_]MP : ∀ {ΔP ΓP} {AMP : TyMP ΔP} → TmMP ΔP AMP → (σP : SubP ΓP ΔP) → TmMP ΓP (AMP [ σP ]TM)
  TmMP.∣ _[_]MP aMP σP ∣ γ = TmMP.∣ aMP ∣ (SubP.∣ σP ∣ γ)
  TmMP.nat (_[_]MP {AMP = AMP} aMP σP) {γ = γ'} =
      sym (symᴰ {p = cong (∣ AMP ∣) (SubP.nat σP γ')}
        (trans (congᴰ (∣ AMP ∣) (λ δ → TmMP.∣ aMP ∣ δ) (SubP.nat σP γ'))
               (TmMP.nat aMP)))

  pMP : SubP (ΓP ▷MP AMP) ΓP
  SubP.∣ pMP ∣ (γ ,, a) = γ
  SubP.nat pMP _ = refl

  qMP : TmMP (ΓP ▷MP AMP) (AMP [ pMP ]TM)
  TmMP.∣ qMP ∣ (γ ,, a) = a
  TmMP.nat qMP = sym reflᴰ

  _,MP_ : ∀ {ΓP ΔP} {AMP : TyMP ΔP} → (σP : SubP ΓP ΔP) → TmMP ΓP (AMP [ σP ]TM) → SubP ΓP (ΔP ▷MP AMP)
  SubP.∣ σP ,MP aMP ∣ γ = (SubP.∣ σP ∣ γ ,, TmMP.∣ aMP ∣ γ)
  SubP.nat (σP ,MP aMP) γ = Σ≡ (SubP.nat σP γ) (movel (TmMP.nat aMP))

  CodeP : TyOP ΓP → TyMP ΓP
  ∣ CodeP AOP ∣ {Γ} γ = Tm Γ (∣ AOP ∣ γ)
  _⟨_⟩ (CodeP AOP) a σ = coe (ap-Tm (sym (nat AOP))) (a [ σ ])
  ⟨id⟩ (CodeP AOP) a = trans (splitl refl) [id]
  ⟨∘⟩ (CodeP AOP) {σ = σ} {τ = τ} a =
      let pathR₂ = ap-Tm (cong (_[ τ ]T) (sym (nat AOP)))
          pathQ₃ = ap-Tm (sym (nat AOP))
      in
      (trans (splitl refl)
      (trans (sym (splitl refl))
      (trans (cong (coe (trans pathR₂ pathQ₃)) [∘])
      (trans (sym (splitl refl))
             (cong (coe pathQ₃) (sym ([]-natural (sym (nat AOP)) (a [ σ ]) τ)))))))
  ∣ CodeP AOP ∣ᴿ γ Γᴿ μ a = Tmᴿ Γᴿ μ (∣ AOP ∣ γ) a
  ∣ CodeP AOP ∣ᴿ0 _ = 0ᵗ _
  ∣ CodeP AOP ∣ᴿ-sub σ σᴿ a aᴿ = ap-Tmᴿ (sym (nat AOP)) (aᴿ [ σᴿ ]ᴿ)

  <_>P : TmOP ΓP AOP → TmMP ΓP (CodeP AOP)
  TmMP.∣ < a >P ∣ γ = TmOP.∣ a ∣ γ
  TmMP.nat (<_>P {AOP = AOP} a) = sym (symᴰ {p = ap-Tm (nat AOP)} (TmOP.nat a))

  ~P_ : TmMP ΓP (CodeP AOP) → TmOP ΓP AOP
  TmOP.∣ ~P aMP ∣ γ = TmMP.∣ aMP ∣ γ
  TmOP.nat (~P_ {AOP = AOP} aMP) = movel (TmMP.nat aMP)

  opaque
    unfolding coe

    [id]TMP : (AMP [ idP ]TM) ≡ AMP
    [id]TMP = refl

    [id]MOP : coe (ap-TmMP [id]TMP) (aMP [ idP ]MP) ≡ aMP
    [id]MOP = refl

    p∘,MP : pMP ∘P (σP ,MP aMP) ≡ σP
    p∘,MP = refl

    p,qMP : _,MP_ {AMP = AMP} pMP qMP ≡ idP
    p,qMP = refl

    ~<>P : (a : TmOP ΓP AOP) → (~P < a >P) ≡ a
    ~<>P _ = refl

    <>~P : (t : TmMP ΓP (CodeP AOP)) → < ~P t >P ≡ t
    <>~P _ = refl

  opaque
    unfolding coe

    [∘]TMP-eq : TyMP-≡ (AMP [ σP ∘P τP ]TM) ((AMP [ σP ]TM) [ τP ]TM)
    TyMP-≡.∣_∣-≡ [∘]TMP-eq γ = refl
    TyMP-≡.⟨⟩-≡ ([∘]TMP-eq {AMP = AMP} {σP = σP} {τP = τP}) {γ = γ} a σ = sym (splitl (splitr refl))
    TyMP-≡.∣ᴿ-≡ [∘]TMP-eq γ Γᴿ μ m = refl

    Code[]P-eq : TyMP-≡ ((CodeP AOP) [ σP ]TM) (CodeP (AOP [ σP ]TP))
    TyMP-≡.∣_∣-≡ Code[]P-eq γ = refl
    TyMP-≡.⟨⟩-≡ (Code[]P-eq {AOP = AOP} {σP = σP}) {γ = γ} a σ =
      ap-⟨⟩ {A = (CodeP AOP) [ σP ]TM} {B = CodeP (AOP [ σP ]TP)}
        (λ γ → refl)
        (λ a σ →  splitr (splitl (splitl reflᴰ)))
        a σ
    TyMP-≡.∣ᴿ-≡ Code[]P-eq γ Γᴿ μ m = refl

  [∘]TMP : AMP [ σP ∘P τP ]TM ≡ (AMP [ σP ]TM) [ τP ]TM
  [∘]TMP = fromTyMP-≡ [∘]TMP-eq

  Code[]P : (CodeP AOP) [ σP ]TM ≡ CodeP (AOP [ σP ]TP)
  Code[]P = fromTyMP-≡ Code[]P-eq

  [∘]MOP : coe (ap-TmMP [∘]TMP) (aMP [ σP ∘P τP ]MP) ≡ (aMP [ σP ]MP) [ τP ]MP
  [∘]MOP = TmMP-het-≡ [∘]TMP _ _ (λ γ → reflᴰ)

  ,∘MP : (σP ,MP aMP) ∘P τP ≡ ((σP ∘P τP) ,MP coe (ap-TmMP (sym [∘]TMP)) (aMP [ τP ]MP))
  ,∘MP = fromSubP-≡ record { ∣_∣-≡ = λ γ → Σ≡ refl (trans reflᴰ (undep (TmMP-coe-∣∣ (sym [∘]TMP) _ γ))) }

  q[,]MP : let ap-[]TM' = TL.InMetaSorts.MetaUtils.ap-[]TM-impl objectSorts objectBase metaSorts _[_]TM
           in coe (ap-TmMP (trans (sym [∘]TMP) (ap-[]TM' p∘,MP))) (qMP [ σP ,MP aMP ]MP) ≡ aMP
  q[,]MP = TmMP-het-≡ (trans (sym [∘]TMP) refl) _ _ (λ γ → reflᴰ)

  <>[]P : coe (ap-TmMP Code[]P) (< aOP >P [ σP ]MP) ≡ < aOP [ σP ]P >P
  <>[]P = TmMP-het-≡ Code[]P _ _ (λ γ → reflᴰ)

  ~[]P : (~P aMP) [ σP ]P ≡ ~P (coe (ap-TmMP Code[]P) (aMP [ σP ]MP))
  ~[]P = fromTmOP-≡ record { ∣_∣-≡ = λ γ → undep (TmMP-coe-∣∣ Code[]P _ γ) }

  UMP : TyMP ΓP
  ∣ UMP ∣ _ = Set
  _⟨_⟩ UMP S _ = S
  ⟨id⟩ UMP _ = reflᴰ
  ⟨∘⟩ UMP _ = reflᴰ
  ∣ UMP ∣ᴿ _ _ _ _ = ⊤
  ∣ UMP ∣ᴿ0 _ = tt
  ∣ UMP ∣ᴿ-sub _ _ _ _ = tt

  ElMP : TmMP ΓP UMP → TyMP ΓP
  ∣ ElMP aMP ∣ γ = TmMP.∣ aMP ∣ γ
  _⟨_⟩ (ElMP aMP) x σ = coe (sym (TmMP.nat aMP)) x
  ⟨id⟩ (ElMP aMP) x = splitl reflᴰ
  ⟨∘⟩ (ElMP aMP) x = splitl (splitr (splitr reflᴰ))
  ∣ ElMP aMP ∣ᴿ _ _ _ _ = ⊤
  ∣ ElMP aMP ∣ᴿ0 _ = tt
  ∣ ElMP aMP ∣ᴿ-sub _ _ _ _ = tt

  ΠMP : R → (AMP : TyMP ΓP) → TyMP (ΓP ▷MP AMP) → TyMP ΓP
  ∣ ΠMP ρ AMP BMP ∣ {Γ} γ =
    ∀ {Γ'} (σ : Sub Γ' Γ) (a : ∣ AMP ∣ (γ ⟪ σ ⟫)) → ∣ BMP ∣ (γ ⟪ σ ⟫ ,, a)
  _⟨_⟩ (ΠMP {ΓP = ΓP} ρ AMP BMP) {γ = γ} f τ σ a =
    let eq = ⟪∘⟫ γ
        a' = coe (cong (∣ AMP ∣) (sym eq)) a
        result = f (τ ∘ σ) a'
    in coe (cong (∣ BMP ∣) (Σ≡ eq (splitl reflᴰ))) result
  ⟨id⟩ (ΠMP {ΓP = ΓP} ρ AMP BMP) {γ = γ} f = ifunext (λ _ → funext (λ σ → funext (λ x₁ → {! undep ?!})))
    -- ifunext (λ _ → funext (λ σ → funext (λ a → pw σ a)))
    -- where
    -- opaque
    --   unfolding coe
    --   pw : ∀ {Γ'} (σ : Sub Γ' _) (a : ∣ AMP ∣ (γ ⟪ σ ⟫))
    --      -- → coe (cong (∣ ΠMP ρ AMP BMP ∣) (⟪id⟫ γ)) (_⟨_⟩ (ΠMP ρ AMP BMP) f id) σ a ≡ f σ a
    --      → coe ({!!}) (_⟨_⟩ (ΠMP ρ AMP BMP) f id) σ a ≡ f σ a
    --   pw σ a = splitl (congᴰ {y = (σ ,, a)}
    --     (λ (δ : Σ (Sub _ _) (λ τ → ∣ AMP ∣ (γ ⟪ τ ⟫))) → ∣ BMP ∣ (γ ⟪ proj₁ δ ⟫ ,, proj₂ δ))
    --     (λ δ → f (proj₁ δ) (proj₂ δ))
    --     (Σ≡ id∘ (splitl (splitl reflᴰ))))
  ⟨∘⟩ (ΠMP {ΓP = ΓP} ρ AMP BMP) {_} {γ} {_} {σ₀} {_} {τ₀} f =
    ifunext (λ _ → funext (λ σ' → funext (λ a → pw σ' a)))
    where
    opaque
      unfolding coe
      pw : ∀ {Γ''} (σ' : Sub Γ'' _) (a : ∣ AMP ∣ (((γ ⟪ σ₀ ⟫) ⟪ τ₀ ⟫) ⟪ σ' ⟫))
         → coe (cong (∣ ΠMP ρ AMP BMP ∣) (⟪∘⟫ γ)) (_⟨_⟩ (ΠMP ρ AMP BMP) f (σ₀ ∘ τ₀)) σ' a
           ≡ _⟨_⟩ (ΠMP ρ AMP BMP) (_⟨_⟩ (ΠMP ρ AMP BMP) f σ₀) τ₀ σ' a
      pw σ' a = {!!}
  ∣ ΠMP ρ AMP BMP ∣ᴿ {Γ} γ Γᴿ μ f =
    ∀ {Δ} {Δᴿ : Conᴿ Δ} (σ : Sub Δ Γ) → Subᴿ Δᴿ Γᴿ σ
    → (Θᴿ : Conᴿ Δ)
    → (a : ∣ AMP ∣ (γ ⟪ σ ⟫))
    → ∣ AMP ∣ᴿ (γ ⟪ σ ⟫) Θᴿ (mode ρ) a
    → ∣ BMP ∣ᴿ (γ ⟪ σ ⟫ ,, a) (Δᴿ +ᴿ (ρ *ᴿ Θᴿ)) μ (f σ a)
  ∣ ΠMP ρ AMP BMP ∣ᴿ0 f σ σᴿ Θᴿ a aᴿ = ∣ BMP ∣ᴿ0 (f σ a)
  ∣ ΠMP ρ AMP BMP ∣ᴿ-sub {γ = γ} σ σᴿ f fᴿ τ τᴿ Θᴿ a aᴿ =
    ap-metᴿ {AMP = BMP} (Σ≡ (⟪∘⟫ γ) (splitl reflᴰ)) refl
      (fᴿ (σ ∘ τ) (σᴿ ∘ᴿ τᴿ) Θᴿ
        (coe (cong (∣ AMP ∣) (sym (⟪∘⟫ γ))) a)
        (ap-metᴿ {AMP = AMP} (sym (⟪∘⟫ γ)) refl aᴿ))

  lamMP : TmMP (ΓP ▷MP AMP) BMP → TmMP ΓP (ΠMP ρ AMP BMP)
  TmMP.∣ lamMP {AMP = AMP} tMP ∣ γ σ a = TmMP.∣ tMP ∣ (γ ⟪ σ ⟫ ,, a)
  TmMP.nat (lamMP {AMP = AMP} {BMP = BMP} tMP) {γ = γ} =
    ifunext (λ Γ' → funext (λ σ → funext (λ a →
      sym (congᴰ (∣ BMP ∣) (TmMP.∣ tMP ∣) (Σ≡ (⟪∘⟫ γ) (splitl reflᴰ))))))

  appMP : TmMP ΓP (ΠMP ρ AMP BMP) → TmMP (ΓP ▷MP AMP) BMP
  TmMP.∣ appMP {AMP = AMP} {BMP = BMP} fMP ∣ (γ ,, a) =
    let a' = coe (cong (∣ AMP ∣) (sym (⟪id⟫ γ))) a
    in coe (cong (∣ BMP ∣) (Σ≡ (⟪id⟫ γ) (splitl reflᴰ))) (TmMP.∣ fMP ∣ γ id a')
  TmMP.nat (appMP fMP) = {!!}

  opaque
    unfolding coe

    U[]MP : UMP [ σP ]TM ≡ UMP
    U[]MP = refl

    El[]MP : (ElMP aMP) [ σP ]TM ≡ ElMP (coe (ap-TmMP U[]MP) (aMP [ σP ]MP))
    El[]MP {aMP = aMP'} {σP = σP'} = fromTyMP-≡ record
      { ∣_∣-≡ = λ γ → refl
      ; ⟨⟩-≡  = λ a σ → splitr (splitr (splitl (splitl reflᴰ)))
      ; ∣ᴿ-≡  = λ γ Γᴿ μ m → refl
      }

    ΠβMP : (tMP : TmMP (ΓP ▷MP AMP) BMP) → appMP {ρ = ρ} (lamMP tMP) ≡ tMP
    ΠβMP {AMP = AMP} {BMP = BMP} tMP = fromTmMP-≡ record
      { ∣_∣-≡ = λ { (γ ,, a) →
          congᴰ (∣ BMP ∣) (TmMP.∣ tMP ∣) (Σ≡ (⟪id⟫ γ) (splitl reflᴰ)) } }

    ΠηMP : (fMP : TmMP ΓP (ΠMP ρ AMP BMP)) → lamMP (appMP fMP) ≡ fMP
    ΠηMP {AMP = AMP} {BMP = BMP} fMP = {!!}

    Π[]MP' : (ΠMP ρ AMP BMP) [ σP ]TM
           ≡ ΠMP ρ (AMP [ σP ]TM) (BMP [ ((σP ∘P pMP) ,MP coe (ap-TmMP (sym [∘]TMP)) qMP) ]TM)
    Π[]MP' = {!!}

    lam[]MP' : (tMP : TmMP (ΔP ▷MP AMP) BMP)
             → (lamMP {ρ = ρ} tMP) [ σP ]MP ≡[ ap-TmMP Π[]MP' ]
               lamMP (tMP [ ((σP ∘P pMP) ,MP coe (ap-TmMP (sym [∘]TMP)) qMP) ]MP)
    lam[]MP' = {!!}

  -- Meta base assembly
  -- This is basically the 'standard model' in presheaves

  metaCtors : TL.InMetaSorts.MetaCtors objectSorts objectBase metaSorts
  metaCtors = record
    { _[_]TM = _[_]TM
    ; [id]TM = [id]TMP
    ; [∘]TM  = [∘]TMP
    ; _[_]M  = _[_]MP
    ; [id]M  = [id]MOP
    ; [∘]M   = [∘]MOP
    ; _▷M_   = _▷MP_
    ; pM     = pMP
    ; qM     = qMP
    ; _,M_   = _,MP_
    ; p∘,M   = p∘,MP
    ; ,∘M    = ,∘MP
    ; p,qM   = p,qMP
    ; q[,]M  = q[,]MP
    ; UM     = UMP
    ; ElM    = ElMP
    ; U[]M   = U[]MP
    ; El[]M  = El[]MP
    ; ΠM     = ΠMP
    ; lamM   = lamMP
    ; appM   = appMP
    ; ΠβM    = ΠβMP
    ; ΠηM    = ΠηMP
    ; Π[]M   = Π[]MP'
    ; lam[]M = lam[]MP'
    ; Code    = CodeP
    ; Code[]  = Code[]P
    ; <_>     = <_>P
    ; ~_      = ~P_
    ; <>[]    = <>[]P
    ; ~[]     = ~[]P
    ; ~<>     = ~<>P
    ; <>~     = <>~P
    }

  -- Resourced meta
  -- This is the interesting part

  resMetaSorts : TL.ResMetaSorts objectBase metaSorts objectRSorts
  resMetaSorts = record { TmᴿM = TmᴿMP }

  -- A lot of this is very similar to the object resourced fragment, but we implement
  -- everything using semantic structure in presheaves rather than from object syntax.
  -- The splitting structure we derived earlier is what allows us to use e.g. a modified Kripke
  -- function space for a resourced meta Π that preserves object-level resources.

  ,ᴿM-helper : ∀ {AMP : TyMP ΔP} {σP : SubP ΓP ΔP} {aMP : TmMP ΓP (AMP [ σP ]TM)}
             {ΓᴿP : ConᴿP ΓP} {ΔᴿP : ConᴿP ΔP} {ΘᴿP : ConᴿP ΓP}
             → SubᴿP ΓᴿP ΔᴿP σP → (ρ : R)
             → TmᴿMP ΘᴿP (mode ρ) (AMP [ σP ]TM) aMP
             → SubᴿP (ΓᴿP +ᴿP (ρ *ᴿP ΘᴿP)) (ΔᴿP ▷ᴿMP[ ρ ]) (σP ,MP aMP)
  ,ᴿM-helper {AMP = AMP} {σP = σP} {aMP = aMP} {ΓᴿP = ΓᴿP} {ΔᴿP = ΔᴿP} {ΘᴿP = ΘᴿP} σᴿ ρ tᴿM = record
    { ∣_∣ = λ {_} {γ} {Γᴿ} h →
        ∃P-elim (λ { (Γᴿ₁ ,, Γᴿ₂) (eq₁ ,P (h₁ ,P h₂)) →
          go (mode ρ) refl γ Γᴿ Γᴿ₁ Γᴿ₂ eq₁ h₁ h₂
        }) (bwd-+ ΓᴿP (ρ *ᴿP ΘᴿP) γ Γᴿ h)
    }
    where
      go : ∀ μ → mode ρ ≡ μ → ∀ {Γ} (γ : ⟦ _ ⟧ Γ) (Γᴿ : Conᴿ Γ) Γᴿ₁ Γᴿ₂
         → (Γᴿ₁ +ᴿ Γᴿ₂) ≡ Γᴿ → ⟦ ΓᴿP ⟧ᴿ γ Γᴿ₁ → ⟦ ρ *ᴿP ΘᴿP ⟧ᴿ γ Γᴿ₂
         → ⟦ _▷ᴿMP[_] {AMP = AMP} ΔᴿP ρ ⟧ᴿ (SubP.∣ σP ∣ γ ,, TmMP.∣ aMP ∣ γ) Γᴿ
      go 0m meq γ Γᴿ Γᴿ₁ Γᴿ₂ eq₁ h₁ h₂ =
        ∃P-elim (λ { Γᴿ₂' eq₂ →
          (Γᴿ₁ ,, Γᴿ₂') ,∃
            (trans (cong (Γᴿ₁ +ᴿ_) eq₂) eq₁
            ,P (SubᴿP.∣ σᴿ ∣ h₁ ,P substP (λ μ → ∣ AMP ∣ᴿ (SubP.∣ σP ∣ γ) Γᴿ₂' μ (TmMP.∣ aMP ∣ γ)) (sym meq) (∣ AMP ∣ᴿ0 (TmMP.∣ aMP ∣ γ))))
        }) (bwd-*-res ρ ΘᴿP γ Γᴿ₂ h₂)
      go 1m meq γ Γᴿ Γᴿ₁ Γᴿ₂ eq₁ h₁ h₂ =
        ∃P-elim (λ { Γᴿ₂' (eq₂ ,P h₂') →
          (Γᴿ₁ ,, Γᴿ₂') ,∃
            (trans (cong (Γᴿ₁ +ᴿ_) eq₂) eq₁
            ,P (SubᴿP.∣ σᴿ ∣ h₁ ,P TmᴿMP.∣ tᴿM ∣ h₂'))
        }) (bwd-* ρ meq ΘᴿP γ Γᴿ₂ h₂)

  pᴿMP : ∀ {AMP : TyMP ΓP} → SubᴿP (_▷ᴿMP[_] {AMP = AMP} ΓᴿP 0r) ΓᴿP pMP
  SubᴿP.∣ pᴿMP ∣ {γ = γ ,, a} h =
    ∃P-elim (λ { (Γᴿ₁ ,, Γᴿ₂) (eq ,P (tail ,P _)) →
      substP (⟦ _ ⟧ᴿ γ)
        (trans (sym (trans +ᴿ-comm +ᴿ-0)) eq)
        tail }) h

  qᴿMP : ∀ {AMP : TyMP ΓP} → TmᴿMP (_▷ᴿMP[_] {AMP = AMP} (0r *ᴿP ΓᴿP) 1r) 1m (AMP [ pMP ]TM) qMP
  TmᴿMP.∣ qᴿMP {AMP = AMP'} ∣ {γ = γ ,, a} h =
    ∃P-elim (λ { (Γᴿ₁ ,, Γᴿ₂) (eq ,P (tail ,P tmr)) →
      substP (λ Γᴿ → ∣ AMP' ∣ᴿ γ Γᴿ _ a)
        (trans (sym (trans (cong (_+ᴿ (1r *ᴿ Γᴿ₂)) (0ᴿP-is-∙ᴿ γ Γᴿ₁ tail))
          (trans (cong ((0r *ᴿ Γᴿ₁) +ᴿ_) *ᴿ-1) +ᴿ-0))) eq)
        (substP (λ μ → ∣ AMP' ∣ᴿ γ Γᴿ₂ μ a) mode-1r tmr) }) h

  _[_]ᴿMP : TmᴿMP ΔᴿP μ AMP aMP → SubᴿP ΓᴿP ΔᴿP σP → TmᴿMP ΓᴿP μ (AMP [ σP ]TM) (aMP [ σP ]MP)
  TmᴿMP.∣ tᴿM [ σᴿ ]ᴿMP ∣ h = TmᴿMP.∣ tᴿM ∣ (SubᴿP.∣ σᴿ ∣ h)

  0ᵗMP : (aMP : TmMP ΓP AMP) → TmᴿMP ΓᴿP 0m AMP aMP
  TmᴿMP.∣ 0ᵗMP {AMP = AMP} aMP ∣ {γ = γ} _ = ∣ AMP ∣ᴿ0 (TmMP.∣ aMP ∣ γ)

  <>ᴿP : TmᴿOP ΓᴿP 1m AOP aOP → TmᴿMP ΓᴿP 1m (CodeP AOP) (< aOP >P)
  TmᴿMP.∣ <>ᴿP tᴿ ∣ h = TmᴿOP.∣ tᴿ ∣ h

  ~ᴿP_ : TmᴿMP ΓᴿP 1m (CodeP AOP) aMP → TmᴿOP ΓᴿP 1m AOP (~P aMP)
  TmᴿOP.∣ ~ᴿP tᴿM ∣ h = TmᴿMP.∣ tᴿM ∣ h

  lamᴿMP : ∀ {AMP : TyMP ΓP} {BMP : TyMP (ΓP ▷MP AMP)} {tMP : TmMP (ΓP ▷MP AMP) BMP}
         → TmᴿMP (_▷ᴿMP[_] {AMP = AMP} ΓᴿP ρ) 1m BMP tMP
         → TmᴿMP ΓᴿP 1m (ΠMP ρ AMP BMP) (lamMP tMP)
  TmᴿMP.∣ lamᴿMP {AMP = AMP} tᴿMP ∣ {γ = γ} h σ σᴿ Θᴿ a aᴿ =
    let h' = ⟦⟧ᴿ-base-sub _ h σ σᴿ
        ext-h : ⟦ _▷ᴿMP[_] {AMP = AMP} _ _ ⟧ᴿ (γ ⟪ σ ⟫ ,, a) (_ +ᴿ (_ *ᴿ Θᴿ))
        ext-h = (_ ,, Θᴿ) ,∃ (refl ,P (h' ,P aᴿ))
    in TmᴿMP.∣ tᴿMP ∣ ext-h

  appᴿMP : ∀ {AMP : TyMP ΓP} {BMP : TyMP (ΓP ▷MP AMP)} {fMP : TmMP ΓP (ΠMP ρ AMP BMP)}
         → TmᴿMP ΓᴿP 1m (ΠMP ρ AMP BMP) fMP
         → TmᴿMP (_▷ᴿMP[_] {AMP = AMP} ΓᴿP ρ) 1m BMP (appMP fMP)
  TmᴿMP.∣ appᴿMP {ρ = ρ} {AMP = AMP} {BMP = BMP} {fMP = fMP} fᴿMP ∣ {γ = γ ,, a} h =
    ∃P-elim (λ { (Γᴿ₁ ,, Γᴿ₂) (eq ,P (h₁ ,P h₂)) →
      let a' = coe (cong (∣ AMP ∣) (sym (⟪id⟫ γ))) a
          aᴿ' = ap-metᴿ {AMP = AMP} (sym (⟪id⟫ γ)) refl h₂
          result = TmᴿMP.∣ fᴿMP ∣ h₁ id idᴿ Γᴿ₂ a' aᴿ'
          ctx-path = Σ≡ (⟪id⟫ γ) (splitl reflᴰ)
      in ap-metᴿ {AMP = BMP} ctx-path eq result
    }) h

  -- Meta resourced fragment
  resMetaCtors : TL.InResMetaSorts.ResMetaCtors metaCtors objectResourced resMetaSorts
  resMetaCtors = record
    { _[_]ᴿM   = _[_]ᴿMP
    ; 0ᵗM      = 0ᵗMP
    ; _▷M[_]_  = λ ΓᴿP ρ AMP → ΓᴿP ▷ᴿMP[ ρ ]
    ; extM+    = refl
    ; extM*    = refl
    ; projᶜM   = projᶜMP
    ; projʳM   = projʳMP
    ; proj-ηM  = proj-ηMP
    ; projᶜ-βM = refl
    ; projʳ-βM = refl
    ; pᴿM      = pᴿMP
    ; qᴿM      = qᴿMP
    ; _,ᴿM[_]_ = λ σᴿ ρ tᴿM → ,ᴿM-helper σᴿ ρ tᴿM
    ; lamᴿM    = lamᴿMP
    ; appᴿM    = appᴿMP
    ; <>ᴿ      = <>ᴿP
    ; ~ᴿ_      = ~ᴿP_
    }

  -- Total model
  staging : TL.Total²
  staging = record
    { sorts     = objectSorts
    ; base      = objectBase
    ; rsorts    = objectRSorts
    ; resourced = objectResourced
    ; msorts    = metaSorts
    ; meta      = metaCtors
    ; rmsorts   = resMetaSorts
    ; resmeta   = resMetaCtors
    }

  -- Staging functions

  stageT : TyOP ∙P → Ty ∙
  stageT AOP = ∣ AOP ∣ tt𝟙

  stage : TmOP ∙P AOP → Tm ∙ (stageT AOP)
  stage aOP = ∣ aOP ∣ tt𝟙

  stageᴿ : TmᴿOP ∙ᴿP μ AOP aOP → Tmᴿ ∙ᴿ μ (stageT AOP) (stage aOP)
  stageᴿ aᴿOP = TmᴿOP.∣ aᴿOP ∣ (sym *ᴿ-∙)
