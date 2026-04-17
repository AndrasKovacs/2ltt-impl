{-# OPTIONS --type-in-type #-}
module RCwF.Model where

open import Utils
open import Semiring public

-- Here we define the notion of RCwF (resourced CwF)

-- This is *similar* but not the same as Atkey's notion of QCwF.

-- Essentially, RCwF is a refinement type system over a standard CwF. We have the base CwF B,
-- and the resourced category E which is displayed over B. The displaying map is
-- injective, which means that the (dependent) sorts of E are in Prop.
-- This refinement is what restricts variable usage to match the 'available resources' we have.
--
-- Resources are represented by a semiring R. Resourced contexts (over a fixed
-- base Γ) carry an R-module structure, in the sense that we can add them, and
-- scale them by R. Atkey's models are weaker in that the R module structure can
-- be very lax (but the syntax this yields is not so good..). Also Atkey
-- requires that the resourced category is properly lax monoidal in the sense
-- that the + and * are functors. We do not require this but I think it is
-- admissible (I have not proven that yet!)

module Over {D : SemiringBase} (S : InSemiringBase.SemiringAxioms D) where
  open InSemiringBase D
  open InSemiringBase.SemiringAxioms S

  -- The Base is just a normal CwF

  record BaseSorts : Set where
    field
      Con : Set
      Sub : Con → Con → Set
      Ty  : Con → Set
      Tm  : (Γ : Con) → Ty Γ → Set

  module InBaseSorts (sorts : BaseSorts) where
    open BaseSorts sorts

    variable
      Γ Δ Θ Γ' Δ' Θ' : Con
      A B A' B' : Ty Γ
      σ τ δ σ' τ' : Sub Γ Δ
      a b a' b' : Tm Γ A

    opaque
      unfolding coe
      ap-Ty : Γ ≡ Δ → Ty Γ ≡ Ty Δ
      ap-Ty refl = refl

      ap-Sub : Γ ≡ Γ' → Δ ≡ Δ' → Sub Γ Δ ≡ Sub Γ' Δ'
      ap-Sub refl refl = refl

      ap-Tm : A ≡ B → Tm Γ A ≡ Tm Γ B
      ap-Tm refl = refl

      ap-Tmᶜ : (eΓ : Γ ≡ Δ) → A ≡[ ap-Ty eΓ ] B → Tm Γ A ≡ Tm Δ B
      ap-Tmᶜ refl refl = refl

    module BaseUtils
      (_[_]T : ∀ {Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ)
      where
      opaque
        unfolding coe
        ap-[]T-impl : σ ≡ τ → A [ σ ]T ≡ A [ τ ]T
        ap-[]T-impl refl = refl

        ap-[]T₁-impl : A ≡ B → A [ σ ]T ≡ B [ σ ]T
        ap-[]T₁-impl refl = refl

    record BaseCtors : Set where
      field
        id    : Sub Γ Γ
        _∘_   : Sub Δ Θ → Sub Γ Δ → Sub Γ Θ
        id∘   : id ∘ σ ≡ σ
        ∘id   : σ ∘ id ≡ σ
        assoc : δ ∘ (σ ∘ τ) ≡ (δ ∘ σ) ∘ τ

        ∙     : Con
        ε     : Sub Γ ∙
        ∃!ε   : ε ≡ σ

        _[_]T : Ty Δ → Sub Γ Δ → Ty Γ
        [id]T : A [ id ]T ≡ A
        [∘]T  : A [ σ ∘ τ ]T ≡ (A [ σ ]T) [ τ ]T

        _[_]  : Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
        [id]  : a [ id ] ≡[ ap-Tm [id]T ] a
        [∘]   : a [ σ ∘ τ ] ≡[ ap-Tm [∘]T ] (a [ σ ]) [ τ ]

        _▷_   : (Γ : Con) → Ty Γ → Con
        p     : Sub (Γ ▷ A) Γ
        q     : Tm (Γ ▷ A) (A [ p ]T)
        _,_   : (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T) → Sub Γ (Δ ▷ A)
        p∘,   : p ∘ (σ , a) ≡ σ
        ,∘    : (σ , a) ∘ τ ≡ ((σ ∘ τ) , coe (ap-Tm (sym [∘]T)) (a [ τ ]))
        p,q   : _,_ {A = A} p q ≡ id

      ap-[]T : σ ≡ τ → A [ σ ]T ≡ A [ τ ]T
      ap-[]T = BaseUtils.ap-[]T-impl _[_]T

      _↑_ : (σ : Sub Γ Δ) → (A : Ty Δ) → Sub (Γ ▷ (A [ σ ]T)) (Δ ▷ A)
      σ ↑ A = ((σ ∘ p) , coe (ap-Tm (sym [∘]T)) q)

      field
        q[,]  : q [ σ , a ] ≡[ ap-Tm (trans (sym [∘]T) (ap-[]T p∘,)) ] a

        U     : Ty Γ
        El    : Tm Γ U → Ty Γ
        U[]   : U [ σ ]T ≡ U
        El[]  : (El a) [ σ ]T ≡ El (coe (ap-Tm U[]) (a [ σ ]))

        Π     : R → (A : Ty Γ) → Ty (Γ ▷ A) → Ty Γ
        lam   : Tm (Γ ▷ A) B → Tm Γ (Π ρ A B)
        app   : Tm Γ (Π ρ A B) → Tm (Γ ▷ A) B
        Πβ    : (t : Tm (Γ ▷ A) B) → app {ρ = ρ} (lam t) ≡ t
        Πη    : (f : Tm Γ (Π ρ A B)) → lam (app f) ≡ f
        Π[]   : (Π ρ A B) [ σ ]T ≡ Π ρ (A [ σ ]T) (B [ σ ↑ A ]T)
        lam[] : (t : Tm (Δ ▷ A) B) → (lam {ρ = ρ} t) [ σ ] ≡[ ap-Tm Π[] ] lam (t [ σ ↑ A ])

      ap-[]T₁ : A ≡ B → A [ σ ]T ≡ B [ σ ]T
      ap-[]T₁ = BaseUtils.ap-[]T₁-impl _[_]T

      opaque
        unfolding coe

        ap-▷ : (eΓ : Γ ≡ Δ) → A ≡[ ap-Ty eΓ ] B → (Γ ▷ A) ≡ (Δ ▷ B)
        ap-▷ refl refl = refl

        ap-id : (e : Γ ≡ Δ) → id {Γ} ≡[ ap-Sub e e ] id {Δ}
        ap-id refl = refl

        ap-ε : (e : Γ ≡ Δ) → ε {Γ} ≡[ ap-Sub e refl ] ε {Δ}
        ap-ε refl = refl

        ap-∘ : (eΓ : Γ ≡ Γ') (eΔ : Δ ≡ Δ') (eΘ : Θ ≡ Θ')
          → σ ≡[ ap-Sub eΔ eΘ ] σ'
          → τ ≡[ ap-Sub eΓ eΔ ] τ'
          → (σ ∘ τ) ≡[ ap-Sub eΓ eΘ ] (σ' ∘ τ')
        ap-∘ refl refl refl refl refl = refl

        ap-[]Tᶜ : (eΔ : Δ ≡ Δ') (eΘ : Θ ≡ Θ')
          → A ≡[ ap-Ty eΘ ] B
          → σ ≡[ ap-Sub eΔ eΘ ] σ'
          → (A [ σ ]T) ≡[ ap-Ty eΔ ] (B [ σ' ]T)
        ap-[]Tᶜ refl refl refl refl = refl

        ap-p : (eΓ : Γ ≡ Δ) → (eA : A ≡[ ap-Ty eΓ ] B)
          → p {Γ} {A} ≡[ ap-Sub (ap-▷ eΓ eA) eΓ ] p {Δ} {B}
        ap-p refl refl = refl

        ap-q : (eΓ : Γ ≡ Δ) → (eA : A ≡[ ap-Ty eΓ ] B)
          → q {Γ} {A} ≡[ ap-Tmᶜ (ap-▷ eΓ eA) (ap-[]Tᶜ (ap-▷ eΓ eA) eΓ eA (ap-p eΓ eA)) ] q {Δ} {B}
        ap-q refl refl = refl

        ap-[] : (eΔ : Δ ≡ Δ') (eΘ : Θ ≡ Θ')
          → (eA : A ≡[ ap-Ty eΘ ] B)
          → (eσ : σ ≡[ ap-Sub eΔ eΘ ] σ')
          → a ≡[ ap-Tmᶜ eΘ eA ] b
          → (a [ σ ]) ≡[ ap-Tmᶜ eΔ (ap-[]Tᶜ eΔ eΘ eA eσ) ] (b [ σ' ])
        ap-[] refl refl refl refl refl = refl

        ap-, : {a : Tm Γ (A [ σ ]T)} {b : Tm Γ' (B [ σ' ]T)}
          → (eΓ : Γ ≡ Γ') (eΔ : Δ ≡ Δ')
          → (eA : A ≡[ ap-Ty eΔ ] B)
          → (eσ : σ ≡[ ap-Sub eΓ eΔ ] σ')
          → a ≡[ ap-Tmᶜ eΓ (ap-[]Tᶜ eΓ eΔ eA eσ) ] b
          → (σ , a) ≡[ ap-Sub eΓ (ap-▷ eΔ eA) ] (σ' , b)
        ap-, refl refl refl refl refl = refl

        ap-U : (eΓ : Γ ≡ Δ) → U {Γ} ≡[ ap-Ty eΓ ] U {Δ}
        ap-U refl = refl

        ap-El : (eΓ : Γ ≡ Δ) → {a : Tm Γ U} {b : Tm Δ U}
          → a ≡[ ap-Tmᶜ eΓ (ap-U eΓ) ] b
          → El a ≡[ ap-Ty eΓ ] El b
        ap-El refl refl = refl

        ap-Π : (eΓ : Γ ≡ Δ) → ρ ≡ π
          → (eA : A ≡[ ap-Ty eΓ ] B)
          → {C : Ty (Γ ▷ A)} {D : Ty (Δ ▷ B)}
          → C ≡[ ap-Ty (ap-▷ eΓ eA) ] D
          → Π ρ A C ≡[ ap-Ty eΓ ] Π π B D
        ap-Π refl refl refl refl = refl

        ap-lam : (eΓ : Γ ≡ Δ) → (eρ : ρ ≡ π)
          → (eA : A ≡[ ap-Ty eΓ ] B)
          → {C : Ty (Γ ▷ A)} {D : Ty (Δ ▷ B)}
          → (eC : C ≡[ ap-Ty (ap-▷ eΓ eA) ] D)
          → {c : Tm (Γ ▷ A) C} {d : Tm (Δ ▷ B) D}
          → c ≡[ ap-Tmᶜ (ap-▷ eΓ eA) eC ] d
          → lam {ρ = ρ} c ≡[ ap-Tmᶜ eΓ (ap-Π eΓ eρ eA eC) ] lam {ρ = π} d
        ap-lam refl refl refl refl refl = refl

        ap-app : (eΓ : Γ ≡ Δ) → (eρ : ρ ≡ π)
          → (eA : A ≡[ ap-Ty eΓ ] B)
          → {C : Ty (Γ ▷ A)} {D : Ty (Δ ▷ B)}
          → (eC : C ≡[ ap-Ty (ap-▷ eΓ eA) ] D)
          → {f : Tm Γ (Π ρ A C)} {g : Tm Δ (Π π B D)}
          → f ≡[ ap-Tmᶜ eΓ (ap-Π eΓ eρ eA eC) ] g
          → app f ≡[ ap-Tmᶜ (ap-▷ eΓ eA) eC ] app g
        ap-app refl refl refl refl refl = refl

      opaque
        unfolding coe
        ap-[]₀ : (p : σ ≡ τ) → a [ σ ] ≡[ ap-Tm (ap-[]T p) ] a [ τ ]
        ap-[]₀ refl = refl

        ap-[]₁ : {a : Tm Γ A} {b : Tm Γ B} → (p : A ≡ B) → a ≡[ ap-Tm p ] b
          → a [ σ ] ≡[ ap-Tm (ap-[]T₁ p) ] b [ σ ]
        ap-[]₁ refl refl = refl

  -- Resourced CwF (with a definitionally-coherent injective map into Base)

  -- Types only exist in the base.
  record ResSorts (sorts : BaseSorts) : Set where
    open BaseSorts sorts
    field
      Conᴿ : Con → Set
      Subᴿ : ∀ {Γ Δ} → Conᴿ Γ → Conᴿ Δ → Sub Γ Δ → Prop

      -- Terms are indexed by a mode, which can be derived from a resource ρ
      -- (see Semiring.agda). It must also obey a monotonicity law.
      Tmᴿ  : ∀ {Γ} → Conᴿ Γ → Mode → (A : Ty Γ) → Tm Γ A → Prop

      -- Addition and scaling of contexts.
      _+ᴿ_ : ∀ {Γ} → Conᴿ Γ → Conᴿ Γ → Conᴿ Γ
      _*ᴿ_ : ∀ {Γ} → R → Conᴿ Γ → Conᴿ Γ

  module InResSorts {sorts : BaseSorts} (base : InBaseSorts.BaseCtors sorts) (rsorts : ResSorts sorts) where
    open BaseSorts sorts
    open InBaseSorts sorts
    open InBaseSorts.BaseCtors base
    open ResSorts rsorts

    variable
      Γᴿ Δᴿ Θᴿ Φᴿ : Conᴿ Γ

    opaque
      unfolding coe
      ap-Conᴿ : Γ ≡ Δ → Conᴿ Γ ≡ Conᴿ Δ
      ap-Conᴿ refl = refl

      ap-Tmᴿ : (e : A ≡ B) → Tmᴿ Γᴿ μ A a → Tmᴿ Γᴿ μ B (coe (ap-Tm e) a)
      ap-Tmᴿ refl x = x

      ap-Subᴿ₁ : Γᴿ ≡ Δᴿ → Subᴿ Γᴿ Θᴿ σ → Subᴿ Δᴿ Θᴿ σ
      ap-Subᴿ₁ refl x = x

      ap-Subᴿ₂ : Δᴿ ≡ Θᴿ → Subᴿ Γᴿ Δᴿ σ → Subᴿ Γᴿ Θᴿ σ
      ap-Subᴿ₂ refl x = x

      ap-+ᴿ : Γᴿ ≡ Δᴿ → Θᴿ ≡ Φᴿ → (Γᴿ +ᴿ Θᴿ) ≡ (Δᴿ +ᴿ Φᴿ)
      ap-+ᴿ refl refl = refl

      ap-*ᴿ : ρ ≡ π → Γᴿ ≡ Δᴿ → (ρ *ᴿ Γᴿ) ≡ (π *ᴿ Δᴿ)
      ap-*ᴿ refl refl = refl

      ap-Tmᴿ-mode : {μ ν : Mode} → μ ≡ ν → Tmᴿ Γᴿ μ A a → Tmᴿ Γᴿ ν A a
      ap-Tmᴿ-mode refl x = x

    record ResCtors : Set where
      field
        -- 0-mode terms come from base terms.
        -- This is useful because then we only need one context structure that
        -- handles both resourced and unresourced terms.
        --
        -- An η law is unnecessary since we are in Prop
        0ᵗ    : (a : Tm Γ A) → Tmᴿ Γᴿ 0m A a

        -- Module laws
        +ᴿ-comm  : Γᴿ +ᴿ Δᴿ ≡ Δᴿ +ᴿ Γᴿ
        +ᴿ-assoc : (Γᴿ +ᴿ Δᴿ) +ᴿ Θᴿ ≡ Γᴿ +ᴿ (Δᴿ +ᴿ Θᴿ)
        +ᴿ-0     : (0r *ᴿ Γᴿ) +ᴿ Δᴿ ≡ Δᴿ
        *ᴿ-assoc : (ρ *r π) *ᴿ Γᴿ ≡ ρ *ᴿ (π *ᴿ Γᴿ)

        -- Category
        idᴿ   : Subᴿ Γᴿ Γᴿ id
        _∘ᴿ_  : Subᴿ Γᴿ Δᴿ σ → Subᴿ Θᴿ Γᴿ τ → Subᴿ Θᴿ Δᴿ (σ ∘ τ)

        -- We will also require uniqueness rules for resourced contexts;
        -- A resourced context displayed over an extended base is itself extended.
        -- Similarly a resourced context displayed over an empty base is itself empty.

        -- Terminal object
        ∙ᴿ    : Conᴿ ∙
        +ᴿ-∙  : ∙ᴿ +ᴿ ∙ᴿ ≡ ∙ᴿ
        *ᴿ-∙  : ρ *ᴿ ∙ᴿ ≡ ∙ᴿ
        ∃!∙ᴿ  : (Γᴿ : Conᴿ ∙) → Γᴿ ≡ ∙ᴿ
        εᴿ    : Subᴿ {Γ} (0r *ᴿ Γᴿ) ∙ᴿ ε

        -- Resourced substitution
        _[_]ᴿ : Tmᴿ Δᴿ μ A a → Subᴿ Γᴿ Δᴿ σ → Tmᴿ Γᴿ μ (A [ σ ]T) (a [ σ ])

        -- Context extension
        _▷[_]_ : Conᴿ Γ → R → (A : Ty Γ) → Conᴿ (Γ ▷ A)

        ext+   : (Γᴿ +ᴿ Δᴿ) ▷[ ρ +r π ] A ≡ (Γᴿ ▷[ ρ ] A) +ᴿ (Δᴿ ▷[ π ] A)
        ext*   : (ρ *ᴿ Γᴿ) ▷[ ρ *r π ] A ≡ ρ *ᴿ (Γᴿ ▷[ π ] A)

        -- Uniqueness of extensions
        projᶜ  : Conᴿ (Γ ▷ A) → Conᴿ Γ
        projʳ  : Conᴿ (Γ ▷ A) → R
        proj-η  : (Γᴿ : Conᴿ (Γ ▷ A)) → Γᴿ ≡ projᶜ Γᴿ ▷[ projʳ Γᴿ ] A
        projᶜ-β : projᶜ (Γᴿ ▷[ ρ ] A) ≡ Γᴿ
        projʳ-β : projʳ (Γᴿ ▷[ ρ ] A) ≡ ρ
    
        -- This is the 'resourced' context extension structure.
        -- An extended substitution corresponds to a base substitution
        -- and a resourced term, where the resources of the total context
        -- must be split across the two.
        --
        -- We can also add the full def.iso that says
        --    Subᴿ Γᴿ (Δᴿ ▷[ρ] A) (σ,a) ≃ ∃ Γᴿ₁ Γᴿ₂ . Γᴿ = Γᴿ₁ + ρ*Γᴿ₂ ∧ Subᴿ Γᴿ₁ Δᴿ σ ∧ Tmᴿ Γᴿ₂ A[σ] a
        -- but this isn't really necessary because it (should be) admissible. (and otherwise would
        -- require some kind of propositional truncation in GAT signatures??)
        pᴿ    : Subᴿ (Γᴿ ▷[ 0r ] A) Γᴿ p
        qᴿ    : Tmᴿ ((0r *ᴿ Γᴿ) ▷[ 1r ] A) 1m (A [ p ]T) q
        _,ᴿ[_]_ : Subᴿ Γᴿ Δᴿ σ → (ρ : R) →
                   Tmᴿ Θᴿ (mode ρ) (A [ σ ]T) a →
                   Subᴿ (Γᴿ +ᴿ (ρ *ᴿ Θᴿ)) (Δᴿ ▷[ ρ ] A) (σ , a)

        -- No βη, we keep the base for extensional information, the resourced refinement carries
        -- intensional information.
        lamᴿ  : Tmᴿ (Γᴿ ▷[ ρ ] A) 1m B b → Tmᴿ Γᴿ 1m (Π ρ A B) (lam b)
        appᴿ  : Tmᴿ Γᴿ 1m (Π ρ A B) a → Tmᴿ (Γᴿ ▷[ ρ ] A) 1m B (app a)


      ap-▷ᴿ : Γᴿ ≡ Δᴿ → ρ ≡ π → Γᴿ ▷[ ρ ] A ≡ Δᴿ ▷[ π ] A
      ap-▷ᴿ refl refl = refl

      opaque
        unfolding coe

        ap-▷ᴿᶜ : (eΓ : Γ ≡ Δ) → Γᴿ ≡[ ap-Conᴿ eΓ ] Δᴿ → ρ ≡ π
          → (eA : A ≡[ ap-Ty eΓ ] B)
          → (Γᴿ ▷[ ρ ] A) ≡[ ap-Conᴿ (ap-▷ eΓ eA) ] (Δᴿ ▷[ π ] B)
        ap-▷ᴿᶜ refl refl refl refl = refl

      lower : Tmᴿ Γᴿ 1m A a → (μ : Mode) → Tmᴿ Γᴿ μ A a
      lower x 0m = 0ᵗ _
      lower x 1m = x

      -- In Atkey's models this isn't derivable
      _↑ᴿ[_]_ : Subᴿ Γᴿ Δᴿ σ → (ρ : R) → (A : Ty _)
              → Subᴿ (Γᴿ ▷[ ρ ] (A [ σ ]T)) (Δᴿ ▷[ ρ ] A) (σ ↑ A)
      _↑ᴿ[_]_ {Γᴿ = Γᴿ} {Δᴿ = Δᴿ} {σ = σ} σᴿ ρ A =
        let A' = A [ σ ]T
            step3 = (σᴿ ∘ᴿ pᴿ) ,ᴿ[ ρ ] lower (ap-Tmᴿ (sym [∘]T) (qᴿ {Γᴿ = Γᴿ})) (mode ρ)
            p1 : ρ *ᴿ ((0r *ᴿ Γᴿ) ▷[ 1r ] A') ≡ (0r *ᴿ Γᴿ) ▷[ ρ ] A'
            p1 = trans (sym ext*) (ap-▷ᴿ (trans (sym *ᴿ-assoc) (cong (_*ᴿ Γᴿ) *r-0r)) *r-1r)
            p2 : (Γᴿ ▷[ 0r ] A') +ᴿ ((0r *ᴿ Γᴿ) ▷[ ρ ] A') ≡ (Γᴿ +ᴿ (0r *ᴿ Γᴿ)) ▷[ 0r +r ρ ] A'
            p2 = sym ext+
            p3 : (Γᴿ +ᴿ (0r *ᴿ Γᴿ)) ▷[ 0r +r ρ ] A' ≡ Γᴿ ▷[ ρ ] A'
            p3 = ap-▷ᴿ (trans +ᴿ-comm +ᴿ-0) +r-0
        in ap-Subᴿ₁ (trans (cong ((Γᴿ ▷[ 0r ] A') +ᴿ_) p1) (trans p2 p3)) step3


  record Total : Set where
    field
      sorts : BaseSorts
    open BaseSorts sorts public
    open InBaseSorts sorts
    field
      base : BaseCtors
    open BaseCtors base public
    field
      rsorts : ResSorts sorts
    open ResSorts rsorts public
    open InResSorts base rsorts
    field
      resourced : ResCtors
    open ResCtors resourced public
