{-# OPTIONS --type-in-type #-}
module 2LRCwF.Model where

open import Utils
open import Semiring public
import RCwF.Model as RCwF

-- Here we define a 2-level structure over an RCwF. This is entirely analogous to
-- the usual 2LTT setup. In usual 2LTT, we add another representable map to the
-- base category of contexts. Here, we add another 'resourced' representable map
-- to the base 'displayed category of contexts and resources'
--
-- In other words, the meta level is resourced in the same way that the base is
-- resourced. This is required in order for the meta level to be stable under
-- object substitutions. Concretely, `Code` is linear.

module Over {D : SemiringBase} (S : InSemiringBase.SemiringAxioms D) where
  open InSemiringBase D
  open InSemiringBase.SemiringAxioms S
  open RCwF.Over S

  record MetaSorts (sorts : BaseSorts) : Set where
    open BaseSorts sorts
    field
      TyM : Con → Set
      TmM : (Γ : Con) → TyM Γ → Set

  module InMetaSorts (sorts : BaseSorts) (base : InBaseSorts.BaseCtors sorts) (msorts : MetaSorts sorts) where
    open BaseSorts sorts
    open InBaseSorts sorts
    open InBaseSorts.BaseCtors base
    open MetaSorts msorts

    variable
      AM BM AM' BM' : TyM Γ
      aM bM aM' bM' : TmM Γ AM

    opaque
      unfolding coe
      ap-TmM : AM ≡ BM → TmM Γ AM ≡ TmM Γ BM
      ap-TmM refl = refl

    module MetaUtils
      (_[_]TM : ∀ {Γ Δ} → TyM Δ → Sub Γ Δ → TyM Γ)
      where
      opaque
        unfolding coe
        ap-[]TM-impl : σ ≡ τ → AM [ σ ]TM ≡ AM [ τ ]TM
        ap-[]TM-impl refl = refl

    record MetaCtors : Set where
      field
        _[_]TM : TyM Δ → Sub Γ Δ → TyM Γ
        [id]TM : AM [ id ]TM ≡ AM
        [∘]TM  : AM [ σ ∘ τ ]TM ≡ (AM [ σ ]TM) [ τ ]TM

        _[_]M  : TmM Δ AM → (σ : Sub Γ Δ) → TmM Γ (AM [ σ ]TM)
        [id]M  : aM [ id ]M ≡[ ap-TmM [id]TM ] aM
        [∘]M   : aM [ σ ∘ τ ]M ≡[ ap-TmM [∘]TM ] (aM [ σ ]M) [ τ ]M

        _▷M_  : (Γ : Con) → TyM Γ → Con
        pM    : Sub (Γ ▷M AM) Γ
        qM    : TmM (Γ ▷M AM) (AM [ pM ]TM)
        _,M_  : (σ : Sub Γ Δ) → TmM Γ (AM [ σ ]TM) → Sub Γ (Δ ▷M AM)
        p∘,M  : pM ∘ (σ ,M aM) ≡ σ
        ,∘M   : (σ ,M aM) ∘ τ ≡ ((σ ∘ τ) ,M coe (ap-TmM (sym [∘]TM)) (aM [ τ ]M))
        p,qM  : _,M_ {AM = AM} pM qM ≡ id

      ap-[]TM : σ ≡ τ → AM [ σ ]TM ≡ AM [ τ ]TM
      ap-[]TM = MetaUtils.ap-[]TM-impl _[_]TM

      _↑M_ : (σ : Sub Γ Δ) → (AM : TyM Δ) → Sub (Γ ▷M (AM [ σ ]TM)) (Δ ▷M AM)
      σ ↑M AM = ((σ ∘ pM) ,M coe (ap-TmM (sym [∘]TM)) qM)

      field
        q[,]M : (qM [ σ ,M aM ]M) ≡[ ap-TmM (trans (sym [∘]TM) (ap-[]TM p∘,M)) ] aM

        UM    : TyM Γ
        ElM   : TmM Γ UM → TyM Γ
        U[]M  : UM [ σ ]TM ≡ UM
        El[]M : (ElM aM) [ σ ]TM ≡ ElM (coe (ap-TmM U[]M) (aM [ σ ]M))

        ΠM     : R → (AM : TyM Γ) → TyM (Γ ▷M AM) → TyM Γ
        lamM   : TmM (Γ ▷M AM) BM → TmM Γ (ΠM ρ AM BM)
        appM   : TmM Γ (ΠM ρ AM BM) → TmM (Γ ▷M AM) BM
        ΠβM    : (t : TmM (Γ ▷M AM) BM) → appM {ρ = ρ} (lamM t) ≡ t
        ΠηM    : (f : TmM Γ (ΠM ρ AM BM)) → lamM (appM f) ≡ f
        Π[]M   : (ΠM ρ AM BM) [ σ ]TM ≡ ΠM ρ (AM [ σ ]TM) (BM [ σ ↑M AM ]TM)
        lam[]M : (t : TmM (Δ ▷M AM) BM) → (lamM {ρ = ρ} t) [ σ ]M ≡[ ap-TmM Π[]M ] lamM (t [ σ ↑M AM ]M)

        Code    : Ty Γ → TyM Γ
        Code[]  : (Code A) [ σ ]TM ≡ Code (A [ σ ]T)
        <_>     : Tm Γ A → TmM Γ (Code A)
        ~_      : TmM Γ (Code A) → Tm Γ A
        <>[]    : < a > [ σ ]M ≡[ ap-TmM Code[] ] < a [ σ ] >
        ~[]     : (~ aM) [ σ ] ≡ ~ (coe (ap-TmM Code[]) (aM [ σ ]M))
        ~<>     : (a : Tm Γ A) → ~ < a > ≡ a
        <>~     : (t : TmM Γ (Code A)) → < ~ t > ≡ t

  record ResMetaSorts
    {sorts : BaseSorts} (base : InBaseSorts.BaseCtors sorts)
    (msorts : MetaSorts sorts) (rsorts : ResSorts sorts) : Set where
    open BaseSorts sorts
    open MetaSorts msorts
    open ResSorts rsorts
    field
      TmᴿM : ∀ {Γ} → Conᴿ Γ → Mode → (AM : TyM Γ) → TmM Γ AM → Prop

  module InResMetaSorts
    {sorts : BaseSorts} {base : InBaseSorts.BaseCtors sorts}
    {msorts : MetaSorts sorts} (metaCtors : InMetaSorts.MetaCtors sorts base msorts)
    {rsorts : ResSorts sorts} (resCtors : InResSorts.ResCtors base rsorts)
    (rmsorts : ResMetaSorts base msorts rsorts) where
    open BaseSorts sorts
    open InBaseSorts sorts
    open InBaseSorts.BaseCtors base
    open MetaSorts msorts
    open InMetaSorts sorts base msorts
    open InMetaSorts.MetaCtors metaCtors
    open ResSorts rsorts
    open InResSorts base rsorts
    open InResSorts.ResCtors resCtors
    open ResMetaSorts rmsorts

    opaque
      unfolding coe
      ap-TmᴿM : (e : AM ≡ BM) → TmᴿM Γᴿ μ AM aM → TmᴿM Γᴿ μ BM (coe (ap-TmM e) aM)
      ap-TmᴿM refl x = x

    record ResMetaCtors : Set where
      field
        _[_]ᴿM : TmᴿM Δᴿ μ AM aM → Subᴿ Γᴿ Δᴿ σ → TmᴿM Γᴿ μ (AM [ σ ]TM) (aM [ σ ]M)

        0ᵗM : (aM : TmM Γ AM) → TmᴿM Γᴿ 0m AM aM

        _▷M[_]_ : Conᴿ Γ → R → (AM : TyM Γ) → Conᴿ (Γ ▷M AM)
        extM+  : (Γᴿ +ᴿ Δᴿ) ▷M[ ρ +r π ] AM ≡ (Γᴿ ▷M[ ρ ] AM) +ᴿ (Δᴿ ▷M[ π ] AM)
        extM*  : (ρ *ᴿ Γᴿ) ▷M[ ρ *r π ] AM ≡ ρ *ᴿ (Γᴿ ▷M[ π ] AM)
        projᶜM  : Conᴿ (Γ ▷M AM) → Conᴿ Γ
        projʳM  : Conᴿ (Γ ▷M AM) → R
        proj-ηM  : (Γᴿ : Conᴿ (Γ ▷M AM)) → Γᴿ ≡ projᶜM Γᴿ ▷M[ projʳM Γᴿ ] AM
        projᶜ-βM : projᶜM (Γᴿ ▷M[ ρ ] AM) ≡ Γᴿ
        projʳ-βM : projʳM (Γᴿ ▷M[ ρ ] AM) ≡ ρ

        pᴿM    : Subᴿ (Γᴿ ▷M[ 0r ] AM) Γᴿ pM
        qᴿM    : TmᴿM ((0r *ᴿ Γᴿ) ▷M[ 1r ] AM) 1m (AM [ pM ]TM) qM

        _,ᴿM[_]_ : Subᴿ Γᴿ Δᴿ σ → (ρ : R) →
                    TmᴿM Θᴿ (mode ρ) (AM [ σ ]TM) aM →
                    Subᴿ (Γᴿ +ᴿ (ρ *ᴿ Θᴿ)) (Δᴿ ▷M[ ρ ] AM) (σ ,M aM)

        lamᴿM : TmᴿM (Γᴿ ▷M[ ρ ] AM) 1m BM bM → TmᴿM Γᴿ 1m (ΠM ρ AM BM) (lamM bM)
        appᴿM : TmᴿM Γᴿ 1m (ΠM ρ AM BM) aM → TmᴿM (Γᴿ ▷M[ ρ ] AM) 1m BM (appM aM)

        <>ᴿ    : Tmᴿ Γᴿ 1m A a → TmᴿM Γᴿ 1m (Code A) < a >
        ~ᴿ_    : TmᴿM Γᴿ 1m (Code A) aM → Tmᴿ Γᴿ 1m A (~ aM)

      ap-▷Mᴿ : Γᴿ ≡ Δᴿ → ρ ≡ π → Γᴿ ▷M[ ρ ] AM ≡ Δᴿ ▷M[ π ] AM
      ap-▷Mᴿ refl refl = refl

      lowerM : TmᴿM Γᴿ 1m AM aM → (μ : Mode) → TmᴿM Γᴿ μ AM aM
      lowerM x 0m = 0ᵗM _
      lowerM x 1m = x

      _↑ᴿM[_]_ : Subᴿ Γᴿ Δᴿ σ → (ρ : R) → (AM : TyM _)
              → Subᴿ (Γᴿ ▷M[ ρ ] (AM [ σ ]TM)) (Δᴿ ▷M[ ρ ] AM) (σ ↑M AM)
      _↑ᴿM[_]_ {Γᴿ = Γᴿ} {σ = σ} σᴿ ρ AM =
        let AM' = AM [ σ ]TM
            step3 = (σᴿ ∘ᴿ pᴿM) ,ᴿM[ ρ ] lowerM (ap-TmᴿM (sym [∘]TM) (qᴿM {Γᴿ = Γᴿ})) (mode ρ)
            p1 : ρ *ᴿ ((0r *ᴿ Γᴿ) ▷M[ 1r ] AM') ≡ (0r *ᴿ Γᴿ) ▷M[ ρ ] AM'
            p1 = trans (sym extM*) (ap-▷Mᴿ (trans (sym *ᴿ-assoc) (cong (_*ᴿ Γᴿ) *r-0r)) *r-1r)
            p2 : (Γᴿ ▷M[ 0r ] AM') +ᴿ ((0r *ᴿ Γᴿ) ▷M[ ρ ] AM') ≡ (Γᴿ +ᴿ (0r *ᴿ Γᴿ)) ▷M[ 0r +r ρ ] AM'
            p2 = sym extM+
            p3 : (Γᴿ +ᴿ (0r *ᴿ Γᴿ)) ▷M[ 0r +r ρ ] AM' ≡ Γᴿ ▷M[ ρ ] AM'
            p3 = ap-▷Mᴿ (trans +ᴿ-comm +ᴿ-0) +r-0
        in ap-Subᴿ₁ (trans (cong ((Γᴿ ▷M[ 0r ] AM') +ᴿ_) p1) (trans p2 p3)) step3

  record Total² : Set where
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
    field
      msorts : MetaSorts sorts
    open MetaSorts msorts public
    open InMetaSorts sorts base msorts
    field
      meta : MetaCtors
    open MetaCtors meta public
    field
      rmsorts : ResMetaSorts base msorts rsorts
    open ResMetaSorts rmsorts public
    open InResMetaSorts meta resourced rmsorts
    field
      resmeta : ResMetaCtors
    open ResMetaCtors resmeta public
