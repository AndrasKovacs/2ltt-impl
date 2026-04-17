{-# OPTIONS --type-in-type #-}
module Semiring where

open import Utils

data Mode : Set where
  0m : Mode
  1m : Mode

record SemiringBase : Set where
  field
    R : Set
    0r 1r : R
    _+r_ _*r_ : R → R → R
    mode : R → Mode

module InSemiringBase (D : SemiringBase) where
  open SemiringBase D public

  variable
    ρ π ξ : R
    μ ν : Mode

  record SemiringAxioms : Set where
    field
      +r-assoc : (ρ +r π) +r ξ ≡ ρ +r (π +r ξ)
      +r-comm  : ρ +r π ≡ π +r ρ
      +r-0     : 0r +r ρ ≡ ρ
      *r-assoc : (ρ *r π) *r ξ ≡ ρ *r (π *r ξ)
      *r-1l    : 1r *r ρ ≡ ρ
      *r-1r    : ρ *r 1r ≡ ρ
      *r-0l    : 0r *r ρ ≡ 0r
      *r-0r    : ρ *r 0r ≡ 0r
      distl    : ρ *r (π +r ξ) ≡ (ρ *r π) +r (ρ *r ξ)
      distr    : (ρ +r π) *r ξ ≡ (ρ *r ξ) +r (π *r ξ)

      mode-0-inj : mode ρ ≡ 0m → ρ ≡ 0r
      mode-0r : mode 0r ≡ 0m
      mode-1r : mode 1r ≡ 1m
      mode-+r : mode ρ ≡ 1m → mode (ρ +r π) ≡ 1m
      mode-*r : mode ρ ≡ 1m → mode π ≡ 1m → mode (ρ *r π) ≡ 1m
