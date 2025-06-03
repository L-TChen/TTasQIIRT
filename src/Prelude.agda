module Prelude where

open import Cubical.Core.Primitives     public
  hiding (Sub)
open import Cubical.Foundations.Prelude public
  hiding (Sub)
open import Cubical.Foundations.HLevels public
open import Cubical.Data.Sigma          public
  hiding (Sub)
open import Cubical.Data.Empty          public
open import Cubical.Data.Unit           public
  renaming (tt to ⋆)
open import Cubical.Data.Nat            public
  using (ℕ; zero; suc; _+_)
open import Cubical.Data.Bool           public
  using (Bool; true; false)

open import Agda.Primitive              public

variable
  ℓ ℓ' ℓ'' ℓ''' ℓ'''' ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

infix 4 PathP-syntax
PathP-syntax : ∀ {ℓ} (A : I → Type ℓ) → A i0 → A i1 → Type ℓ
PathP-syntax = PathP

syntax PathP-syntax (λ i → A) x y = x ≡[ i ⊢ A ] y
