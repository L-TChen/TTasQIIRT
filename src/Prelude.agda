module Prelude where

open import Cubical.Core.Primitives     public
  hiding (Sub)
open import Cubical.Foundations.Prelude public
  hiding (Sub)
open import Cubical.Foundations.HLevels public
open import Cubical.Foundations.Path    public
open import Cubical.Foundations.Isomorphism public
open import Cubical.Data.Sigma          public
  hiding (Sub)
open import Cubical.Data.Empty          public
  renaming (elim to elim-⊥; rec to rec-⊥)
open import Cubical.Data.Unit           public
  renaming (tt to ⋆)
open import Cubical.Data.Nat            public
  using (ℕ; zero; suc; _+_)
open import Cubical.Data.Bool           public
  using (Bool; true; false)

open import Cubical.Foundations.Function public 
  using (_$_; hasType)
  
open import Agda.Primitive              public

variable
  ℓ ℓ' ℓ'' ℓ''' ℓ'''' ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₁' ℓ₂' ℓ₃' ℓ₄' : Level

infix 4 PathP-syntax
PathP-syntax : (A : I → Type ℓ) → A i0 → A i1 → Type ℓ
PathP-syntax = PathP

syntax PathP-syntax (λ i → A) x y = x ≡[ i ⊢ A ] y

private variable
  A : Set ℓ
postulate
  UIP : {A : Set ℓ} → {x y : A} → isProp (x ≡ y)

UIP' : {A : Set ℓ} → isSet A 
UIP' x y = UIP

_∙P_
  : {x y z : A} {B : A → Type ℓ'} {x' : B x} {y' : B y} {z' : B z} {p : x ≡ y} {q : y ≡ z}
  → PathP (λ i → B (p i)) x' y'
  → PathP (λ i → B (q i)) y' z'
  → PathP (λ i → B ((p ∙ q) i)) x' z'
_∙P_ {ℓ} {A} {ℓ'} {x} {y} {z} {B} {x'} {y'} {z'} {p} {q} p' q' =
  compPathP' {ℓ} {A} {ℓ'} {x} {y} {z} {B} {x'} {y'} {z'} {p} {q} p' q'
