module Prelude where

open import Cubical.Core.Primitives     public
  hiding (Sub)
open import Cubical.Foundations.Prelude public
  hiding (Sub; _∙'_; step-≡; ≡⟨⟩-syntax; _≡⟨⟩_; ≡⟨⟩⟨⟩-syntax; _≡⟨_⟩≡⟨_⟩_)
  renaming (_∙_ to _∙'_; _∙∙_∙∙_ to _∙∙'_∙∙_)
open import Cubical.Foundations.HLevels public
open import Cubical.Foundations.Path    public
open import Cubical.Foundations.Isomorphism public
open import Cubical.Data.Sigma          public
  hiding (Sub)
open import Cubical.Data.Empty          public
  renaming (elim to elim-⊥; rec to rec-⊥)
open import Cubical.Data.Unit           public
  renaming (tt to ⋆)
open import Cubical.Data.Nat.Base       public
  using (ℕ; zero; suc; _+_)
open import Cubical.Data.Bool.Base      public
  using (Bool; true; false)
--  renaming (elim to elim-Bool)
open import Cubical.Relation.Nullary.Base using (Discrete; Dec; yes; no; decRec) public
open import Cubical.Relation.Nullary.Properties using (Discrete→isSet) public


open import Cubical.Foundations.Function public
  using (_$_; hasType)

open import Agda.Primitive              public

variable
  ℓ ℓ' ℓ'' ℓ''' ℓ'''' ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₁' ℓ₂' ℓ₃' ℓ₄' : Level

infix 4 PathP-syntax
PathP-syntax : (A : I → Type ℓ) → A i0 → A i1 → Type ℓ
PathP-syntax = PathP

syntax PathP-syntax (λ i → A) x y = x ≡[ i ⊢ A ] y

Σ-syntax' : ∀ {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
Σ-syntax' = Σ

syntax Σ-syntax' A (λ x → B) = [ x ∶ A ] × B

private variable
  A : Set ℓ

module _ where opaque
  infixr 30 _∙_
--  infix  3 _∎
  infixr 2 step-≡ _≡⟨⟩_
  infixr 2.5 _≡⟨_⟩≡⟨_⟩_
  _∙∙_∙∙_
    : {x y z w : A}
    → x ≡ y → y ≡ z → z ≡ w → x ≡ w
  _∙∙_∙∙_ = _∙∙'_∙∙_
  _∙_
    : {x y z : A}
    → x ≡ y → y ≡ z → x ≡ z
  _∙_ = _∙'_

  _∙P_
    : {x y z : A} {B : A → Type ℓ'} {x' : B x} {y' : B y} {z' : B z} {p : x ≡ y} {q : y ≡ z}
    → PathP (λ i → B (p i)) x' y'
    → PathP (λ i → B (q i)) y' z'
    → PathP (λ i → B ((p ∙ q) i)) x' z'
  _∙P_ {ℓ} {A} {ℓ'} {x} {y} {z} {B} {x'} {y'} {z'} {p} {q} p' q' =
    compPathP' {ℓ} {A} {ℓ'} {x} {y} {z} {B} {x'} {y'} {z'} {p} {q} p' q'

  -- Syntax for chains of equational reasoning

  step-≡
    : {y z : A}
    → (x : A) → y ≡ z → x ≡ y → x ≡ z
  step-≡ _ p q = q ∙ p

  syntax step-≡ x y p = x ≡⟨ p ⟩ y

  ≡⟨⟩-syntax
    : {y z : A}
    → (x : A) → y ≡ z → x ≡ y → x ≡ z
  ≡⟨⟩-syntax = step-≡

  infixr 2 ≡⟨⟩-syntax
  syntax ≡⟨⟩-syntax x y (λ i → B) = x ≡[ i ]⟨ B ⟩ y

  _≡⟨⟩_
    : {y : A}
    → (x : A) → x ≡ y → x ≡ y
  _ ≡⟨⟩ x≡y = x≡y

  ≡⟨⟩⟨⟩-syntax
    : {z w : A}
    → (x y : A) → x ≡ y → y ≡ z → z ≡ w → x ≡ w
  ≡⟨⟩⟨⟩-syntax x y p q r = p ∙∙ q ∙∙ r
  infixr 3 ≡⟨⟩⟨⟩-syntax
  syntax ≡⟨⟩⟨⟩-syntax x y B C = x ≡⟨ B ⟩≡ y ≡⟨ C ⟩≡

  _≡⟨_⟩≡⟨_⟩_
    : {y z w : A}
    → (x : A) → x ≡ y → y ≡ z → z ≡ w → x ≡ w
  _ ≡⟨ x≡y ⟩≡⟨ y≡z ⟩ z≡w = x≡y ∙∙ y≡z ∙∙ z≡w

transportRefl³ : {A : Set} (a : A)
  → transport refl (transport refl (transport refl a))
  ≡ a
transportRefl³ a =
  transport refl (transport refl (transport refl a))
    ≡⟨ cong (transport refl) (cong (transport refl) (transportRefl a)) ⟩
  transport refl (transport refl a)
    ≡⟨ cong (transport refl) (transportRefl a) ⟩
  transport refl a
    ≡⟨ transportRefl a ⟩
  a
    ∎
