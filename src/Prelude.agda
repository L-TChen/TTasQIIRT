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
  renaming (elim to elim-⊥)
open import Cubical.Data.Unit           public
  renaming (tt to ⋆)
open import Cubical.Data.Nat            public
  using (ℕ; zero; suc; _+_)
open import Cubical.Data.Bool           public
  using (Bool; true; false)

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

-- PathP-fam : {A : Set ℓ'} {P : A → Type ℓ} {x y : A} → P x → (e : x ≡ y) → P y → Type ℓ
-- PathP-fam {P = P} {x} {y} px e py = PathP (λ i → P (e i)) px py
-- 
-- syntax PathP-fam px e py = px ≡[ e ] py

-- Syntax for chains of equational reasoning

-- step-≡'
--   : {P : A → Type ℓ} {x y z : A} (px : P x) {py : P y} {e' : y ≡ z} {pz : P z} 
--   → {p : py ≡[ e' ] pz} → (e : x ≡ y) → px ≡[ e ] py → px ≡[ e ∙ e' ] pz
-- step-≡' px {py} {e'} {pz} {p} e q = {!!}  -- compPathP q p 
-- 
-- syntax step-≡' px p e py = px ≡[ e ]⟨ p ⟩ py

-- ≡⟨⟩-syntax : (x : A) → y ≡ z → x ≡ y → x ≡ z
-- ≡⟨⟩-syntax = step-≡

-- infixr 2 ≡⟨⟩-syntax
-- syntax ≡⟨⟩-syntax x y (λ i → B) = x ≡[ i ]⟨ B ⟩ y

-- _≡⟨⟩_ : (x : A) → x ≡ y → x ≡ y
-- _ ≡⟨⟩ x≡y = x≡y

-- ≡⟨⟩⟨⟩-syntax : (x y : A) → x ≡ y → y ≡ z → z ≡ w → x ≡ w
-- ≡⟨⟩⟨⟩-syntax x y p q r = p ∙∙ q ∙∙ r
-- infixr 3 ≡⟨⟩⟨⟩-syntax
-- syntax ≡⟨⟩⟨⟩-syntax x y B C = x ≡⟨ B ⟩≡ y ≡⟨ C ⟩≡

-- _≡⟨_⟩≡⟨_⟩_ : (x : A) → x ≡ y → y ≡ z → z ≡ w → x ≡ w
-- _ ≡⟨ x≡y ⟩≡⟨ y≡z ⟩ z≡w = x≡y ∙∙ y≡z ∙∙ z≡w

-- _∎ : (x : A) → x ≡ x
-- _ ∎ = refl
