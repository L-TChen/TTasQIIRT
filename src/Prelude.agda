module Prelude where

open import Cubical.Foundations.Prelude public
  hiding (Sub)
open import Cubical.Data.Sigma          public
  hiding (Sub)
open import Cubical.Data.Empty          public
open import Cubical.Data.Unit           public
  renaming (tt to ⋆)
open import Cubical.Data.Nat            public
  using (ℕ; zero; suc; _+_)
open import Cubical.Data.Bool           public
  using (Bool; true; false)
open import Agda.Builtin.Equality public
  renaming (_≡_ to _≣_)
open import Agda.Builtin.Equality.Rewrite public

{-
infix 4 _≣_ _≡≡_
data _≡≡_ {l : Level} {A : Set l} (x : A) : {B : Set l}(y : B) → Prop l where
  instance refl : x ≡≡ x

_≣_ : {l : Level}{A : Set l}(x y : A) → Prop l
x ≣ y = x ≡≡ y

infix  1 ∃
data ∃ {l m : Level}(A : Set l)(P : A → Prop m) : Prop (l ⊔ m) where
  _,_ : (x : A)(p : P x) → ∃ A P

syntax ∃ A (λ x → P) = ∃ x ∶ A , P
-}

PathToId
  : ∀ {ℓ} {A : Set ℓ} {x y : A}
  → x ≡ y → x ≣ y
PathToId {ℓ} {A} {x} {y} p = J (λ y p → x ≣ y) refl p

IdToPath
  : ∀ {ℓ} {A : Set ℓ} {x y : A}
  → x ≣ y → x ≡ y
IdToPath {_} {A} {x} {y} refl i = x

J≣
  : ∀ {ℓ ℓ'} {A : Set ℓ} {x y : A} (P : ∀ y → x ≣ y → Set ℓ') (d : P x refl) (p : x ≣ y)
  → P y p
J≣ P d refl = d
