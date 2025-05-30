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
  renaming (_≡_ to _≣_; refl to reflId)

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
PathToId {ℓ} {A} {x} {y} p = J (λ y p → x ≣ y) reflId p

IdToPath
  : ∀ {ℓ} {A : Set ℓ} {x y : A}
  → x ≣ y → x ≡ y
IdToPath {_} {A} {x} {y} reflId i = x

J≣
  : ∀ {ℓ ℓ'} {A : Set ℓ} {x y : A} (P : ∀ y → x ≣ y → Set ℓ') (d : P x reflId) (p : x ≣ y)
  → P y p
J≣ P d reflId = d

congId
  : {ℓ : Level} {A : Type ℓ} {ℓ' : Level}
    {B : Type ℓ'} {x y : A} (f : A → B) (p : x ≣ y)
  → (f x) ≣ (f y)
congId f reflId = reflId

trans
  : ∀ {ℓ} {A : Set ℓ} {x y z : A}
  → x ≣ y → y ≣ z
  → x ≣ z
trans reflId reflId = reflId
