module Prelude where

open import Agda.Primitive public
open import Data.Empty public
open import Data.Unit public
open import Data.Product public
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning) renaming (subst to tr) public
open ≡-Reasoning public

apd : ∀{l l'}{A : Set l}{B : A → Set l'}{a a' : A}
    → (f : (a : A) → B a)(p : a ≡ a')
    → tr B p (f a) ≡ f a'
apd f refl = refl 