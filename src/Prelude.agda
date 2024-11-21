module Prelude where

open import Agda.Builtin.Equality.Rewrite public
open import Agda.Primitive public

open import Data.Empty     public
open import Data.Unit      public
open import Data.Product   public

open import Relation.Binary.PropositionalEquality.WithK public
open import Relation.Binary.PropositionalEquality as Eq

  using (_≡_; refl; sym; trans; cong; cong₂; trans-symˡ; module ≡-Reasoning) renaming (subst to tr) public
open ≡-Reasoning public

apd : ∀{l l'}{A : Set l}{B : A → Set l'}{a a' : A}
    → (f : (a : A) → B a)(p : a ≡ a')
    → tr B p (f a) ≡ f a'
apd f refl = refl 

conv : ∀{l}{A B : Set l} → A ≡ B → A → B
conv refl a = a

conv² : ∀{l}{A B C : Set l}
      → (p : A ≡ B)(q : B ≡ C){a : A}
      → conv q (conv p a) ≡ conv (trans p q) a
conv² refl _ = refl

cvtr : ∀{l}{A B C : Set l}(p : A ≡ B)(q : B ≡ C)
      → {a : A}{b : B}{c : C}
      → conv p a ≡ b → conv q b ≡ c
      → conv (trans p q) a ≡ c
cvtr p q refl refl = sym (conv² p q)

syntax cvtr p q eq1 eq2 = eq1 ⟫ p , q ⟫ eq2

conv-unique : ∀{l}{A B : Set l}(p q : A ≡ B)(a : A) → conv p a ≡ conv q a
conv-unique refl refl _ = refl

tr-conv : ∀{l l'}{X : Set l}{Y : X → Set l'}{x x' : X}{y : Y x}
        → (p : x ≡ x') → tr Y p y ≡ conv (cong Y p) y
tr-conv refl = refl

tr-comp : ∀{l l' l''}{X : Set l}{Y : X → Set l'}{Z : (x : X) → Set l''}
           {x x' : X}{y : Y x}{y' : Y x'}
        → (f : {x : X}(y : Y x) → Z x)(p : x ≡ x') → tr Y p y ≡ y'
        → tr Z p (f y) ≡ f y'
tr-comp f refl refl = refl
 