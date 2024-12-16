module Prelude where

open import Agda.Builtin.Equality.Rewrite public
open import Agda.Primitive                public

open import Function.Base                 public
  using (id; _$_)

open import Data.Empty                    public
open import Data.Unit                     public
open import Data.Product                  public

open import Relation.Binary.PropositionalEquality.WithK public
open import Relation.Binary.PropositionalEquality       public
  using (_≡_; refl; sym; trans; cong; cong₂; trans-symˡ; subst-subst; module ≡-Reasoning)
  renaming (subst to tr; dcong to apd)
open import Relation.Binary.HeterogeneousEquality       public
  using (_≅_; refl; ≅-to-≡; ≡-to-≅; module ≅-Reasoning)

module Eq  = Relation.Binary.PropositionalEquality
module HEq = Relation.Binary.HeterogeneousEquality

private variable
  ℓ ℓ' ℓ'' : Level
  A B C : Set ℓ

conv : A ≡ B → A → B
conv = tr id

conv² : (p : A ≡ B)(q : B ≡ C){x : A}
      → conv q (conv p x) ≡ conv (trans p q) x
conv² p q = subst-subst p {q} 

cvtr :  (p : A ≡ B)(q : B ≡ C)
      → {a : A}{b : B}{c : C}
      → conv p a ≡ b → conv q b ≡ c
      → conv (trans p q) a ≡ c
cvtr p q refl refl = sym (conv² p q)

syntax cvtr p q eq1 eq2 = eq1 ⟫ p , q ⟫ eq2

conv-unique : {A B : Set ℓ}(p q : A ≡ B)(a : A) → conv p a ≡ conv q a
conv-unique refl refl _ = refl

conv~unique : {A B C : Set ℓ}(p : A ≡ B)(q : A ≡ C)(a : A) → conv p a ≅ conv q a
conv~unique refl refl _ = refl

conv-rm : {A B : Set ℓ}(p : A ≡ B)(a : A) → conv p a ≅ a
conv-rm p a = conv~unique p refl a

tr-conv : {X : Set ℓ}{Y : X → Set ℓ'}{x x' : X}{y : Y x}
        → (p : x ≡ x') → tr Y p y ≡ conv (cong Y p) y
tr-conv refl = refl

tr-comp : {X : Set ℓ}{Y : X → Set ℓ'}{Z : (x : X) → Set ℓ''}
           {x x' : X}{y : Y x}{y' : Y x'}
        → (f : {x : X}(y : Y x) → Z x)(p : x ≡ x') → tr Y p y ≡ y'
        → tr Z p (f y) ≡ f y'
tr-comp f refl refl = refl

conv-in-func : {X : Set ℓ}{Y : X → Set ℓ'}{Z : X → Set ℓ''}{x x' : X}
             → (x≡x' : x ≡ x')(f : {x : X} → Y x → Z x)(eq : Y x ≡ Y x')(y : Y x)(eq' : Z x ≡ Z x')
             → f (conv eq y) ≡ conv eq' (f y)
conv-in-func refl f refl y refl = refl

apd' : {X : Set ℓ}{Y : X → Set ℓ'}(f : (x : X) → Y x){x x' : X}
     → (x≡x' : x ≡ x') → conv (cong Y x≡x') (f x) ≡ f x'
apd' f refl = refl 