module Prelude where

open import Agda.Builtin.Equality.Rewrite public
open import Agda.Primitive                public

open import Function.Base                 public
  using (id; _$_; _∘_)

open import Data.Empty                    public
open import Data.Unit                     public
open import Data.Product                  public
open import Data.Product.Properties       public
  using (Σ-≡,≡→≡; Σ-≡,≡←≡)

open import Data.Nat                      public
  using (ℕ; suc; zero)

open import Relation.Binary.PropositionalEquality.WithK public
open import Axiom.UniquenessOfIdentityProofs.WithK      public
  using (uip)
open import Relation.Binary.PropositionalEquality       public
  using (_≡_; refl; sym; trans; cong; cong₂; trans-symˡ; trans-symʳ; J; module ≡-Reasoning)
  renaming (subst to tr; dcong to apd; dcong₂ to apd₂;
            subst-∘ to tr-cong; subst-subst to tr²; subst-application′ to tr-nat;
            subst-subst-sym to tr-tr-sym; subst-sym-subst to tr-sym-tr)
open import Relation.Binary.HeterogeneousEquality       public
  using (_≅_; refl; ≅-to-≡; ≡-to-≅; module ≅-Reasoning)
  using (icong; icong₂)
  renaming (cong to hcong; cong₂ to hcong₂)

module Eq  = Relation.Binary.PropositionalEquality
module HEq = Relation.Binary.HeterogeneousEquality

private variable
  ℓ ℓ' ℓ'' : Level
  A B C : Set ℓ

tr₂ : ∀ (_∼_ : A → B → Set ℓ) {x y u v} → x ≡ y → u ≡ v → x ∼ u → y ∼ v
tr₂ _∼_ {x} {y} {u} {v} p q x∼u = tr (λ x → x ∼ v) p (tr (λ v → x ∼ v) q x∼u)

conv : A ≡ B → A → B
conv = tr id

{-
cvtr :  (p : A ≡ B)(q : B ≡ C)
      → {a : A}{b : B}{c : C}
      → conv p a ≡ b → conv q b ≡ c
      → conv (trans p q) a ≡ c
cvtr p _ refl refl = sym (tr² p)

syntax cvtr p q eq1 eq2 = eq1 ⟫ p , q ⟫ eq2
-}

tr-unique
  : {A : Set ℓ}(P : A → Set ℓ'){x y : A} (p q : x ≡ y)(a : P x)
  → tr P p a ≡ tr P q a
tr-unique P p q a = cong (λ p → tr P p a) (uip p q) 

conv-unique : {A B : Set ℓ}(p q : A ≡ B)(a : A) → conv p a ≡ conv q a
conv-unique = tr-unique id

conv~unique : {A B C : Set ℓ}(p : A ≡ B)(q : A ≡ C)(a : A) → conv p a ≅ conv q a
conv~unique refl refl _ = refl

conv-rm : {A B : Set ℓ}(p : A ≡ B)(a : A) → conv p a ≅ a
conv-rm p a = conv~unique p refl a

{-
tr-conv : {X : Set ℓ}{Y : X → Set ℓ'}{x x' : X}{y : Y x}
        → (p : x ≡ x') → tr Y p y ≡ tr id (cong Y p) y
tr-conv p = tr-cong p
-}

{-
tr-comp : {X : Set ℓ}{Y : X → Set ℓ'}{Z : (x : X) → Set ℓ''}
           {x x' : X}{y : Y x}{y' : Y x'}
        → (f : {x : X}(y : Y x) → Z x)(p : x ≡ x') → tr Y p y ≡ y'
        → tr Z p (f y) ≡ f y'
tr-comp f refl refl = refl
-}

conv-in-func : {X : Set ℓ}{Y : X → Set ℓ'}{Z : X → Set ℓ''}{x x' : X}
             → (x≡x' : x ≡ x')(f : {x : X} → Y x → Z x)(eq : Y x ≡ Y x')(y : Y x)(eq' : Z x ≡ Z x')
             → f (conv eq y) ≡ conv eq' (f y)
conv-in-func refl f refl y refl = refl

{-
apd' : {X : Set ℓ}{Y : X → Set ℓ'}(f : (x : X) → Y x){x x' : X}
     → (x≡x' : x ≡ x') → conv (cong Y x≡x') (f x) ≡ f x'
apd' f refl = refl
-}
to-Σ≡ : {X : Set ℓ}{Y : X → Set ℓ'}{x x' : X}(x≡x' : x ≡ x'){y : Y x}{y' : Y x'}
      → conv (cong Y x≡x') y ≡ y'
      → _≡_ {A = Σ X Y} (x , y) (x' , y')
to-Σ≡ refl refl = refl

from-Σ≡ : {X : Set ℓ}{Y : X → Set ℓ'}{x x' : X}{y : Y x}{y' : Y x'}
        → _≡_ {A = Σ X Y} (x , y) (x' , y')
        → Σ[ p ∈ x ≡ x' ] tr Y p y ≡ y'
from-Σ≡ refl = refl , refl

infix 10 _,Σ≡_
_,Σ≡_ : {X : Set ℓ}{Y : X → Set ℓ'}{x x' : X}{y : Y x}{y' : Y x'}(x≡x' : x ≡ x')
      → tr Y x≡x' y ≡ y'
      → _≡_ {A = Σ X Y} (x , y) (x' , y')
_,Σ≡_ = curry Σ-≡,≡→≡

{-
UIP : {X : Set ℓ}{x y : X}(p q : x ≡ y) → p ≡ q
UIP refl refl = refl 
-}

apdΣ
  : {A : Set ℓ} {B : A → Set ℓ'} (f : (x : A) → B x) {x y : A}
  → (p : x ≡ y) → _≡_ {_} {Σ A B} (x , f x) (y , f y)
apdΣ f refl = refl

apΣ
  : {B : Set ℓ} (P : B → Set ℓ') {A : Set ℓ''} (f : A → B)
  → {(x , t) (y , u) : Σ A (λ x → P (f x)) }
  → (x , t) ≡ (y , u)
  → _≡_ {_} {Σ B P} (f x , t) (f y , u)
apΣ P f refl = refl

ap₂Σ
  : {A : Set ℓ} {B : A → Set ℓ'} {C : A → Set ℓ''}(f : {x : A} → B x → C x)
    {x x' : A}{y : B x}{y' : B x'}
  → _≡_ {_} {Σ A B} (x , y) (x' , y') → _≡_ {_} {Σ A C} (x , f y) (x' , f y')
ap₂Σ f refl = refl 

ap,Σ : {A : Set ℓ}{B : Set ℓ'}{C : B → Set ℓ''}
       (f : A → B)(g : (x : A) → C (f x))
       {x y : A}
     → x ≡ y
     → _≡_ {_} {Σ B C} (f x , g x) (f y , g y)
ap,Σ f g refl = refl

lift : (P : A → Set) {x y : A} (t : P x)
  → (p : x ≡ y)
  → (x , t) ≡ (y , tr P p t)
lift P t refl = refl

cong₃ : ∀{a b c d} 
      → {A : Set a}{B : A → Set b}{C : A → Set c}{D : Set d}
        {x y : A}{u₁ : B x}{v₁ : B y}{u₂ : C x}{v₂ : C y}
        (f : (z : A)(w₁ : B z)(w₂ : C z) → D)
      → (p : x ≡ y) → tr B p u₁ ≡ v₁ → tr C p u₂ ≡ v₂
      → f x u₁ u₂ ≡ f y v₁ v₂
cong₃ {x = x} f refl = cong₂ (f x)

module _ {a b c : Level} {I : Set ℓ} (A : I → Set a) {B : {k : I} → A k → Set b} where
  icong₃ : {C : {k : I} → (a : A k) → B a → B a → Set c}
           {i j : I} {x : A i} {y : A j} {u₁ u₂ : B x} {v₁ v₂ : B y} →
           i ≡ j →
           (f : {k : I} → (z : A k) → (w₁ w₂ : B z) → C z w₁ w₂) →
           x ≅ y → u₁ ≅ v₁ → u₂ ≅ v₂ →
           f x u₁ u₂ ≅ f y v₁ v₂
  icong₃ refl _ refl refl refl = refl

tr-const
  : {A : Set ℓ} {B : Set ℓ'} {x y : A} (p : x ≡ y) {b : B}
  → tr (λ _ → B) p b ≡ b
tr-const refl = refl

infixr 30 _∙_
_∙_ : {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
p ∙ q = trans p q

tr≡-to-≅
  : {A : Set ℓ} (P : A → Set ℓ') {x y : A} {u : P x} {v : P y}
  → (p : x ≡ y)
  → tr P p u ≡ v → u ≅ v
tr≡-to-≅ P refl eq = ≡-to-≅ eq

tr≅ : ∀{ℓ ℓ'}{A : Set ℓ}(P : A → Set ℓ'){x y : A}(p : x ≡ y)(a : P x)
    → tr P p a ≅ a
tr≅ P p a = tr≡-to-≅ P (sym p) (trans (tr² p) (cong (λ p' → tr P p' a) (trans-symʳ p)))

flip-tr : {X : Set ℓ}{Y : X → Set ℓ'}{x x' : X}{y : Y x}{y' : Y x'}{p : x ≡ x'}
        → tr Y p y ≡ y' → tr Y (sym p) y' ≡ y
flip-tr {Y = Y} {y = y} {y'} {p} eq = begin
  tr Y (sym p) y'
    ≡⟨ cong (tr Y (sym p)) (sym eq) ⟩
  tr Y (sym p) (tr Y p y)
    ≡⟨ tr-sym-tr p ⟩
  y
    ∎
  where open ≡-Reasoning


{-
apd₂′ : {A : Set ℓ} {B : A → Set ℓ'} {C : (x : A) (y : B x) → Set ℓ''}
  → (f : (x : A) (y : B x) → C x y)
  → {x₁ x₂ : A} (p : x₁ ≡ x₂)
  → {y₁ : B x₁} {y₂ : B x₂} (q : tr B p y₁ ≡ y₂)
  → tr (C x₂) q (f x₂ (tr B p y₁)) ≡ f x₂ y₂
apd₂′ {A = A} {B} {C} f {x₁} {x₂} p {y₁} {y₂} q = apd {B = (C x₂)} (f x₂) q
-}
