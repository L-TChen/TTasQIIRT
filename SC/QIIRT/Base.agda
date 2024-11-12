-- {-# OPTIONS --cubical #-}
-- {-# OPTIONS --exact-split --rewriting -vtc.cover.splittree:10 #-}
-- Formalizing Substitution Calculus as QIIRT
module SC.QIIRT.Base where

open import Prelude
-- open import Cubical.Core.Primitives

-- inductive-inductive-recursive definition of context, type, term, and type substitution

infixl 35 _[_] _[_]t _[_]tm
infix  20 _‣_

data Ctx : Set
data Ty  : Ctx → Set
data Sub : Ctx → Ctx → Set
data Tm  : (Γ : Ctx) → Ty Γ → Set

_[_]  : ∀{Δ Γ} → Ty Γ → Sub Δ Γ → Ty Δ
 
variable
    Γ Γ' Γ'' Δ Δ' Θ Θ' Φ : Ctx
    A A' A'' B B' B'' : Ty Γ
    t t' s s' : Tm Γ A
    σ σ' τ τ' : Sub Δ Γ

data Ctx where
  ∅
    : Ctx
  _‣_
    : (Γ : Ctx) (A : Ty Γ)
    → Ctx

data Sub where
  ∅
    ---------
    : Sub Δ ∅
  _‣_
    : (σ : Sub Δ Γ) (t : Tm Δ (A [ σ ]))
    ------------------------------------
    → Sub Δ (Γ ‣ A)
  idS
    : Sub Δ Δ
  _∘_
    : {Γ Δ Θ : Ctx}
    → (σ : Sub Δ Γ) (δ : Sub Θ Δ)
    → Sub Θ Γ
  π₁
   : (σ : Sub Δ (Γ ‣ A))
   → Sub Δ Γ

data Ty where
  U
    : Ty Γ

data Tm where
  π₂
    : (σ : Sub Δ (Γ ‣ A))
    → Tm Δ (A [ π₁ σ ])
  _[_]tm
    : Tm Γ A → (σ : Sub Δ Γ)
    → Tm Δ (A [ σ ])

-- type substitution as recursion
-- pattern matching on types first
U [ σ ]        = U

_[_]t : {Γ Δ : Ctx} {A : Ty Γ} (t : Tm Γ A) (σ : Sub Δ Γ)
      → Tm Δ (A [ σ ])
_[_]t {Γ} {_} {U} t idS = t
_[_]t {_} {Δ} {U} t (σ ∘ τ) = t [ σ ]t [ τ ]t
_[_]t {A = U} t ∅ = t [ ∅ ]tm
_[_]t {Γ} {Δ} {U} t (σ ‣ s) = t [ σ ‣ s ]tm
_[_]t {A = U} t (π₁ σ) = t [ π₁ σ ]tm

-- equalities of substitutions
postulate
  idS∘_ 
    : (σ : Sub Δ Γ)
    → idS ∘ σ ≡ σ
  _∘idS
    : (σ : Sub Δ Γ)
    → σ ∘ idS ≡ σ
  assocS
    : {σ : Sub Δ Γ}{τ : Sub Θ Δ}{υ : Sub Φ Θ}
    → (σ ∘ τ) ∘ υ ≡ σ ∘ (τ ∘ υ)
  ‣∘ -- only defined on terms of type U
    : {σ : Sub Δ Γ}{t : Tm Δ U}{τ : Sub Θ Δ}
    → (_‣_ σ t) ∘ τ ≡ (σ ∘ τ) ‣ (t [ τ ]t)
  βπ₁
    : {σ : Sub Δ Γ}{t : Tm Δ (A [ σ ])}
    → π₁ (_‣_ {A = A} σ t) ≡ σ
  βπ₂
    : {σ : Sub Δ Γ}{t : Tm Δ (A [ σ ])}
    → π₂ (_‣_ {A = A} σ t) ≡ t
  ηπ
    : {σ : Sub Δ (Γ ‣ A)}
    → π₁ σ ‣ π₂ σ ≡ σ
  η∅
    : {σ : Sub Δ ∅}
    → σ ≡ ∅

π₁∘ : (σ : Sub Δ (Γ ‣ A))(τ : Sub Θ Δ) → π₁ (σ ∘ τ) ≡ π₁ σ ∘ τ
π₁∘ {A = U} {Θ} σ τ =
    π₁ (σ ∘ τ)
  ≡⟨ cong (λ σ' → π₁ (σ' ∘ τ)) (sym ηπ) ⟩
    π₁ ((π₁ σ ‣ π₂ σ) ∘ τ)
  ≡⟨ cong π₁ ‣∘ ⟩
    π₁ ((π₁ σ ∘ τ) ‣ π₂ σ [ τ ]t)
  ≡⟨ βπ₁ {σ = π₁ σ ∘ τ} ⟩
    π₁ σ ∘ τ
  ∎

π₁idS∘ : {A : Ty Γ}(σ : Sub Δ (Γ ‣ A)) → π₁ idS ∘ σ ≡ π₁ σ
π₁idS∘ σ =
    π₁ idS ∘ σ
  ≡⟨ sym (π₁∘ idS σ) ⟩
    π₁ (idS ∘ σ)
  ≡⟨ cong π₁ (idS∘ σ) ⟩
    π₁ σ
  ∎

-- only on case when A = U
π₂∘ : (σ : Sub Δ (Γ ‣ U))(τ : Sub Θ Δ) → π₂ (σ ∘ τ) ≡ π₂ σ [ τ ]t
π₂∘ σ τ =
    π₂ (σ ∘ τ)
  ≡⟨ cong (λ σ' → π₂ (σ' ∘ τ)) (sym ηπ) ⟩
    π₂ ((π₁ σ ‣ π₂ σ) ∘ τ)
  ≡⟨ cong π₂ ‣∘ ⟩
    π₂ ((π₁ σ ∘ τ) ‣ π₂ σ [ τ ]t)
  ≡⟨ βπ₂ {σ = π₁ σ ∘ τ} ⟩
    π₂ σ [ τ ]t
  ∎

-- syntax abbreviations
wk : Sub (Δ ‣ A) Δ
wk = π₁ idS

vz : Tm (Γ ‣ A) (A [ wk ])
vz = π₂ idS

vs : Tm Γ A → Tm (Γ ‣ B) (A [ wk ])
vs x = x [ wk ]t

vz:= : Tm Γ A → Sub Γ (Γ ‣ A)
vz:= {Γ} {U} t = idS ‣ t -- pattern matching on type

-- -- -- -- Use equality constructor instead or postulate
-- -- -- data _⟶⟨_⟩_ : Tm Γ A → A ≡ B → Tm Γ B → Set where
-- -- --     [idS] : t [ idS ] ⟶⟨ A [idS]ᵀ ⟩ t  -- subst (Tm Γ) (A [idS]ᵀ) (t [ idS ]) ⟶ t
-- -- --     [∘] : {t : Tm Γ A}{σ : Sub Δ Γ}{τ : Sub Θ Δ} → (t [ σ ∘ τ ]) ⟶⟨ A [∘]ᵀ ⟩ t [ σ ] [ τ ] -- subst (Tm Θ) (A [∘]ᵀ) (t [ σ ∘ τ ]) ⟶ t [ σ ] [ τ ]