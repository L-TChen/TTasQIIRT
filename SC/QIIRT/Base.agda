{-# OPTIONS --cubical #-}
-- {-# OPTIONS --exact-split --rewriting -vtc.cover.splittree:10 #-}
-- Formalizing Substitution Calculus as QIIRT
module SC.QIIRT.Base where

-- open import Prelude 
open import Cubical.Foundations.Prelude hiding (Sub)
open import Cubical.Foundations.Function hiding (_∘_)

-- inductive-inductive-recursive definition of context, type, term, and type substitution

infixl 35 _[_] _[_]tm
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

_‣'_ : (Γ : Ctx) (A : Ty Γ) → Ctx
π₁' : (σ : Sub Δ (Γ ‣' A)) → Sub Δ Γ
π₂' : (σ : Sub Δ (Γ ‣' A)) → Tm Δ (A [ π₁' σ ])
_[_]tm' : Tm Γ A → (σ : Sub Δ Γ) → Tm Δ (A [ σ ])

data Ctx where
  ∅
    : Ctx
  _‣_
    : (Γ : Ctx) (A : Ty Γ)
    → Ctx

_‣'_ = _‣_

data Ty where
  U
    : Ty Γ

-- type substitution as recursion
-- pattern matching on types first
U [ σ ]        = U

-- _[_]t : {Γ Δ : Ctx}(t : Tm Γ U)(σ : Sub Δ Γ) → Tm Δ (U [ σ ])

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
  
  -- paths
  idS∘_ 
    : (σ : Sub Δ Γ)
    → idS ∘ σ ≡ σ
  _∘idS
    : (σ : Sub Δ Γ)
    → σ ∘ idS ≡ σ
  assocS
    : {σ : Sub Δ Γ}{τ : Sub Θ Δ}{υ : Sub Φ Θ}
    → (σ ∘ τ) ∘ υ ≡ σ ∘ (τ ∘ υ)
  βπ₁
    : {σ : Sub Δ Γ}{t : Tm Δ (A [ σ ])}
    → π₁ (_‣_ {A = A} σ t) ≡ σ
  ηπ
    : {σ : Sub Δ (Γ ‣ A)}
    → π₁' σ ‣ π₂' σ ≡ σ
  η∅
    : {σ : Sub Δ ∅}
    → σ ≡ ∅
  ‣∘ -- only defined on terms of type U
    : {A : Ty Γ}{σ : Sub Δ Γ}{t : Tm Δ (A [ σ ])}{τ : Sub Θ Δ}
    → (_‣_ σ t) ∘ τ ≡ (σ ∘ τ) ‣ {! t [ τ ]tm'  !} -- (_‣_ σ t) ∘ τ ≡ (σ ∘ τ) ‣ (t [ τ ]tm')
  trunc : isSet (Sub Δ Γ)

data Tm where
  π₂
    : (σ : Sub Δ (Γ ‣ A))
    → Tm Δ (A [ π₁ σ ])
  _[_]tm
    : Tm Γ A → (σ : Sub Δ Γ)
    → Tm Δ (A [ σ ])
  
  -- path constructors
  βπ₂
    : {σ : Sub Δ Γ}{t : Tm Δ (U [ σ ])}
    → π₂ (_‣_ {A = U} σ t) ≡ t
  
  -- link
  --   : {t : Tm Γ U}{σ : Sub Δ Γ}
  --   → t [ σ ]tm ≡ t [ σ ]t

π₁' = π₁
π₂' = π₂
_[_]tm' = _[_]tm

Sub≡ : {σ σ' : Sub Δ Γ}(t : Tm Γ U) → σ ≡ σ' → t [ σ ]tm ≡ t [ σ' ]tm
Sub≡ t σ≡σ' i = t [ σ≡σ' i ]tm

{-
t [ idS ]t = t
t [ σ ∘ τ ]t = t [ σ ]t [ τ ]t -- t [ σ ]t [ τ ]t
_[_]t t ∅ = t [ ∅ ]tm
_[_]t t (σ ‣ s) = t [ σ ‣ s ]tm
_[_]t t (π₁ σ) = t [ π₁ σ ]tm
t [ (idS∘ σ) i ]t = t [ σ ]t
t [ (σ ∘idS) i ]t = t [ σ ]t
t [ assocS {σ = σ} {τ} {υ} i ]t = t [ σ ]t [ τ ]t [ υ ]t
t [ βπ₁ {σ = σ} {t'} i ]t = {!   !} -- (Sub≡ t (βπ₁ {σ = σ} {t'}) ∙ link) i
t [ η∅ {σ = σ} i ]t = {!   !} -- (sym link ∙ Sub≡ t (η∅ {σ = σ})) i
t [ ‣∘ {σ = σ} {t'} {τ} i ]t = {!   !} -- (sym link ∙ Sub≡ t (‣∘ {σ = σ} {t'} {τ})) i
t [ trunc σ σ' x y i j ]t = {!   !}
-}

-- -- derived computation rules on composition
-- π₁∘ : (σ : Sub Δ (Γ ‣ A))(τ : Sub Θ Δ) → π₁ (σ ∘ τ) ≡ π₁ σ ∘ τ
-- π₁∘ {A = U} {Θ} σ τ =
--     π₁ (σ ∘ τ)
--   ≡⟨ cong (λ σ' → π₁ (σ' ∘ τ)) (sym ηπ) ⟩
--     π₁ ((π₁ σ ‣ π₂ σ) ∘ τ)
--   ≡⟨ cong π₁ ‣∘ ⟩
--     π₁ ((π₁ σ ∘ τ) ‣ π₂ σ [ τ ]t)
--   ≡⟨ βπ₁ {σ = π₁ σ ∘ τ} ⟩
--     π₁ σ ∘ τ
--   ∎

-- π₁idS∘ : {A : Ty Γ}(σ : Sub Δ (Γ ‣ A)) → π₁ idS ∘ σ ≡ π₁ σ
-- π₁idS∘ σ =
--     π₁ idS ∘ σ
--   ≡⟨ sym (π₁∘ idS σ) ⟩
--     π₁ (idS ∘ σ)
--   ≡⟨ cong π₁ (idS∘ σ) ⟩
--     π₁ σ
--   ∎

-- -- only on case when A = U
-- π₂∘ : (σ : Sub Δ (Γ ‣ U))(τ : Sub Θ Δ) → π₂ (σ ∘ τ) ≡ π₂ σ [ τ ]t
-- π₂∘ σ τ =
--     π₂ (σ ∘ τ)
--   ≡⟨ cong (λ σ' → π₂ (σ' ∘ τ)) (sym ηπ) ⟩
--     π₂ ((π₁ σ ‣ π₂ σ) ∘ τ)
--   ≡⟨ cong π₂ ‣∘ ⟩
--     π₂ ((π₁ σ ∘ τ) ‣ π₂ σ [ τ ]t)
--   ≡⟨ βπ₂ {σ = π₁ σ ∘ τ} ⟩
--     π₂ σ [ τ ]t
--   ∎

-- syntax abbreviations
wk : Sub (Δ ‣ A) Δ
wk = π₁ idS

vz : Tm (Γ ‣ U) (U [ wk ])
vz = π₂ idS

vs : Tm Γ U → Tm (Γ ‣ U) (U [ wk ]) 
vs x = x [ wk ]tm

vz:= : Tm Γ A → Sub Γ (Γ ‣ A)
vz:= {Γ} {U} t = idS ‣ t -- pattern matching on type

-- -- -- -- Use equality constructor instead or postulate
-- -- -- data _⟶⟨_⟩_ : Tm Γ A → A ≡ B → Tm Γ B → Set where 
-- -- --     [idS] : t [ idS ] ⟶⟨ A [idS]ᵀ ⟩ t  -- subst (Tm Γ) (A [idS]ᵀ) (t [ idS ]) ⟶ t  
-- -- --     [∘] : {t : Tm Γ A}{σ : Sub Δ Γ}{τ : Sub Θ Δ} → (t [ σ ∘ τ ]) ⟶⟨ A [∘]ᵀ ⟩ t [ σ ] [ τ ] -- subst (Tm Θ) (A [∘]ᵀ) (t [ σ ∘ τ ]) ⟶ t [ σ ] [ τ ]