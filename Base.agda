-- {-# OPTIONS --cubical --exact-split #-}
{-# OPTIONS --exact-split --rewriting --double-check -vtc.cover.splittree:10 #-}
module DTT-QIIRT.Base where

-- open import Cubical.Core.Primitives
import Relation.Binary.PropositionalEquality as Eq
open import Agda.Builtin.Equality.Rewrite
open Eq using (_≡_; refl; subst; sym; cong)
open Eq.≡-Reasoning

-- inductive-inductive-recursive definition of context, type, term, and type substitution

infixl 35 _[_]ᵀ _[_]
infix  30 ƛ_ _·vz
infix  20 _‣_

data Ctx : Set
data Ty  : Ctx → Set
data Tm  : (Γ : Ctx) → Ty Γ → Set
data Sub : Ctx → Ctx → Set

_[_]ᵀ : ∀{Δ Γ} → Ty Γ → Sub Δ Γ → Ty Δ

data Ctx where
    ∅
      : Ctx
    _‣_
      : (Γ : Ctx) (A : Ty Γ)
      → Ctx

variable
    Γ Γ' Γ'' Δ Δ' Θ Θ' Φ : Ctx
    A A' A'' B B' B'' : Ty _
    t t' s s' : Tm _ _

data Sub where
  ∅
    ---------
    : Sub Δ ∅
  _‣_
    : (σ : Sub Δ Γ) (t : Tm Δ (A [ σ ]ᵀ))
    ---------------------------------
    → Sub Δ (Γ ‣ A)
  idS
    : Sub Δ Δ
  _⨾_
    : (σ : Sub Δ Γ) (δ : Sub Θ Δ)
    → Sub Θ Γ
  π₁
   : (σ : Sub Δ (Γ ‣ A))
   → Sub Δ Γ

data Ty where
  U
    : Ty Γ
  El
    : (u : Tm Γ U)
    --------------
    → Ty Γ
  Π
    : (A : Ty Γ) (B : Ty (Γ ‣ A))
    ------------------------------
    → Ty Γ

data Tm where
  π₂
    : (σ : Sub Δ (Γ ‣ A))
    → Tm Δ (A [ π₁ σ ]ᵀ)
  ƛ_
    : Tm (Γ ‣ A) B
    → Tm Γ (Π A B)
  _·vz
    : Tm Γ (Π A B)
    → Tm (Γ ‣ A) B
  _[_]
    : Tm Γ A → (σ : Sub Δ Γ)
    → Tm Δ (A [ σ ]ᵀ)

-- type substitution as recursion
_↑_ : (σ : Sub Δ Γ)(A : Ty Γ) → Sub (Δ ‣ A [ σ ]ᵀ) (Γ ‣ A)

{-# TERMINATING #-}
U [ σ ]ᵀ        = U

El u [ idS ]ᵀ   = El u
El u [ σ ⨾ τ ]ᵀ = El u [ σ ]ᵀ [ τ ]ᵀ
El u [ σ ]ᵀ     = El (u [ σ ])

Π A B [ idS ]ᵀ   = Π A B
Π A B [ σ ⨾ τ ]ᵀ = Π A B [ σ ]ᵀ [ τ ]ᵀ
Π A B [ σ ]ᵀ     = Π (A [ σ ]ᵀ) (B [ σ ↑ A ]ᵀ)

σ ↑ U     = (σ ⨾ π₁ idS) ‣ π₂ idS
σ ↑ El _  = (σ ⨾ π₁ idS) ‣ π₂ idS
σ ↑ Π _ _ = (σ ⨾ π₁ idS) ‣ π₂ idS

-- equalities of types
_[idS]ᵀ : (A : Ty Γ) → A [ idS ]ᵀ ≡ A
U     [idS]ᵀ = refl
El u  [idS]ᵀ = refl
Π A B [idS]ᵀ = refl

_[⨾]ᵀ : (A : Ty Γ){σ : Sub Δ Γ}{τ : Sub Θ Δ} → A [ σ ⨾ τ ]ᵀ ≡ A [ σ ]ᵀ [ τ ]ᵀ
U     [⨾]ᵀ = refl
El u  [⨾]ᵀ = refl
Π A B [⨾]ᵀ = refl

{-# REWRITE _[idS]ᵀ _[⨾]ᵀ #-}

-- equalities of substitutions
postulate
  idS⨾_
    : (σ : Sub Δ Γ)
    → idS ⨾ σ ≡ σ
  _⨾idS
    : (σ : Sub Δ Γ)
    → σ ⨾ idS ≡ σ
  assocS
    : {σ : Sub Δ Γ}{τ : Sub Θ Δ}{υ : Sub Φ Θ}
    → (σ ⨾ τ) ⨾ υ ≡ σ ⨾ (τ ⨾ υ)
  ‣⨾
    : {σ : Sub Δ Γ}{t : Tm Δ (A [ σ ]ᵀ)}{τ : Sub Θ Δ}
    → (_‣_ {A = A} σ t) ⨾ τ ≡ (σ ⨾ τ) ‣ t [ τ ]
  βπ₁
    : {σ : Sub Δ Γ}{t : Tm Δ (A [ σ ]ᵀ)} → π₁ (_‣_ {A = A} σ t) ≡ σ
  ηπ
    : {σ : Sub Δ (Γ ‣ A)}
    → π₁ σ ‣ π₂ σ ≡ σ
  η∅
    : {σ : Sub Δ ∅}
    → σ ≡ ∅

idS↑ : (A : Ty Γ) → idS ↑ A ≡ idS
idS↑ U       =
    (idS ⨾ π₁ idS) ‣ π₂ idS
  ≡⟨ cong (_‣ π₂ idS) (idS⨾ π₁ idS) ⟩
      π₁ idS ‣ π₂ idS
  ≡⟨ ηπ ⟩
      idS
  ∎
idS↑ (El u)  = {!!}
idS↑ (Π A B) = {!!}

{-# REWRITE idS↑ #-}

Π[] : {A : Ty Γ}{B : Ty (Γ ‣ A)}(σ : Sub Δ Γ)
  → Π A B [ σ ]ᵀ ≡ Π (A [ σ ]ᵀ) (B [ σ ↑ A ]ᵀ)
Π[] idS     = refl
Π[] (σ ⨾ τ) = {!   !}
Π[] ∅       = refl
Π[] (σ ‣ t) = refl
Π[] (π₁ σ)  = refl

-- common syntax
wk : Sub (Δ ‣ A) Δ
wk = π₁ idS

vz : Tm (Γ ‣ A) (A [ wk ]ᵀ)
vz = π₂ idS

vs : Tm Γ A → Tm (Γ ‣ B) (A [ wk ]ᵀ)
vs x = x [ wk ]

vz:= : Tm Γ A → Sub Γ (Γ ‣ A)
vz:= {Γ} {A} t = idS ‣ subst (Tm Γ) (sym (A [idS]ᵀ)) t

_·_ : Tm Γ (Π A B) → (s : Tm Γ A) → Tm Γ (B [ vz:= s ]ᵀ)
t · s = (t ·vz) [ vz:= s ]

-- -- Use equality constructor instead or postulate
-- data _⟶⟨_⟩_ : Tm Γ A → A ≡ B → Tm Γ B → Set where
--     [idS] : t [ idS ] ⟶⟨ A [idS]ᵀ ⟩ t  -- subst (Tm Γ) (A [idS]ᵀ) (t [ idS ]) ⟶ t
--     [⨾] : {t : Tm Γ A}{σ : Sub Δ Γ}{τ : Sub Θ Δ} → (t [ σ ⨾ τ ]) ⟶⟨ A [⨾]ᵀ ⟩ t [ σ ] [ τ ] -- subst (Tm Θ) (A [⨾]ᵀ) (t [ σ ⨾ τ ]) ⟶ t [ σ ] [ τ ]
--     ƛ[] : {t : Tm (Γ ‣ A) B}{σ : Sub Δ Γ} → (ƛ t) [ σ ] ⟶⟨ Π[] {A = A} ⟩ ƛ t [ σ ↑ A ] -- subst (Tm Δ) (Π[] {A = A}) ((ƛ t) [ σ ]) ⟶ ƛ t [ σ ↑ A ]
--     βπ₂ : {σ : Sub Δ Γ}{t : Tm Δ (A [ σ ]ᵀ)} → π₂ (_‣_ {A = A} σ t) ⟶⟨ cong (A [_]ᵀ) βπ₁ ⟩ t -- subst (λ τ → Tm Δ (A [ τ ]ᵀ)) βπ₁ (π₂ (_‣_ {A = A} σ t)) ⟶ t
--     βΠ : {t : Tm (Γ ‣ A) B} → (ƛ t) ·vz ⟶⟨ refl ⟩ t
--     ηΠ : {t : Tm Γ (Π A B)} → ƛ (t ·vz) ⟶⟨ refl ⟩ t
