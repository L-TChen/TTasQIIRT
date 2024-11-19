-- {-# OPTIONS --cubical #-}
-- {-# OPTIONS --exact-split --rewriting -vtc.cover.splittree:10 #-}
-- Formalizing Substitution Calculus as QIIRT
module SC.QIIT.Base where

open import Prelude
-- open import Agda.Builtin.Equality.Rewrite
-- open import Cubical.Core.Primitives

-- inductive-inductive definition of context, type, term, and type substitution

infixl 35 _[_]ty _[_]tm
infix  10 _‣_

data Ctx : Set
data Ty  : Ctx → Set
data Sub : Ctx → Ctx → Set
data Tm  : (Γ : Ctx) → Ty Γ → Set
 
variable
    Γ Γ' Γ'' Δ Δ' Θ Θ' Φ : Ctx
    A A' A'' B B' B'' : Ty Γ
    t t' s s' : Tm Γ A
    σ σ' τ τ' : Sub Δ Γ

data Ctx where
  ∅
    ------
    : Ctx
  _‣_
    : (Γ : Ctx)(A : Ty Γ)
    ---------------------
    → Ctx

data Ty where
  U
    ------
    : Ty Γ
  _[_]ty
    : (A : Ty Γ)(σ : Sub Δ Γ)
    -------------------------
    → Ty Δ

data Sub where
  ∅
    ---------
    : Sub Δ ∅
  _‣_
    : (σ : Sub Δ Γ) (t : Tm Δ (A [ σ ]ty))
    --------------------------------------
    → Sub Δ (Γ ‣ A)
  idS
    ---------
    : Sub Δ Δ
  _∘_
    : {Γ Δ Θ : Ctx}
    → (σ : Sub Δ Γ) (δ : Sub Θ Δ)
    -----------------------------
    → Sub Θ Γ
  π₁
   : (σ : Sub Δ (Γ ‣ A))
   ---------------------
   → Sub Δ Γ

data Tm where
  π₂
    : (σ : Sub Δ (Γ ‣ A))
    ---------------------
    → Tm Δ (A [ π₁ σ ]ty)
  _[_]tm
    : (t : Tm Γ A)(σ : Sub Δ Γ)
    ---------------------------
    → Tm Δ (A [ σ ]ty)


{-
_[_]t : {Γ Δ : Ctx} {A : Ty Γ} (t : Tm Γ A) (σ : Sub Δ Γ)
      → Tm Δ (A [ σ ])
_[_]t {Γ} {_} {U} t idS = t
_[_]t {_} {Δ} {U} t (σ ∘ τ) = t [ σ ]t [ τ ]t
_[_]t {A = U} t ∅ = t [ ∅ ]tm
_[_]t {Γ} {Δ} {U} t (σ ‣ s) = t [ σ ‣ s ]tm
_[_]t {A = U} t (π₁ σ) = t [ π₁ σ ]tm
-}

-- equalities of substitutions
postulate
  -- equalities on types
  U[]
    : (σ : Sub Δ Γ)
    → U [ σ ]ty ≡ U
  [idS]
    : (A : Ty Γ)
    → A [ idS ]ty ≡ A
  [∘]
    : (A : Ty Γ)(σ : Sub Δ Γ)(τ : Sub Θ Δ)
    → A [ σ ∘ τ ]ty ≡ A [ σ ]ty [ τ ]ty
  
  -- equality on substitutions
  idS∘_ 
    : (σ : Sub Δ Γ)
    → idS ∘ σ ≡ σ
  _∘idS
    : (σ : Sub Δ Γ)
    → σ ∘ idS ≡ σ
  assocS
    : {σ : Sub Δ Γ}{τ : Sub Θ Δ}{υ : Sub Φ Θ}
    → (σ ∘ τ) ∘ υ ≡ σ ∘ (τ ∘ υ)
  ‣∘
    : {A : Ty Γ}{σ : Sub Δ Γ}{t : Tm Δ (A [ σ ]ty)}{τ : Sub Θ Δ}
    → (_‣_ {A = A} σ t) ∘ τ ≡ (σ ∘ τ) ‣ tr (Tm Θ) (sym ([∘] A σ τ)) (t [ τ ]tm)
  βπ₁
    : {σ : Sub Δ Γ}{t : Tm Δ (A [ σ ]ty)}
    → π₁ (_‣_ {A = A} σ t) ≡ σ
  ηπ
    : {σ : Sub Δ (Γ ‣ A)}
    → σ ≡ π₁ σ ‣ π₂ σ
  η∅
    : {σ : Sub Δ ∅}
    → σ ≡ ∅
  
  -- equality on terms
  [idS]tm
    : (t : Tm Γ A)
    → tr (Tm Γ) ([idS] A) (t [ idS ]tm) ≡ t
  [∘]tm
    : (t : Tm Γ A)(σ : Sub Δ Γ)(τ : Sub Θ Δ)
    → tr (Tm Θ) ([∘] A σ τ) (t [ σ ∘ τ ]tm) ≡ t [ σ ]tm [ τ ]tm
  βπ₂
    : {σ : Sub Δ Γ}{t : Tm Δ (A [ σ ]ty)}
    → tr (Tm Δ) (cong (A [_]ty) βπ₁) (π₂ (_‣_ {A = A} σ t)) ≡ t

-- coherence of postulates

{-
coh[idS∘] : {σ : Sub Δ Γ}{t : Tm Γ A} → t [ idS ∘ σ ]t ≡ t [ σ ]t
coh[idS∘] {A = U} = refl

coh[∘idS] : {σ : Sub Δ Γ}{t : Tm Γ A} → t [ σ ∘ idS ]t ≡ t [ σ ]t
coh[∘idS] {A = U} {σ} {t} = refl

coh[assocS]
  : {σ : Sub Δ Γ}{τ : Sub Θ Δ}{υ : Sub Φ Θ}{t : Tm Γ A}
  → t [ (σ ∘ τ) ∘ υ ]t ≡ t [ σ ∘ (τ ∘ υ) ]t
coh[assocS] {A = U} = refl

coh[‣∘]
  : {σ : Sub Δ Γ}{s : Tm Δ (A [ σ ])}{τ : Sub Θ Δ}{t : Tm (Γ ‣ A) B}
  → t [ (σ ‣ s) ∘ τ ]t ≡ t [ (σ ∘ τ) ‣ tr (Tm Θ) (sym ([∘] A σ τ)) (s [ τ ]t) ]t
coh[‣∘] {A = U} {Θ = Θ} {B = U} {σ = σ} {s} {τ} {t} =
    t [ (σ ‣ s) ∘ τ ]t
  ≡⟨ cong (t [_]t) (‣∘ {σ = σ} {s} {τ}) ⟩
    t [ (σ ∘ τ) ‣ tr (Tm Θ) (sym ([∘] U σ τ)) (s [ τ ]t) ]t
  ∎

coh[βπ₁]
  : {σ : Sub Δ Γ}{s : Tm Δ (A [ σ ])}{t : Tm Γ B}
  → t [ π₁ (_‣_ {A = A} σ s) ]t ≡ t [ σ ]t
coh[βπ₁] {A = U} {U} {σ} {s} {t} =
    t [ π₁ (σ ‣ s) ]t
  ≡⟨ cong (t [_]t) (βπ₁ {σ = σ} {s}) ⟩
    t [ σ ]t
  ∎ 

coh[βπ₂]
  : {σ : Sub Δ Γ}{t : Tm Δ (A [ σ ])}{τ : Sub Θ Δ}
  → π₂ (_‣_ {A = A} σ t) [ τ ]t ≡ t [ τ ]t
coh[βπ₂] {A = U} {_} {σ} {t} {τ} =
    π₂ (σ ‣ t) [ τ ]t
  ≡⟨ cong (_[ τ ]t) (βπ₂ {σ = σ} {t}) ⟩
    t [ τ ]t
  ∎

coh[ηπ]
  : {σ : Sub Δ (Γ ‣ A)}{t : Tm (Γ ‣ A) B}
  → tr (λ y → Tm Δ (B [ y ])) (ηπ {σ = σ}) (t [ σ ]t) ≡ t [ (π₁ σ ‣ π₂ σ) ]t
coh[ηπ] {σ = σ} {t} =
    tr _ (ηπ {σ = σ}) (t [ σ ]t)
  ≡⟨ (apd (t [_]t) (ηπ {σ = σ})) ⟩
    t [ π₁ σ ‣ π₂ σ ]t
  ∎

coh[η∅] : {σ : Sub Δ ∅}{t : Tm ∅ A} → tr (λ y → Tm Δ (A [ y ])) (η∅ {σ = σ}) (t [ σ ]t) ≡  t [ ∅ ]t
coh[η∅] {A = U} {σ = σ} {t} =
    tr _ η∅ (t [ σ ]t)
  ≡⟨ apd (t [_]t) (η∅ {σ = σ}) ⟩
    t [ ∅ ]t
  ∎
-}

-- derived computation rules on composition
π₁∘ : (σ : Sub Δ (Γ ‣ A))(τ : Sub Θ Δ) → π₁ (σ ∘ τ) ≡ π₁ σ ∘ τ
π₁∘ {A = A} {Θ} σ τ =
    π₁ (σ ∘ τ)
  ≡⟨ cong (λ σ' → π₁ (σ' ∘ τ)) ηπ ⟩
    π₁ ((π₁ σ ‣ π₂ σ) ∘ τ)
  ≡⟨ cong π₁ ‣∘ ⟩
    π₁ ((π₁ σ ∘ τ) ‣ tr (Tm Θ) (sym ([∘] A (π₁ σ) τ)) (π₂ σ [ τ ]tm))
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
-- π₂∘ : (σ : Sub Δ (Γ ‣ A))(τ : Sub Θ Δ) → tr (Tm Θ) (trans (cong (A [_]ty) (π₁∘ σ τ)) ([∘] A (π₁ σ) τ)) (π₂ (σ ∘ τ)) ≡ π₂ σ [ τ ]tm
-- π₂∘ {Δ} {Γ} {A} {Θ} σ τ =
--     tr (Tm Θ) (trans (cong (_[_]ty A) (π₁∘ σ τ)) ([∘] A (π₁ σ) τ)) (π₂ (σ ∘ τ))
--   ≡⟨ {!    !} ⟩
--     {!   !}
--   --   π₂ (σ ∘ τ)
--   -- ≡⟨ cong (λ σ' → π₂ (σ' ∘ τ)) ηπ ⟩
--   --   π₂ ((π₁ σ ‣ π₂ σ) ∘ τ)
--   -- ≡⟨ cong π₂ ‣∘ ⟩
--   --   π₂ ((π₁ σ ∘ τ) ‣ π₂ σ [ τ ]tm)
--   -- ≡⟨ βπ₂ {σ = π₁ σ ∘ τ} ⟩
--   --   π₂ σ [ τ ]tm
--   -- ∎

-- syntax abbreviations
wk : Sub (Δ ‣ A) Δ
wk = π₁ idS

vz : Tm (Γ ‣ A) (A [ wk ]ty)
vz = π₂ idS

vs : Tm Γ A → Tm (Γ ‣ B) (A [ wk ]ty)
vs x = x [ wk ]tm
-- vs (vs ... (vs vz) ...) = π₂ idS [ π₁ idS ]tm .... [ π₁ idS ]tm
 
vz:= : Tm Γ A → Sub Γ (Γ ‣ A)
vz:= {Γ} {A} t = idS ‣ tr (Tm Γ) (sym ([idS] A)) t -- additional "tr" 