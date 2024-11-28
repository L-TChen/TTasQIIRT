-- {-# OPTIONS --cubical #-}
-- {-# OPTIONS --exact-split --rewriting -vtc.cover.splittree:10 #-}
-- Formalizing Substitution Calculus as QIIRT
module SC.QIIT.Base where

open import Prelude
open ≡-Reasoning

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

-- congruence rules of signatures
congTy : Γ ≡ Γ' → Ty Γ ≡ Ty Γ'
congTy refl = refl

congSub : Γ ≡ Γ' → Δ ≡ Δ' → Sub Γ Δ ≡ Sub Γ' Δ'
congSub refl refl = refl

congTm : (Γ≡Γ' : Γ ≡ Γ'){A : Ty Γ}{A' : Ty Γ'}
       → conv (congTy Γ≡Γ') A ≡ A' → Tm Γ A ≡ Tm Γ' A'
congTm refl refl = refl

congTmΓ : {A A' : Ty Γ} → A ≡ A' → Tm Γ A ≡ Tm Γ A'
congTmΓ = congTm refl

trans-congTmΓ : {A B C : Ty Γ}{p : A ≡ B}{q : B ≡ C} → trans (congTmΓ p) (congTmΓ q) ≡ congTmΓ (trans p q)
trans-congTmΓ {p = refl} = refl

-- congruence rules of constructors
cong‣Ctx : (Γ≡Γ' : Γ ≡ Γ'){A : Ty Γ}{A' : Ty Γ'}
         → (A≡A' : conv (congTy Γ≡Γ') A ≡ A')
         → Γ ‣ A ≡ Γ' ‣ A'
cong‣Ctx refl refl = refl

cong[] : (Γ≡Γ' : Γ ≡ Γ'){A : Ty Γ}{A' : Ty Γ'}
       → conv (congTy Γ≡Γ') A ≡ A'
       → (Δ≡Δ' : Δ ≡ Δ'){σ : Sub Δ Γ}{σ' : Sub Δ' Γ'}
       → conv (congSub Δ≡Δ' Γ≡Γ') σ ≡ σ'
       → conv (congTy Δ≡Δ') (A [ σ ]ty) ≡ A' [ σ' ]ty
cong[] refl refl refl refl = refl

cong‣Sub
  : (Δ≡Δ' : Δ ≡ Δ')(Γ≡Γ' : Γ ≡ Γ'){σ : Sub Δ Γ}{σ' : Sub Δ' Γ'}
  → {A : Ty Γ}{A' : Ty Γ'}{t : Tm Δ (A [ σ ]ty)}{t' : Tm Δ' (A' [ σ' ]ty)}
  → (A≡A' : conv (congTy Γ≡Γ') A ≡ A')
    (σ≡σ' : conv (congSub Δ≡Δ' Γ≡Γ') σ ≡ σ')
    (t≡t' : conv (congTm Δ≡Δ' (cong[] Γ≡Γ' A≡A' Δ≡Δ' σ≡σ')) t ≡ t')
  → conv (congSub Δ≡Δ' (cong‣Ctx Γ≡Γ' A≡A')) (σ ‣ t) ≡ σ' ‣ t'
cong‣Sub refl refl refl refl refl = refl

cong∘ : (Γ≡Γ' : Γ ≡ Γ')(Δ≡Δ' : Δ ≡ Δ')(Θ≡Θ' : Θ ≡ Θ')
        {σ : Sub Δ Γ}{σ' : Sub Δ' Γ'}{τ : Sub Θ Δ}{τ' : Sub Θ' Δ'}
        (σ≡σ' : conv (congSub Δ≡Δ' Γ≡Γ') σ ≡ σ')(τ≡τ' : conv (congSub Θ≡Θ' Δ≡Δ') τ ≡ τ')
      → conv (congSub Θ≡Θ' Γ≡Γ') (σ ∘ τ) ≡ σ' ∘ τ'
cong∘ refl refl refl refl refl = refl

congπ₁ : (Δ≡Δ' : Δ ≡ Δ')(Γ≡Γ' : Γ ≡ Γ'){A : Ty Γ}{A' : Ty Γ'}
         {σ : Sub Δ (Γ ‣ A)}{σ' : Sub Δ' (Γ' ‣ A')}
       → (A≡A' : conv (congTy Γ≡Γ') A ≡ A')
       → conv (congSub Δ≡Δ' (cong‣Ctx Γ≡Γ' A≡A')) σ ≡ σ'
       → conv (congSub Δ≡Δ' Γ≡Γ') (π₁ σ) ≡ π₁ σ'
congπ₁ refl refl refl refl = refl

congπ₂ : (Δ≡Δ' : Δ ≡ Δ')(Γ≡Γ' : Γ ≡ Γ'){A : Ty Γ}{A' : Ty Γ'}
         {σ : Sub Δ (Γ ‣ A)}{σ' : Sub Δ' (Γ' ‣ A')}
       → (A≡A' : conv (congTy Γ≡Γ') A ≡ A')
         (σ≡σ' : conv (congSub Δ≡Δ' (cong‣Ctx Γ≡Γ' A≡A')) σ ≡ σ')
       → conv (congTm Δ≡Δ' (cong[] Γ≡Γ' A≡A' Δ≡Δ' (congπ₁ Δ≡Δ' Γ≡Γ' A≡A' σ≡σ'))) (π₂ σ) ≡ π₂ σ'
congπ₂ refl refl refl refl = refl

cong[]tm : (Γ≡Γ' : Γ ≡ Γ'){A : Ty Γ}{A' : Ty Γ'}(A≡A' : conv (congTy Γ≡Γ') A ≡ A')
           {t : Tm Γ A}{t' : Tm Γ' A'}(t≡t' : conv (congTm Γ≡Γ' A≡A') t ≡ t')
           (Δ≡Δ' : Δ ≡ Δ'){σ : Sub Δ Γ}{σ' : Sub Δ' Γ'}
           (σ≡σ' : conv (congSub Δ≡Δ' Γ≡Γ') σ ≡ σ')
         → conv (congTm Δ≡Δ' (cong[] Γ≡Γ' A≡A' Δ≡Δ' σ≡σ')) (t [ σ ]tm) ≡ t' [ σ' ]tm
cong[]tm refl refl refl refl refl = refl

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
    → (_‣_ {A = A} σ t) ∘ τ ≡ (σ ∘ τ) ‣ conv (congTmΓ (sym ([∘] A σ τ))) (t [ τ ]tm)
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
    → conv (congTmΓ ([idS] A)) (t [ idS ]tm) ≡ t
  [∘]tm
    : (t : Tm Γ A)(σ : Sub Δ Γ)(τ : Sub Θ Δ)
    → conv (congTmΓ ([∘] A σ τ)) (t [ σ ∘ τ ]tm) ≡ t [ σ ]tm [ τ ]tm
  βπ₂
    : {σ : Sub Δ Γ}{t : Tm Δ (A [ σ ]ty)}
    → conv (congTmΓ (cong[] refl refl refl βπ₁)) (π₂ (_‣_ {A = A} σ t)) ≡ t

-- derived computation rules on composition
π₁∘ : (σ : Sub Δ (Γ ‣ A))(τ : Sub Θ Δ) → π₁ (σ ∘ τ) ≡ π₁ σ ∘ τ
π₁∘ {A = A} {Θ} σ τ =
  begin
    π₁ (σ ∘ τ)
  ≡⟨ cong (λ σ' → π₁ (σ' ∘ τ)) ηπ ⟩
    π₁ ((π₁ σ ‣ π₂ σ) ∘ τ)
  ≡⟨ cong π₁ ‣∘ ⟩
    π₁ ((π₁ σ ∘ τ) ‣ conv (congTmΓ (sym ([∘] A (π₁ σ) τ))) (π₂ σ [ τ ]tm))
  ≡⟨ βπ₁ {σ = π₁ σ ∘ τ} ⟩
    π₁ σ ∘ τ
  ∎

π₁idS∘ : {A : Ty Γ}(σ : Sub Δ (Γ ‣ A)) → π₁ idS ∘ σ ≡ π₁ σ
π₁idS∘ σ =
  begin
    π₁ idS ∘ σ
  ≡⟨ sym (π₁∘ idS σ) ⟩
    π₁ (idS ∘ σ)
  ≡⟨ cong π₁ (idS∘ σ) ⟩
    π₁ σ
  ∎

π₂∘ : (σ : Sub Δ (Γ ‣ A))(τ : Sub Θ Δ) → conv (congTmΓ (trans (cong[] refl refl refl (π₁∘ σ τ)) ([∘] A (π₁ σ) τ))) (π₂ (σ ∘ τ))
                                         ≡ π₂ σ [ τ ]tm 
π₂∘ {Δ} {Γ} {A} {Θ} σ τ =
  begin
    conv (congTmΓ (trans (cong[] refl refl refl (π₁∘ σ τ)) ([∘] A (π₁ σ) τ))) (π₂ (σ ∘ τ))
  ≡⟨
    conv-unique (congTmΓ (trans (cong[] refl refl refl (π₁∘ σ τ)) ([∘] A (π₁ σ) τ)))
                (trans (trans (trans p1 p2) p3) p4)
                (π₂ (σ ∘ τ))
  ⟩
    conv (trans (trans (trans p1 p2) p3) p4) (π₂ (σ ∘ τ))
  ≡⟨ 
    ((eq1 ⟫ p1                     , p2 ⟫ eq2)
          ⟫ trans p1 p2            , p3 ⟫ eq3)
          ⟫ trans (trans p1 p2) p3 , p4 ⟫ eq4
  ⟩
    π₂ σ [ τ ]tm
  ∎

  
  where
    p1 : Tm Θ (A [ π₁ (σ ∘ τ) ]ty) ≡ Tm Θ (A [ π₁ ((π₁ σ ‣ π₂ σ) ∘ τ) ]ty)
    p1 = congTmΓ (cong[] refl refl refl (congπ₁ refl refl refl (cong∘ refl refl refl ηπ refl)))

    p2 : Tm Θ (A [ π₁ ((π₁ σ ‣ π₂ σ) ∘ τ) ]ty) ≡ Tm Θ (A [ π₁ ((π₁ σ ∘ τ) ‣ conv (congTmΓ (sym ([∘] A (π₁ σ) τ))) (π₂ σ [ τ ]tm)) ]ty)
    p2 = congTmΓ (cong[] refl refl refl (congπ₁ refl refl refl ‣∘))
    
    p3 : Tm Θ (A [ π₁ ((π₁ σ ∘ τ) ‣ conv (congTmΓ (sym ([∘] A (π₁ σ) τ))) (π₂ σ [ τ ]tm)) ]ty)
         ≡ Tm Θ (A [ π₁ σ ∘ τ ]ty)
    p3 = congTmΓ (cong[] refl refl refl βπ₁)

    p4 : Tm Θ (A [ π₁ σ ∘ τ ]ty) ≡ Tm Θ (A [ π₁ σ ]ty [ τ ]ty)
    p4 = congTmΓ ([∘] A (π₁ σ) τ)
    
    eq1 : conv (congTmΓ (cong[] refl refl refl (congπ₁ refl refl refl (cong∘ refl refl refl ηπ refl)))) (π₂ (σ ∘ τ)) ≡ π₂ ((π₁ σ ‣ π₂ σ) ∘ τ)
    eq1 = congπ₂ refl refl {σ = σ ∘ τ} refl (cong∘ refl refl refl {σ = σ} {τ = τ} ηπ refl)

    eq2 : conv (congTmΓ (cong[] refl refl refl (congπ₁ refl refl refl ‣∘))) (π₂ ((π₁ σ ‣ π₂ σ) ∘ τ)) ≡ π₂ ((π₁ σ ∘ τ) ‣ conv (congTmΓ (sym ([∘] A (π₁ σ) τ))) (π₂ σ [ τ ]tm))
    eq2 = congπ₂ refl refl refl ‣∘

    eq3 : conv (congTm refl (cong[] refl refl refl βπ₁)) (π₂ ((π₁ σ ∘ τ) ‣ conv (congTmΓ (sym ([∘] A (π₁ σ) τ))) (π₂ σ [ τ ]tm)))
           ≡ conv (congTmΓ (sym ([∘] A (π₁ σ) τ))) (π₂ σ [ τ ]tm)
    eq3 = βπ₂

    eq4 : conv (congTmΓ ([∘] A (π₁ σ) τ)) (conv (congTmΓ (sym ([∘] A (π₁ σ) τ))) (π₂ σ [ τ ]tm)) ≡ π₂ σ [ τ ]tm
    eq4 = begin
        conv (congTmΓ ([∘] A (π₁ σ) τ)) (conv (congTmΓ (sym ([∘] A (π₁ σ) τ))) (π₂ σ [ τ ]tm))
      ≡⟨ conv² (congTmΓ (sym ([∘] A (π₁ σ) τ))) (congTmΓ ([∘] A (π₁ σ) τ)) ⟩
        conv (trans (congTmΓ (sym ([∘] A (π₁ σ) τ))) (congTmΓ ([∘] A (π₁ σ) τ))) (π₂ σ [ τ ]tm)
      ≡⟨ cong (λ eq → conv eq (π₂ σ [ τ ]tm)) (trans-congTmΓ {p = sym ([∘] A (π₁ σ) τ)} {[∘] A (π₁ σ) τ}) ⟩
        conv (congTmΓ (trans (sym ([∘] A (π₁ σ) τ)) ([∘] A (π₁ σ) τ))) (π₂ σ [ τ ]tm)
      ≡⟨ cong (λ eq → conv (congTmΓ eq) (π₂ σ [ τ ]tm)) (trans-symˡ ([∘] A (π₁ σ) τ)) ⟩
        π₂ σ [ τ ]tm
      ∎

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
