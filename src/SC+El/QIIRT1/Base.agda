{-# OPTIONS --local-confluence-check #-}

module SC+El.QIIRT1.Base where

open import Prelude
open ≡-Reasoning

-- inductive-inductive-recursive definition of context, type, term, and type substitution

infixl 35 _[_] _[_]tm
infix  10 _‣_

data Ctx : Set
data Ty  : Ctx → Set
data Sub : Ctx → Ctx → Set
data Tm  : (Γ : Ctx) → Ty Γ → Set

postulate
  _[_]  : ∀{Δ Γ} → Ty Γ → Sub Δ Γ → Ty Δ
 
variable
    Γ Γ' Δ Δ' Θ Θ' Φ : Ctx
    A A' B B'        : Ty Γ
    t s              : Tm Γ A
    σ τ γ υ          : Sub Δ Γ

data Ctx where
  ∅
    : Ctx
  _‣_
    : (Γ : Ctx) (A : Ty Γ)
    → Ctx

data Ty where
  U
    : Ty Γ
  El
    : Tm Γ U → Ty Γ

data Sub where
  ∅
    ---------
    : Sub Δ ∅
  _‣_
    : (σ : Sub Γ Δ) (t : Tm Γ (A [ σ ]))
    ------------------------------------
    → Sub Γ (Δ ‣ A)
  idS
    : Sub Γ Γ
  _∘_
    : {Γ Δ Θ : Ctx}
    → (τ : Sub Δ Θ) (σ : Sub Γ Δ)
    → Sub Γ Θ
  π₁
   : (σ : Sub Γ (Δ ‣ A))
   → Sub Γ Δ

postulate
  idS∘_ 
    : (σ : Sub Γ Δ)
    → idS ∘ σ ≡ σ
  _∘idS
    : (σ : Sub Γ Δ)
    → σ ∘ idS ≡ σ
  assocS
    : (υ ∘ τ) ∘ σ ≡ υ ∘ (τ ∘ σ)
  βπ₁
    : {σ : Sub Γ Δ} {t : Tm Γ (A [ σ ])}
    → π₁ (σ ‣ t) ≡ σ
  η∅
    : {σ : Sub Γ ∅}
    → σ ≡ ∅

{-# REWRITE βπ₁ #-}
    
data Tm where
  π₂
    : (σ : Sub Γ (Δ ‣ A))
    → Tm Γ (A [ π₁ σ ])
  _[_]tm
    : Tm Δ A → (σ : Sub Γ Δ)
    → Tm Γ (A [ σ ])

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
       → conv (congTy Δ≡Δ') (A [ σ ]) ≡ A' [ σ' ]
cong[] refl refl refl refl = refl

cong‣Sub
  : (Δ≡Δ' : Δ ≡ Δ')(Γ≡Γ' : Γ ≡ Γ'){σ : Sub Δ Γ}{σ' : Sub Δ' Γ'}
  → {A : Ty Γ}{A' : Ty Γ'}{t : Tm Δ (A [ σ ])}{t' : Tm Δ' (A' [ σ' ])}
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
 
{-
  We'd like to define a resursion by overlapping patterns
  
  A [ idS        ] = A
  A [ σ ∘ τ      ] = A [ σ ] [ τ ]
  A [ π₁ (σ ‣ t) ] = A [ σ ]
  U      [ σ ]     = U
  (El t) [ σ ]     = El (t [ σ ]tm) 

-}
postulate
  [idS] : A      [ idS        ] ≡ A
  [∘]   : A      [ σ ∘ τ      ] ≡ A [ σ ] [ τ ]

{-# REWRITE [idS] [∘] #-}

postulate
  [idS]tm
    : (t : Tm Γ A)
    → t [ idS ]tm ≡ t
  [∘]tm
    : (t : Tm Γ A)(σ : Sub Δ Γ)(τ : Sub Θ Δ)
    → t [ σ ∘ τ ]tm ≡ t [ σ ]tm [ τ ]tm
  βπ₂
    : {σ : Sub Δ Γ}{t : Tm Δ (A [ σ ])}
    →  π₂ (σ ‣ t) ≡ t

{-# REWRITE [idS]tm [∘]tm #-}

postulate
  U[]   : U [ σ ] ≡ U

{-# REWRITE U[] #-}

postulate
  El[]  : (El t) [ σ ] ≡ El (t [ σ ]tm)

{-# REWRITE El[] #-}

postulate
  ‣∘
    : {A : Ty Γ}{σ : Sub Δ Γ}{t : Tm Δ (A [ σ ])}{τ : Sub Θ Δ}
    → (_‣_ {A = A} σ t) ∘ τ ≡ (σ ∘ τ) ‣ t [ τ ]tm
  ηπ
    : {σ : Sub Δ (Γ ‣ A)}
    → σ ≡ π₁ σ ‣ π₂ σ

-- We will need to prove coherence for the following with another rewriting relation:
-- coherence of postulates

coh[idS∘] : A [ idS ∘ σ ] ≡ A [ σ ]
coh[idS∘] {A = U}    = refl
coh[idS∘] {A = El t} = refl

coh[∘idS] : A [ σ ∘ idS ] ≡ A [ σ ]
coh[∘idS] {A = U}    = refl
coh[∘idS] {A = El t} = refl

coh[assocS] : A [ (σ ∘ τ) ∘ γ ] ≡ A [ σ ∘ (τ ∘ γ) ]
coh[assocS] {A = U}    = refl
coh[assocS] {A = El t} = refl

coh[βπ₁] : A [ π₁ (σ ‣ t) ] ≡ A [ σ ]
coh[βπ₁] {A = U}    = refl
coh[βπ₁] {A = El t} = refl

coh[η∅] : A [ σ ] ≡ A [ ∅ ]
coh[η∅] {A = U}    = refl
coh[η∅] {A = El t} {σ = σ} = cong El (cong (t [_]tm) (η∅ {σ = σ}))

-- derived computation rules on composition
π₁∘ : (σ : Sub Δ (Γ ‣ A))(τ : Sub Θ Δ) → π₁ (σ ∘ τ) ≡ π₁ σ ∘ τ
π₁∘ σ τ =
    π₁ (σ ∘ τ)
  ≡⟨ cong (λ σ' → π₁ (σ' ∘ τ)) ηπ ⟩
    π₁ ((π₁ σ ‣ π₂ σ) ∘ τ)
  ≡⟨ cong π₁ ‣∘ ⟩
    π₁ σ ∘ τ
  ∎

π₂∘ : (σ : Sub Δ (Γ ‣ A))(τ : Sub Θ Δ)
  → conv (congTmΓ (cong[] refl {A} refl refl (π₁∘ σ τ))) (π₂ (σ ∘ τ))
    ≡ π₂ σ [ τ ]tm
π₂∘ {Δ} {Γ} {A} {Θ} σ τ = 
  begin
    conv (congTmΓ (cong[] refl refl refl (π₁∘ σ τ))) (π₂ (σ ∘ τ))
  ≡⟨ conv-unique (congTmΓ (cong[] refl refl refl (π₁∘ σ τ))) (trans p1 p2) (π₂ (σ ∘ τ)) ⟩
    conv (trans p1 p2) (π₂ (σ ∘ τ))
  ≡⟨ eq1 ⟫ p1 , p2 ⟫ eq2 ⟩
    π₂ σ [ τ ]tm
  ∎
  where
    p1 : Tm Θ (A [ π₁ (σ ∘ τ) ]) ≡ Tm Θ (A [ π₁ {A = A} ((π₁ σ ‣ π₂ σ) ∘ τ) ])
    p1 = congTmΓ (cong[] refl {A} refl refl (congπ₁ refl refl refl (cong∘ refl refl refl ηπ refl)))

    p2 : Tm Θ (A [ π₁ {A = A} ((π₁ σ ‣ π₂ σ) ∘ τ) ]) ≡ Tm Θ (A [ π₁ σ ] [ τ ])
    p2 = congTmΓ (cong[] refl {A} refl refl (congπ₁ refl refl refl ‣∘))
    
    eq1 : conv (congTmΓ (cong[] refl {A} refl refl (congπ₁ refl refl refl (cong∘ refl refl refl ηπ refl)))) (π₂ (σ ∘ τ)) ≡ π₂ {A = A} ((π₁ σ ‣ π₂ σ) ∘ τ)
    eq1 = congπ₂ refl refl {σ = σ ∘ τ} refl (cong∘ refl refl refl {σ = σ} {τ = τ} ηπ refl)

    eq2 : conv (congTmΓ (cong[] refl {A} refl refl (congπ₁ refl refl refl ‣∘))) (π₂ {A = A} ((π₁ σ ‣ π₂ σ) ∘ τ)) ≡ π₂ σ [ τ ]tm
    eq2 = begin
        conv (congTmΓ (cong[] refl {A} refl refl (congπ₁ refl refl refl ‣∘))) (π₂ {A = A} ((π₁ σ ‣ π₂ σ) ∘ τ))
      ≡⟨ congπ₂ refl refl refl ‣∘ ⟩
        π₂ ((π₁ σ ∘ τ) ‣ π₂ σ [ τ ]tm)
      ≡⟨ βπ₂ ⟩
        π₂ σ [ τ ]tm
      ∎

-- syntax abbreviations
wk : Sub (Δ ‣ A) Δ
wk = π₁ idS

vz : Tm (Γ ‣ A) (A [ wk ])
vz = π₂ idS

vs : Tm Γ A → Tm (Γ ‣ B) (A [ wk ])   
vs x = x [ wk ]tm
-- vs (vs ... (vs vz) ...) = π₂ idS [ π₁ idS ]tm .... [ π₁ idS ]tm

vz:= : Tm Γ A → Sub Γ (Γ ‣ A)
vz:= t = idS ‣ t
