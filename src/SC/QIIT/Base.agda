-- Formalizing Substitution Calculus as QIIT
module SC.QIIT.Base where

open import Prelude
open ≡-Reasoning

infixl 20 _[_] -- _[_]tm
infixr 10 _∘_
infixl 4 _,_

interleaved mutual
  data Ctx : Set
  data Ty  : Ctx → Set
  data Sub : Ctx → Ctx → Set
  data Tm  : (Γ : Ctx) → Ty Γ → Set

  variable
      Γ Γ' Δ Δ' Θ Θ' : Ctx
      A A' B B'      : Ty Γ
      t s            : Tm Γ A
      σ τ δ          : Sub Δ Γ

  data _ where
    ∅
      ------
      : Ctx
    _,_
      : (Γ : Ctx)(A : Ty Γ)
      ---------------------
      → Ctx
    U
      ------
      : Ty Γ
    _[_]
      : (A : Ty Δ)(σ : Sub Γ Δ)
      -------------------------
      → Ty Γ
    ∅
      ---------
      : Sub Γ ∅
    _,_
      : (σ : Sub Γ Δ) (t : Tm Γ (A [ σ ]))
      --------------------------------------
      → Sub Γ (Δ , A)
    idS
      ---------
      : Sub Γ Γ
    _∘_
      : (σ : Sub Δ Θ) (δ : Sub Γ Δ)
      -----------------------------
      → Sub Γ Θ
    π₁
      : (σ : Sub Γ (Δ , A))
      ---------------------
      → Sub Γ Δ
    π₂
      : (σ : Sub Γ (Δ , A))
      ---------------------
      → Tm Γ (A [ π₁ σ ])

    _[_]
      : (t : Tm Δ A)(σ : Sub Γ Δ)
      ---------------------------
      → Tm Γ (A [ σ ])

  -- congruence rules of signatures
  congTy : Γ ≡ Γ' → Ty Γ ≡ Ty Γ'
  congTy = cong Ty

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
  cong,Ctx : (Γ≡Γ' : Γ ≡ Γ'){A : Ty Γ}{A' : Ty Γ'}
          → (A≡A' : conv (congTy Γ≡Γ') A ≡ A')
          → (Γ , A) ≡ (Γ' , A')
  cong,Ctx refl refl = refl

  cong[] : (Γ≡Γ' : Γ ≡ Γ'){A : Ty Γ}{A' : Ty Γ'}
        → conv (congTy Γ≡Γ') A ≡ A'
        → (Δ≡Δ' : Δ ≡ Δ'){σ : Sub Δ Γ}{σ' : Sub Δ' Γ'}
        → conv (congSub Δ≡Δ' Γ≡Γ') σ ≡ σ'
        → conv (congTy Δ≡Δ') (A [ σ ]) ≡ A' [ σ' ]
  cong[] refl refl refl refl = refl

  congA[] : {A : Ty Γ}{σ σ' : Sub Δ Γ} → σ ≡ σ' → A [ σ ] ≡ A [ σ' ]
  congA[] = cong[] refl refl refl

  cong,Sub
    : (Δ≡Δ' : Δ ≡ Δ')(Γ≡Γ' : Γ ≡ Γ'){σ : Sub Δ Γ}{σ' : Sub Δ' Γ'}
    → {A : Ty Γ}{A' : Ty Γ'}{t : Tm Δ (A [ σ ])}{t' : Tm Δ' (A' [ σ' ])}
    → (A≡A' : conv (congTy Γ≡Γ') A ≡ A')
      (σ≡σ' : conv (congSub Δ≡Δ' Γ≡Γ') σ ≡ σ')
      (t≡t' : conv (congTm Δ≡Δ' (cong[] Γ≡Γ' A≡A' Δ≡Δ' σ≡σ')) t ≡ t')
    → conv (congSub Δ≡Δ' (cong,Ctx Γ≡Γ' A≡A')) (σ , t) ≡ (σ' , t')
  cong,Sub refl refl refl refl refl = refl

  cong,Sub' : {σ σ' : Sub Δ Γ}{A A' : Ty Γ}{t : Tm Δ (A [ σ ])}{t' : Tm Δ (A' [ σ' ])}
            → (A≡A' : A ≡ A')(σ≡σ' : σ ≡ σ') → conv (congTmΓ (cong[] refl A≡A' refl σ≡σ')) t ≡ t'
            → conv (congSub refl (cong,Ctx refl A≡A')) (_,_ {A = A} σ t) ≡ _,_ {A = A'} σ' t'
  cong,Sub' refl refl refl = refl

  cong∘ : (Γ≡Γ' : Γ ≡ Γ')(Δ≡Δ' : Δ ≡ Δ')(Θ≡Θ' : Θ ≡ Θ')
          {σ : Sub Δ Γ}{σ' : Sub Δ' Γ'}{τ : Sub Θ Δ}{τ' : Sub Θ' Δ'}
          (σ≡σ' : conv (congSub Δ≡Δ' Γ≡Γ') σ ≡ σ')(τ≡τ' : conv (congSub Θ≡Θ' Δ≡Δ') τ ≡ τ')
        → conv (congSub Θ≡Θ' Γ≡Γ') (σ ∘ τ) ≡ σ' ∘ τ'
  cong∘ refl refl refl refl refl = refl

  cong∘' : {σ σ' : Sub Δ Γ}{τ τ' : Sub Θ Δ}
         → σ ≡ σ' → τ ≡ τ'
         → σ ∘ τ ≡ σ' ∘ τ'
  cong∘' refl refl = refl

  congπ₁ : (Δ≡Δ' : Δ ≡ Δ')(Γ≡Γ' : Γ ≡ Γ'){A : Ty Γ}{A' : Ty Γ'}
          {σ : Sub Δ (Γ , A)}{σ' : Sub Δ' (Γ' , A')}
        → (A≡A' : conv (congTy Γ≡Γ') A ≡ A')
        → conv (congSub Δ≡Δ' (cong,Ctx Γ≡Γ' A≡A')) σ ≡ σ'
        → conv (congSub Δ≡Δ' Γ≡Γ') (π₁ σ) ≡ π₁ σ'
  congπ₁ refl refl refl refl = refl

  congπ₂ : (Δ≡Δ' : Δ ≡ Δ')(Γ≡Γ' : Γ ≡ Γ'){A : Ty Γ}{A' : Ty Γ'}
          {σ : Sub Δ (Γ , A)}{σ' : Sub Δ' (Γ' , A')}
        → (A≡A' : conv (congTy Γ≡Γ') A ≡ A')
          (σ≡σ' : conv (congSub Δ≡Δ' (cong,Ctx Γ≡Γ' A≡A')) σ ≡ σ')
        → conv (congTm Δ≡Δ' (cong[] Γ≡Γ' A≡A' Δ≡Δ' (congπ₁ Δ≡Δ' Γ≡Γ' A≡A' σ≡σ'))) (π₂ σ) ≡ π₂ σ'
  congπ₂ refl refl refl refl = refl

  cong[]tm : (Γ≡Γ' : Γ ≡ Γ'){A : Ty Γ}{A' : Ty Γ'}(A≡A' : conv (congTy Γ≡Γ') A ≡ A')
            {t : Tm Γ A}{t' : Tm Γ' A'}(t≡t' : conv (congTm Γ≡Γ' A≡A') t ≡ t')
            (Δ≡Δ' : Δ ≡ Δ'){σ : Sub Δ Γ}{σ' : Sub Δ' Γ'}
            (σ≡σ' : conv (congSub Δ≡Δ' Γ≡Γ') σ ≡ σ')
          → conv (congTm Δ≡Δ' (cong[] Γ≡Γ' A≡A' Δ≡Δ' σ≡σ')) (t [ σ ]) ≡ t' [ σ' ]
  cong[]tm refl refl refl refl refl = refl

  -- equalities of substitutions
  postulate
    -- equalities on types
    U[]
      : (σ : Sub Γ Δ)
      → U [ σ ] ≡ U
    [idS]
      : (A : Ty Γ)
      → A [ idS ] ≡ A
    [∘]
      : (A : Ty Θ)(τ : Sub Δ Θ)(σ : Sub Γ Δ)
      → A [ τ ∘ σ ] ≡ A [ τ ] [ σ ]

    -- equality on substitutions
    idS∘_ 
      : (σ : Sub Γ Δ)
      → idS ∘ σ ≡ σ
    _∘idS
      : (σ : Sub Γ Δ)
      → σ ∘ idS ≡ σ
    assocS
      : (δ ∘ τ) ∘ σ ≡ δ ∘ (τ ∘ σ)
    ,∘
      : (σ , t) ∘ τ ≡ ((σ ∘ τ) , tr (Tm Γ) (sym $ [∘] A σ τ) (t [ τ ]))
      -- conv (congTmΓ (sym ([∘] A σ τ))) (t [ τ ]))
    βπ₁
      : π₁ (σ , t) ≡ σ
    ηπ
      : σ ≡ (π₁ σ , π₂ σ)
    η∅
      : σ ≡ ∅

    -- equality on terms
    [idS]tm
      : (t : Tm Γ A)
      → conv (congTmΓ ([idS] A)) (t [ idS ]) ≡ t
    [∘]tm
      : (t : Tm Γ A)(σ : Sub Δ Γ)(τ : Sub Θ Δ)
      → conv (congTmΓ ([∘] A σ τ)) (t [ σ ∘ τ ]) ≡ t [ σ ] [ τ ]
    βπ₂
      : tr (λ σ → Tm Γ (A [ σ ])) βπ₁ (π₂ (σ , t)) ≡ t

-- derived computation rules on composition

βπ : (σ : Sub Γ Δ) (t : Tm Γ (A [ σ ]))
  → _≡_ {_} {Σ _ (λ σ → Tm Γ (A [ σ ]))}
    (π₁ (σ , t) , π₂ (σ , t))
    (σ , t)
βπ σ t = Σ-≡,≡→≡ (βπ₁ , βπ₂)

π₁∘ : (σ : Sub Δ (Γ , A))(τ : Sub Θ Δ) → π₁ (σ ∘ τ) ≡ π₁ σ ∘ τ
π₁∘ {Δ} {Γ} {A} {Θ} σ τ =
  begin
    π₁ (σ ∘ τ)
  ≡⟨ cong (λ σ' → π₁ (σ' ∘ τ)) ηπ ⟩
    π₁ ((π₁ σ , π₂ σ) ∘ τ)
  ≡⟨ cong π₁ ,∘ ⟩
    π₁ ((π₁ σ ∘ τ) , tr (Tm Θ) (sym $ [∘] _ _ _) (π₂ σ [ τ ]))
  ≡⟨ βπ₁ {σ = π₁ σ ∘ τ} ⟩
    π₁ σ ∘ τ
  ∎

π₁idS∘ : {A : Ty Γ}(σ : Sub Δ (Γ , A)) → π₁ idS ∘ σ ≡ π₁ σ
π₁idS∘ σ =
  begin
    π₁ idS ∘ σ
  ≡⟨ sym (π₁∘ idS σ) ⟩
    π₁ (idS ∘ σ)
  ≡⟨ cong π₁ (idS∘ σ) ⟩
    π₁ σ
  ∎

π₂∘ : (σ : Sub Γ Δ) {A : Ty Θ} (τ : Sub Δ (Θ , A))
  → _≡_ {_} {∃ (Tm Γ)} (A [ π₁ (τ ∘ σ) ] , π₂ (τ ∘ σ)) (A [ π₁ τ ] [ σ ] , π₂ τ [ σ ])
π₂∘ {Γ} {Δ} {Θ} σ {A} τ = begin

  A [ π₁ (τ ∘ σ) ] , π₂ (τ ∘ σ) 

    ≡⟨ apΣ (Tm Γ) (λ τ → A [ π₁ (τ ∘ σ) ]) (apdΣ (λ τ → π₂ (τ ∘ σ)) ηπ) ⟩

  A [ π₁ ((π₁ τ , π₂ τ) ∘ σ) ] , π₂ ((π₁ τ , π₂ τ) ∘ σ)

    ≡⟨ apΣ (Tm Γ) (λ τ → A [ π₁ τ ]) (apdΣ π₂ ,∘) ⟩

  let t = tr (Tm Γ) (sym $ [∘] _ _ _) (π₂ τ [ σ ]) in
  A [ π₁ (π₁ τ ∘ σ , t) ] , π₂ (π₁ τ ∘ σ , t)

    ≡⟨ apΣ (Tm Γ) (A [_]) (βπ (π₁ τ ∘ σ) t) ⟩

  A [ π₁ τ ∘ σ ] , tr (Tm Γ) (sym $ [∘] _ _ _) (π₂ τ [ σ ])

    ≡⟨ sym $ lift (Tm Γ) (π₂ τ [ σ ]) (sym $ [∘] _ _ _) ⟩

  A [ π₁ τ ] [ σ ] , π₂ τ [ σ ]
  
    ∎

-- syntax abbreviations
wk : Sub (Δ , A) Δ
wk = π₁ idS

vz : Tm (Γ , A) (A [ wk ])
vz = π₂ idS

vs : Tm Γ A → Tm (Γ , B) (A [ wk ])
vs x = x [ wk ]
-- vs (vs ... (vs vz) ...) = π₂ idS [ π₁ idS ]tm .... [ π₁ idS ]tm
 
vz:= : Tm Γ A → Sub Γ (Γ , A)
vz:= {Γ} {A} t = idS , tr (Tm Γ) (sym ([idS] A)) t -- additional "tr" 
