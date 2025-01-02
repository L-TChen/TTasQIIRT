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
      → A [ τ ∘ σ ] ≡ A [ τ ] [ σ ] -- A [ τ ∘ σ ] ≡ A [ τ ] [ σ ]

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
      : (σ , t) ∘ τ ≡ ((σ ∘ τ) , conv (congTmΓ (sym ([∘] A σ τ))) (t [ τ ]))
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
      : conv (congTmΓ (cong[] refl refl refl βπ₁)) (π₂ (σ , t)) ≡ t

-- derived computation rules on composition
π₁∘ : (σ : Sub Δ (Γ , A))(τ : Sub Θ Δ) → π₁ (σ ∘ τ) ≡ π₁ σ ∘ τ
π₁∘ {A = A} {Θ} σ τ =
  begin
    π₁ (σ ∘ τ)
  ≡⟨ cong (λ σ' → π₁ (σ' ∘ τ)) ηπ ⟩
    π₁ ((π₁ σ , π₂ σ) ∘ τ)
  ≡⟨ cong π₁ ,∘ ⟩
    π₁ ((π₁ σ ∘ τ) , conv (congTmΓ (sym ([∘] A (π₁ σ) τ))) (π₂ σ [ τ ]))
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
π₂∘ {Γ} {Δ} σ {A} τ = begin
  A [ π₁ (τ ∘ σ) ] , π₂ (τ ∘ σ)
    ≡⟨ to-Σ≡ eq1L eq1R ⟩
  A [ π₁ ((π₁ τ , π₂ τ) ∘ σ) ] , π₂ ((π₁ τ , π₂ τ) ∘ σ)
    ≡⟨ to-Σ≡ eq2L eq2R ⟩
  A [ π₁ (π₁ τ ∘ σ , conv (congTmΓ (sym $ [∘] A _ _)) (π₂ τ [ σ ])) ] , π₂ (π₁ τ ∘ σ , conv (congTmΓ (sym $ [∘] A _ _)) (π₂ τ [ σ ]))
    ≡⟨ to-Σ≡ eq3L eq3R ⟩
  A [ π₁ τ ∘ σ ] , conv (congTmΓ (sym $ [∘] A _ _)) (π₂ τ [ σ ])
    ≡⟨ to-Σ≡ eq4L eq4R ⟩
  A [ π₁ τ ] [ σ ] , π₂ τ [ σ ]
    ∎
  where
    eq1L : A [ π₁ (τ ∘ σ) ] ≡ A [ π₁ ((π₁ τ , π₂ τ) ∘ σ) ]
    eq1L = cong (λ τ → A [ π₁ (τ ∘ σ) ]) ηπ

    eq1R : conv (cong (Tm Γ) eq1L) (π₂ (τ ∘ σ)) ≡ π₂ ((π₁ τ , π₂ τ) ∘ σ)
    eq1R = begin
      conv (cong (Tm Γ) eq1L) (π₂ (τ ∘ σ))
        ≡⟨ cong (conv (cong (Tm Γ) eq1L)) (sym (apd (λ τ → π₂ (τ ∘ σ)) (sym ηπ))) ⟩
      conv (cong (Tm Γ) eq1L) (tr (λ z → Tm Γ (A [ π₁ (z ∘ σ) ])) (sym ηπ) (π₂ ((π₁ τ , π₂ τ) ∘ σ)))
        ≡⟨ cong (conv (cong (Tm Γ) eq1L)) (tr-conv (sym ηπ)) ⟩
      conv (cong (Tm Γ) eq1L) (conv (cong (λ z → Tm Γ (A [ π₁ (z ∘ σ) ])) (sym ηπ)) (π₂ ((π₁ τ , π₂ τ) ∘ σ)))
        ≡⟨ conv² (cong (λ z → Tm Γ (A [ π₁ (z ∘ σ) ])) (sym ηπ)) (cong (Tm Γ) eq1L) ⟩
      conv _ (π₂ ((π₁ τ , π₂ τ) ∘ σ))
        ≡⟨ conv-unique _ refl _ ⟩
      π₂ ((π₁ τ , π₂ τ) ∘ σ)
        ∎
    
    eq2L : A [ π₁ ((π₁ τ , π₂ τ) ∘ σ) ] ≡ A [ π₁ (π₁ τ ∘ σ , conv (congTmΓ (sym $ [∘] A _ _)) (π₂ τ [ σ ])) ]
    eq2L = cong (λ σ → A [ π₁ σ ]) ,∘

    eq2R : conv (cong (Tm Γ) eq2L) (π₂ ((π₁ τ , π₂ τ) ∘ σ))
         ≡ π₂ (π₁ τ ∘ σ , conv (congTmΓ (sym $ [∘] A _ _)) (π₂ τ [ σ ]))
    eq2R = begin
      conv (cong (Tm Γ) eq2L) (π₂ ((π₁ τ , π₂ τ) ∘ σ))
        ≡⟨ cong (conv (cong (Tm Γ) eq2L)) (sym (apd π₂ (sym ,∘))) ⟩
      conv (cong (Tm Γ) eq2L) (tr (λ σ → Tm Γ (A [ π₁ σ ])) (sym ,∘) (π₂ (π₁ τ ∘ σ , conv (congTmΓ (sym $ [∘] A _ _)) (π₂ τ [ σ ]))))
        ≡⟨ cong (conv (cong (Tm Γ) eq2L)) (tr-conv (sym ,∘)) ⟩
      conv (cong (Tm Γ) eq2L)
           (conv (cong (λ σ → Tm Γ (A [ π₁ σ ])) (sym ,∘))
                 (π₂ (π₁ τ ∘ σ , conv (congTmΓ (sym $ [∘] A _ _)) (π₂ τ [ σ ]))))
        ≡⟨ conv² (cong (λ σ → Tm Γ (A [ π₁ σ ])) (sym ,∘)) (cong (Tm Γ) eq2L) ⟩
      conv _ (π₂ (π₁ τ ∘ σ , conv (congTmΓ (sym $ [∘] A _ _)) (π₂ τ [ σ ])))
        ≡⟨ conv-unique _ refl _ ⟩
      π₂ (π₁ τ ∘ σ , conv (congTmΓ (sym $ [∘] A _ _)) (π₂ τ [ σ ]))
        ∎
    
    eq3L : A [ π₁ (π₁ τ ∘ σ , conv (congTmΓ (sym $ [∘] A _ _)) (π₂ τ [ σ ])) ]
         ≡ A [ π₁ τ ∘ σ ]
    eq3L = cong (A [_]) βπ₁

    eq3R : conv (cong (Tm Γ) eq3L) (π₂ (π₁ τ ∘ σ , conv (congTmΓ (sym $ [∘] A _ _)) (π₂ τ [ σ ])))
         ≡ conv (congTmΓ (sym $ [∘] A _ _)) (π₂ τ [ σ ])
    eq3R = begin
      conv (cong (Tm Γ) eq3L) (π₂ (π₁ τ ∘ σ , conv (congTmΓ (sym $ [∘] A _ _)) (π₂ τ [ σ ])))
        ≡⟨ cong (conv (cong (Tm Γ) eq3L)) (conv-unique refl (trans (congTmΓ (congA[] βπ₁)) (sym (cong (Tm Γ) eq3L))) _) ⟩
      conv (cong (Tm Γ) eq3L)
           (conv (trans (congTmΓ (congA[] βπ₁)) (sym (cong (Tm Γ) eq3L)))
                 (π₂ (π₁ τ ∘ σ , conv (congTmΓ (sym $ [∘] A _ _)) (π₂ τ [ σ ]))))
        ≡⟨ cong (conv (cong (Tm Γ) eq3L)) (conv² (congTmΓ (congA[] βπ₁)) (sym (cong (Tm Γ) eq3L))) ⟨
      conv (cong (Tm Γ) eq3L)
           (conv (sym (cong (Tm Γ) eq3L))
                 (conv (congTmΓ (congA[] βπ₁))
                       ((π₂ (π₁ τ ∘ σ , conv (congTmΓ (sym $ [∘] A _ _)) (π₂ τ [ σ ])))))) 
        ≡⟨ conv² (sym (cong (Tm Γ) eq3L)) (cong (Tm Γ) eq3L) ⟩
      conv (trans (sym (cong (Tm Γ) eq3L)) (cong (Tm Γ) eq3L))
           (conv (congTmΓ (congA[] βπ₁)) (π₂ (π₁ τ ∘ σ , conv (congTmΓ (sym $ [∘] A _ _)) (π₂ τ [ σ ]))))
        ≡⟨ cong (conv (trans (sym (cong (Tm Γ) eq3L)) (cong (Tm Γ) eq3L))) βπ₂ ⟩
      conv (trans (sym (cong (Tm Γ) eq3L)) (cong (Tm Γ) eq3L)) (conv (congTmΓ (sym ([∘] A _ _))) (π₂ τ [ σ ]))
        ≡⟨ cong (λ p → conv p (conv (congTmΓ (sym ([∘] A _ _))) (π₂ τ [ σ ]))) (trans-symˡ (cong (Tm Γ) eq3L)) ⟩
      conv (congTmΓ (sym ([∘] A _ _))) (π₂ τ [ σ ])
        ∎

    eq4L : A [ π₁ τ ∘ σ ] ≡ A [ π₁ τ ] [ σ ]
    eq4L = [∘] A _ _

    eq4R : conv (cong (Tm Γ) eq4L) (conv (congTmΓ (sym $ [∘] A _ _)) (π₂ τ [ σ ])) ≡ π₂ τ [ σ ]
    eq4R = begin
      conv (cong (Tm Γ) eq4L) (conv (congTmΓ (sym $ [∘] A _ _)) (π₂ τ [ σ ]))
        ≡⟨ conv² (congTmΓ (sym $ [∘] A _ _)) (cong (Tm Γ) eq4L) ⟩
      conv (trans (congTmΓ (sym $ [∘] A _ _)) (cong (Tm Γ) eq4L)) (π₂ τ [ σ ])
        ≡⟨ conv-unique _ refl _ ⟩
      π₂ τ [ σ ]
        ∎

{-
π₂∘ : (σ : Sub Δ (Γ , A))(τ : Sub Θ Δ) → conv (congTmΓ (trans (congA[] (π₁∘ σ τ)) ([∘] A (π₁ σ) τ))) (π₂ (σ ∘ τ))
                                         ≡ π₂ σ [ τ ]
π₂∘ {Δ} {Γ} {A} {Θ} σ τ =
  begin
    conv (congTmΓ (trans (congA[] (π₁∘ σ τ)) ([∘] A (π₁ σ) τ))) (π₂ (σ ∘ τ))
  ≡⟨
    conv-unique (congTmΓ (trans (congA[] (π₁∘ σ τ)) ([∘] A (π₁ σ) τ)))
                (trans (trans (trans p1 p2) p3) p4)
                (π₂ (σ ∘ τ))
  ⟩
    conv (trans (trans (trans p1 p2) p3) p4) (π₂ (σ ∘ τ))
  ≡⟨ 
    ((eq1 ⟫ p1                     , p2 ⟫ eq2)
          ⟫ trans p1 p2            , p3 ⟫ eq3)
          ⟫ trans (trans p1 p2) p3 , p4 ⟫ eq4
  ⟩
    π₂ σ [ τ ]
  ∎

  
  where
    p1 : Tm Θ (A [ π₁ (σ ∘ τ) ]) ≡ Tm Θ (A [ π₁ ((π₁ σ , π₂ σ) ∘ τ) ])
    p1 = congTmΓ (congA[] (congπ₁ refl refl refl (cong∘ refl refl refl ηπ refl)))

    p2 : Tm Θ (A [ π₁ ((π₁ σ , π₂ σ) ∘ τ) ]) ≡ Tm Θ (A [ π₁ ((π₁ σ ∘ τ) , conv (congTmΓ (sym ([∘] A (π₁ σ) τ))) (π₂ σ [ τ ])) ])
    p2 = congTmΓ (congA[] (congπ₁ refl refl refl ,∘))
    
    p3 : Tm Θ (A [ π₁ ((π₁ σ ∘ τ) , conv (congTmΓ (sym ([∘] A (π₁ σ) τ))) (π₂ σ [ τ ])) ])
         ≡ Tm Θ (A [ π₁ σ ∘ τ ])
    p3 = congTmΓ (congA[] βπ₁)

    p4 : Tm Θ (A [ π₁ σ ∘ τ ]) ≡ Tm Θ (A [ π₁ σ ] [ τ ])
    p4 = congTmΓ ([∘] A (π₁ σ) τ)
    
    eq1 : conv (congTmΓ (congA[] (congπ₁ refl refl refl (cong∘ refl refl refl ηπ refl)))) (π₂ (σ ∘ τ)) ≡ π₂ ((π₁ σ , π₂ σ) ∘ τ)
    eq1 = congπ₂ refl refl {σ = σ ∘ τ} refl (cong∘ refl refl refl {σ = σ} {τ = τ} ηπ refl)

    eq2 : conv (congTmΓ (congA[] (congπ₁ refl refl refl ,∘))) (π₂ ((π₁ σ , π₂ σ) ∘ τ)) ≡ π₂ ((π₁ σ ∘ τ) , conv (congTmΓ (sym ([∘] A (π₁ σ) τ))) (π₂ σ [ τ ]))
    eq2 = congπ₂ refl refl refl ,∘

    eq3 : conv (congTm refl (congA[] βπ₁)) (π₂ ((π₁ σ ∘ τ) , conv (congTmΓ (sym ([∘] A (π₁ σ) τ))) (π₂ σ [ τ ])))
           ≡ conv (congTmΓ (sym ([∘] A (π₁ σ) τ))) (π₂ σ [ τ ])
    eq3 = βπ₂

    eq4 : conv (congTmΓ ([∘] A (π₁ σ) τ)) (conv (congTmΓ (sym ([∘] A (π₁ σ) τ))) (π₂ σ [ τ ])) ≡ π₂ σ [ τ ]
    eq4 = begin
        conv (congTmΓ ([∘] A (π₁ σ) τ)) (conv (congTmΓ (sym ([∘] A (π₁ σ) τ))) (π₂ σ [ τ ]))
      ≡⟨ conv² (congTmΓ (sym ([∘] A (π₁ σ) τ))) (congTmΓ ([∘] A (π₁ σ) τ)) ⟩
        conv (trans (congTmΓ (sym ([∘] A (π₁ σ) τ))) (congTmΓ ([∘] A (π₁ σ) τ))) (π₂ σ [ τ ])
      ≡⟨ cong (λ eq → conv eq (π₂ σ [ τ ])) (trans-congTmΓ {p = sym ([∘] A (π₁ σ) τ)} {[∘] A (π₁ σ) τ}) ⟩
        conv (congTmΓ (trans (sym ([∘] A (π₁ σ) τ)) ([∘] A (π₁ σ) τ))) (π₂ σ [ τ ])
      ≡⟨ cong (λ eq → conv (congTmΓ eq) (π₂ σ [ τ ])) (trans-symˡ ([∘] A (π₁ σ) τ)) ⟩
        π₂ σ [ τ ]
      ∎
-}

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
