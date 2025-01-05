-- Formalizing Substitution Calculus as QIIT
module SC.QIIT2.Base where

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
      Γ Γ' Δ Δ' Θ Θ' Φ : Ctx
      A A' B B'      : Ty Γ
      t t' s            : Tm Γ A
      σ σ' τ δ          : Sub Δ Γ

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
      : (σ , t) ∘ τ ≡ ((σ ∘ τ) , tr (Tm _) (sym $ [∘] _ _ _) (t [ τ ]))
    βπ₁
      : π₁ (σ , t) ≡ σ
    ηπ
      : σ ≡ (π₁ σ , π₂ σ)
    η∅
      : σ ≡ ∅

    -- equality on terms
    [idS]tm
      : (t : Tm Γ A)
      → tr (Tm Γ) ([idS] A) (t [ idS ]) ≡ t
    [∘]tm
      : (t : Tm Γ A)(σ : Sub Δ Γ)(τ : Sub Θ Δ)
      → tr (Tm Θ) ([∘] _ _ _) (t [ σ ∘ τ ]) ≡ t [ σ ] [ τ ]
    βπ₂
      : {σ : Sub Γ Δ}{t : Tm Γ (A [ σ ])}
      → tr (λ σ → Tm Γ (A [ σ ])) βπ₁ (π₂ (σ , t)) ≡ t

-- derived computation rules on composition
π₁∘ : (σ : Sub Δ (Γ , A))(τ : Sub Θ Δ) → π₁ (σ ∘ τ) ≡ π₁ σ ∘ τ
π₁∘ {A = A} {Θ} σ τ = begin
  π₁ (σ ∘ τ)
    ≡⟨ cong (λ σ' → π₁ (σ' ∘ τ)) ηπ ⟩
  π₁ ((π₁ σ , π₂ σ) ∘ τ)
    ≡⟨ cong π₁ ,∘ ⟩
  π₁ (π₁ σ ∘ τ , tr (Tm Θ) (sym $ [∘] _ _ _) (π₂ σ [ τ ]))
    ≡⟨ βπ₁ ⟩
  π₁ σ ∘ τ
    ∎

π₁idS∘ : {A : Ty Γ}(σ : Sub Δ (Γ , A)) → π₁ idS ∘ σ ≡ π₁ σ
π₁idS∘ σ = begin
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
    ≡⟨ eq1L ,Σ≡ eq1R ⟩
  A [ π₁ ((π₁ τ , π₂ τ) ∘ σ) ] , π₂ ((π₁ τ , π₂ τ) ∘ σ)
    ≡⟨ eq2L ,Σ≡ eq2R ⟩
  A [ π₁ (π₁ τ ∘ σ , tr (Tm Γ) (sym $ [∘] _ _ _) (π₂ τ [ σ ])) ] , π₂ (π₁ τ ∘ σ , tr (Tm Γ) (sym $ [∘] _ _ _) (π₂ τ [ σ ]))
    ≡⟨ eq3L ,Σ≡ eq3R ⟩
  A [ π₁ τ ∘ σ ] , tr (Tm Γ) (sym $ [∘] _ _ _) (π₂ τ [ σ ])
    ≡⟨ eq4L ,Σ≡ eq4R ⟩
  A [ π₁ τ ] [ σ ] , π₂ τ [ σ ]
    ∎
  where
    eq1L : A [ π₁ (τ ∘ σ) ] ≡ A [ π₁ ((π₁ τ , π₂ τ) ∘ σ) ]
    eq1L = cong (λ τ → A [ π₁ (τ ∘ σ) ]) ηπ

    eq1R : tr (Tm Γ) eq1L (π₂ (τ ∘ σ)) ≡ π₂ ((π₁ τ , π₂ τ) ∘ σ)
    eq1R = begin
      tr (Tm Γ) eq1L (π₂ (τ ∘ σ))
        ≡⟨ tr-cong ηπ ⟨
      tr (λ τ → Tm Γ (A [ π₁ (τ ∘ σ) ])) ηπ (π₂ (τ ∘ σ))
        ≡⟨ apd (λ τ → π₂ (τ ∘ σ)) ηπ ⟩
      π₂ ((π₁ τ , π₂ τ) ∘ σ)
        ∎
    
    eq2L : A [ π₁ ((π₁ τ , π₂ τ) ∘ σ) ] ≡ A [ π₁ (π₁ τ ∘ σ , tr (Tm Γ) (sym $ [∘] _ _ _) (π₂ τ [ σ ])) ]
    eq2L = cong (λ σ → A [ π₁ σ ]) ,∘

    eq2R : tr (Tm Γ) eq2L (π₂ ((π₁ τ , π₂ τ) ∘ σ))
         ≡ π₂ (π₁ τ ∘ σ , tr (Tm Γ) (sym $ [∘] _ _ _) (π₂ τ [ σ ]))
    eq2R = begin
      tr (Tm Γ) eq2L (π₂ ((π₁ τ , π₂ τ) ∘ σ))
        ≡⟨ tr-cong ,∘ ⟨
      tr (λ σ → Tm Γ (A [ π₁ σ ])) ,∘ (π₂ ((π₁ τ , π₂ τ) ∘ σ))
        ≡⟨ apd π₂ ,∘ ⟩
      π₂ (π₁ τ ∘ σ , tr (Tm Γ) (sym $ [∘] _ _ _) (π₂ τ [ σ ]))
        ∎
    
    eq3L : A [ π₁ (π₁ τ ∘ σ , tr (Tm Γ) (sym $ [∘] _ _ _) (π₂ τ [ σ ])) ]
         ≡ A [ π₁ τ ∘ σ ]
    eq3L = cong (A [_]) βπ₁

    eq3R : tr (Tm Γ) eq3L (π₂ (π₁ τ ∘ σ , tr (Tm Γ) (sym $ [∘] _ _ _) (π₂ τ [ σ ])))
         ≡ tr (Tm Γ) (sym $ [∘] _ _ _) (π₂ τ [ σ ])
    eq3R = begin
      tr (Tm Γ) eq3L (π₂ (π₁ τ ∘ σ , tr (Tm Γ) (sym $ [∘] _ _ _) (π₂ τ [ σ ])))
        ≡⟨ tr-cong βπ₁ ⟨
      tr (λ σ → Tm Γ (A [ σ ])) βπ₁ (π₂ (π₁ τ ∘ σ , tr (Tm Γ) (sym ([∘] _ _ _)) (π₂ τ [ σ ])))
        ≡⟨ βπ₂ ⟩
      tr (Tm Γ) (sym $ [∘] _ _ _) (π₂ τ [ σ ])
        ∎

    eq4L : A [ π₁ τ ∘ σ ] ≡ A [ π₁ τ ] [ σ ]
    eq4L = [∘] A _ _

    eq4R : tr (Tm Γ) eq4L (tr (Tm Γ) (sym $ [∘] _ _ _) (π₂ τ [ σ ])) ≡ π₂ τ [ σ ]
    eq4R = begin
      tr (Tm Γ) eq4L (tr (Tm Γ) (sym $ [∘] _ _ _) (π₂ τ [ σ ]))
        ≡⟨ tr² (sym $ [∘] _ _ _) ⟩
      tr (Tm Γ) (trans (sym $ [∘] _ _ _) ([∘] _ _ _)) (π₂ τ [ σ ])
        ≡⟨ cong (λ p → tr (Tm Γ) p (π₂ τ [ σ ])) (trans-symˡ ([∘] _ _ _)) ⟩
      π₂ τ [ σ ]
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