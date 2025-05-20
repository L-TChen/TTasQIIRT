-- Formalising Substitution Calculus as QIIT
open import Prelude
  hiding (_∘_)

module Theory.SC.QIIT.Syntax where

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

TmFam : {Γ : Ctx}(A : Ty Γ) → Set
TmFam {Γ} = Tm Γ

-- derived computation rules on composition
βπ : {A : Ty Δ} (σ : Sub Γ Δ) (t : Tm Γ (A [ σ ]))
  → _≡_ {A = ∃ λ σ → Tm Γ (A [ σ ])}
        (π₁ (σ , t) , π₂ (σ , t))
        (σ , t)
βπ σ t = βπ₁ ,Σ≡ βπ₂

π∘ : (σ : Sub Γ Δ) {A : Ty Θ} (τ : Sub Δ (Θ , A))
   →  _≡_ {A = ∃ λ σ → Tm Γ (A [ σ ])}
          (π₁ (τ ∘ σ) , π₂ (τ ∘ σ))
          (π₁ τ ∘ σ   , tr TmFam (sym $ [∘] _ _ _) (π₂ τ [ σ ]))
π∘ σ {A} τ = begin
  π₁ (τ ∘ σ) , π₂ (τ ∘ σ)
    ≡⟨ ap,Σ (λ τ → π₁ (τ ∘ σ)) (λ τ → π₂ (τ ∘ σ)) ηπ ⟩
  π₁ ((π₁ τ , π₂ τ) ∘ σ) , π₂ ((π₁ τ , π₂ τ) ∘ σ)
    ≡⟨ ap,Σ π₁ π₂ ,∘ ⟩
  π₁ (π₁ τ ∘ σ , _) , π₂ (_ , tr TmFam (sym $ [∘] _ _ _) (π₂ τ [ σ ]))
    ≡⟨ βπ (π₁ τ ∘ σ) (tr TmFam (sym $ [∘] _ _ _) (π₂ τ [ σ ] )) ⟩
  π₁ τ ∘ σ , tr TmFam (sym $ [∘] A (π₁ τ) σ) (π₂ τ [ σ ])
    ∎

π₁∘ : (σ : Sub Δ (Γ , A))(τ : Sub Θ Δ) → π₁ (σ ∘ τ) ≡ π₁ σ ∘ τ
π₁∘ {A = A} {Θ} σ τ = Σ-≡,≡←≡ (π∘ τ σ) .proj₁

π₁idS∘ : {A : Ty Γ}(σ : Sub Δ (Γ , A)) → π₁ idS ∘ σ ≡ π₁ σ
π₁idS∘ σ = begin
  π₁ idS ∘ σ
    ≡⟨ sym (π₁∘ idS σ) ⟩
  π₁ (idS ∘ σ)
    ≡⟨ cong π₁ (idS∘ σ) ⟩
  π₁ σ
    ∎

π₂∘-tot : (σ : Sub Γ Δ) {A : Ty Θ} (τ : Sub Δ (Θ , A))
  → _≡_ {_} {∃ (Tm Γ)} (A [ π₁ (τ ∘ σ) ] , π₂ (τ ∘ σ)) (A [ π₁ τ ] [ σ ] , π₂ τ [ σ ])
π₂∘-tot {Γ} {Δ} σ {A} τ = begin
  A [ π₁ (τ ∘ σ) ] , π₂ (τ ∘ σ)
    ≡⟨ apΣ TmFam (A [_]) (π∘ σ τ) ⟩
  A [ π₁ τ ∘ σ ] , tr TmFam (sym $ [∘] _ _ _) (π₂ τ [ σ ])
    ≡⟨ lift TmFam (π₂ τ [ σ ]) (sym $ [∘] _ _ _) ⟨
  A [ π₁ τ ] [ σ ] , π₂ τ [ σ ]
    ∎

π₂∘ : (τ : Sub Δ (Θ , A))(σ : Sub Γ Δ)
    → tr TmFam (cong (A [_]) (π₁∘ τ σ) ∙ [∘] _ _ _) (π₂ (τ ∘ σ))
    ≡ π₂ τ [ σ ]
π₂∘ {A = A} τ σ = begin
  tr TmFam (cong (A [_]) (π₁∘ τ σ) ∙ [∘] _ _ _) (π₂ (τ ∘ σ))
    ≡⟨ cong (λ p → tr TmFam p (π₂ (τ ∘ σ))) (uip _ (Σ-≡,≡←≡ (π₂∘-tot σ τ) .proj₁)) ⟩
  tr TmFam (Σ-≡,≡←≡ (π₂∘-tot σ τ) .proj₁) (π₂ (τ ∘ σ))
    ≡⟨ Σ-≡,≡←≡ (π₂∘-tot σ τ) .proj₂ ⟩
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
