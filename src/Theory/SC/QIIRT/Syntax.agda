-- Formalising Substitution Calculus as QIIRT
module Theory.SC.QIIRT.Syntax where

open import Prelude
  hiding (_,_; _∘_)

-- inductive-inductive-recursive definition of context, type, term, and type substitution

infixl 35 _[_] _[_]tm
infixl 10 _,_

interleaved mutual
  data Ctx : Set
  data Ty  (Γ : Ctx) : Set
  data Sub (Γ : Ctx) : Ctx → Set
  data Tm  : (Γ : Ctx) → Ty Γ → Set

  postulate
    _[_]  : ∀{Δ Γ} → Ty Γ → Sub Δ Γ → Ty Δ

  variable
    Γ Δ Θ : Ctx
    A B C : Ty Γ
    t u   : Tm Γ A
    σ τ γ : Sub Δ Γ

  data _ where
    ∅
      : Ctx
    _,_
      : (Γ : Ctx) (A : Ty Γ)
      → Ctx
    ∅
      : Sub Γ ∅
    _,_
      : (σ : Sub Γ Δ) (t : Tm Γ (A [ σ ]))
      → Sub Γ (Δ , A)
    idS
      : Sub Γ Γ
    _∘_
      : {Δ Θ : Ctx}
      → (σ : Sub Δ Θ) (δ : Sub Γ Δ)
      → Sub Γ Θ
    π₁
      : (σ : Sub Γ (Δ , A))
      → Sub Γ Δ
    U
      : Ty Γ
    π₂
      : (σ : Sub Δ (Γ , A))
      → Tm Δ (A [ π₁ σ ])
    _[_]tm
      : Tm Γ A → (σ : Sub Δ Γ)
      → Tm Δ (A [ σ ])

  postulate
    U[]   : U [ σ ] ≡ U
    {-# REWRITE U[] #-}

    [id]  : A [ idS ]        ≡ A
    [∘]   : A [ τ ∘ σ ]      ≡ A [ τ ] [ σ ]
    [π₁,] : A [ π₁ (σ , t) ] ≡ A [ σ ]
    [π₁∘] : A [ π₁ (τ ∘ σ) ] ≡ A [ π₁ τ ] [ σ ]
    {-# REWRITE [id] [∘] [π₁,] [π₁∘] #-}

  postulate
    [id]tm : t [ idS   ]tm ≡ t
    [∘]tm  : t [ τ ∘ σ ]tm ≡ t [ τ ]tm [ σ ]tm
    -- equality constructors
    idS∘_ 
      : (σ : Sub Δ Γ)
      → idS ∘ σ ≡ σ
    _∘idS
      : (σ : Sub Δ Γ)
      → σ ∘ idS ≡ σ
    assocS
      : (σ ∘ τ) ∘ γ ≡ σ ∘ (τ ∘ γ)
    ,∘
      : (σ , t) ∘ τ ≡ σ ∘ τ , t [ τ ]tm
    π₁,
      : π₁ (σ , t) ≡ σ
    π₂,
      : π₂ (σ , t) ≡ t
    η∅
      : {σ : Sub Δ ∅}
      → σ ≡ ∅
    η,
      : σ ≡ π₁ σ , π₂ σ

-- derived computation rules on composition
π₁∘
  : (σ : Sub Γ Δ) (τ : Sub Δ (Θ , A))
  → π₁ (τ ∘ σ) ≡ π₁ τ ∘ σ
π₁∘ σ τ = begin
    π₁ (τ ∘ σ)                     ≡⟨ cong (λ σ' → π₁ (σ' ∘ σ)) η, ⟩
    π₁ ((π₁ τ , π₂ τ) ∘ σ)         ≡⟨ cong π₁ ,∘ ⟩ 
    π₁ (π₁ τ ∘ σ , (π₂ τ) [ σ ]tm) ≡⟨ π₁, ⟩
    π₁ τ ∘ σ                       ∎
  where open ≡-Reasoning

π₁idS∘ : {A : Ty Γ}(σ : Sub Δ (Γ , A)) → π₁ idS ∘ σ ≡ π₁ σ
π₁idS∘ σ = begin
  π₁ idS ∘ σ      ≡⟨ π₁∘ σ idS ⟨
  π₁ (idS ∘ σ)    ≡⟨ cong π₁ (idS∘ σ) ⟩
  π₁ σ            ∎
  where open ≡-Reasoning

π₂∘ : (σ : Sub Γ Δ) (τ : Sub Δ (Θ , A))
  → π₂ (τ ∘ σ) ≡ π₂ τ [ σ ]tm
π₂∘ {Γ} {Δ} {Θ} {A} σ τ = begin
  π₂ (τ ∘ σ)                         ≡⟨ ≅-to-≡ $ hcong (λ ν → π₂ (ν ∘ σ)) (≡-to-≅ η,) ⟩
  π₂ (((π₁ τ) , (π₂ τ)) ∘ σ)         ≡⟨ ≅-to-≡ $ hcong π₂ (≡-to-≅ ,∘) ⟩
  π₂ (((π₁ τ ∘ σ) , (π₂ τ [ σ ]tm))) ≡⟨ π₂, ⟩
  π₂ τ  [ σ ]tm                      ∎
  where open ≡-Reasoning

-- We will need to prove coherence for the following with another rewriting relation:
-- coherence of postulates
coh[idS∘] : A [ idS ∘ σ ] ≡ A [ σ ]
coh[idS∘] = refl

coh[∘idS] : A [ σ ∘ idS ] ≡ A [ σ ]
coh[∘idS] = refl

coh[assocS] : A [ (σ ∘ τ) ∘ γ ] ≡ A [ σ ∘ (τ ∘ γ) ]
coh[assocS] = refl

coh[βπ₁] : A [ π₁ (σ , t) ] ≡ A [ σ ]
coh[βπ₁] = refl

coh[η,] : ∀ A → A [ σ ] ≡ A [ π₁ σ , π₂ σ ]
coh[η,] U = refl

coh[η∅] : ∀ A → A [ σ ] ≡ A [ ∅ ]
coh[η∅] U = refl
    
-- syntax abbreviations
-- wk : Sub (Δ , A) Δ
pattern wk = π₁ idS
-- vz : Tm (Γ , A) (A [ wk ])
pattern vz = π₂ idS
-- vs : Tm Γ A → Tm (Γ , B) (A [ wk ])   
pattern vs x = x [ wk ]tm
-- vs (vs ... (vs vz) ...) = π₂ idS [ π₁ idS ]tm .... [ π₁ idS ]tm

vz:= : Tm Γ A → Sub Γ (Γ , A)
vz:= t = idS , t
