open import Prelude

module Theory.SC+Tarski+MetaPi.QIIRT.Syntax where

interleaved mutual
  data Ctx : Set
  data Ty : Ctx → Set
  data Tm : (Γ : Ctx) → Ty Γ → Set
  data Sub : (Γ Δ : Ctx) → Set
  data UU  : Set
  T : UU → Set

  variable
    Γ Δ Θ Ξ : Ctx
    A B C   : Ty Γ
    t u v   : Tm Γ A
    σ τ γ   : Sub Γ Δ


  data Ctx where
    ∅
      : Ctx
    _,_
      : (Γ : Ctx) → Ty Γ
      → Ctx

  idS' : Sub Γ Γ
  _∘'_
    : Sub Δ Ξ → Sub Γ Δ
    → Sub Γ Ξ
  π₁'
    : Sub Γ (Δ , A)
    → Sub Γ Δ

  data Ty where
    _[_]
      : Ty Δ → Sub Γ Δ
      → Ty Γ
    U
      : Ty Γ
    [id]T
      : A [ idS' ] ≡ A
    [][]T
      : A [ τ ] [ σ ] ≡ A [ τ ∘' σ ]
      
  π₂'
    : (σ : Sub Γ (Δ , A))
    → Tm Γ (A [ π₁' σ ])

  data Sub where
    ∅
      : Sub Γ ∅
    _,_
      : (σ : Sub Γ Δ) → Tm Γ (A [ σ ])
      → Sub Γ (Δ , A)
    idS
      : Sub Γ Γ
    _∘_
      : Sub Δ Ξ → Sub Γ Δ
      → Sub Γ Ξ
    π₁
      : Sub Γ (Δ , A)
      → Sub Γ Δ
    ∘-identityˡ
      : (σ : Sub Γ Δ)
      → idS ∘ σ ≡ σ
    ∘-identityʳ
      : (σ : Sub Γ Δ)
      → σ ∘ idS ≡ σ
    ∘-assoc
      : (γ ∘ τ) ∘ σ ≡ γ ∘ (τ ∘ σ) 
    ,∘
      : (τ : Sub Δ Ξ) (σ : Sub Γ Δ) {A : Ty Ξ} {t : Tm Δ (A [ τ ])}
      → (τ , t) ∘ σ ≡ (τ ∘ σ , {!!})
    π₁β
      : π₁ (σ , t) ≡ σ
    πη
      : (σ : Sub Γ (Δ , A))
      → Tm Γ (A [ π₁' σ ])
      → σ ≡ (π₁' σ , π₂' σ)
    ∅η
      : (σ : Sub Γ ∅)
      → σ ≡ ∅

  data Tm where
    π₂
      : (σ : Sub Γ (Δ , A))
      → Tm Γ (A [ π₁ σ ])
    _[_]
      : Tm Δ A → (σ : Sub Γ Δ)
      → Tm Γ (A [ σ ])
    π₂β
      : π₂ (σ , t) ≡ {!t!} -- t
      
  data UU where
    `Bool `ℕ : UU
    Π        : (`A : UU) → (T `A → UU) → UU
    μ        : Tm Γ U → UU

  T `Bool         = Bool
  T `ℕ            = ℕ
  T (Π `A `B)     = (x : T `A) → T (`B x)
  T (μ {Γ = Γ} t) = ?

  idS' = idS
  _∘'_ = _∘_
  π₁'  = π₁
  π₂'  = π₂
