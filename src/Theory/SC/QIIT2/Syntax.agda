{-# OPTIONS --cubical --exact-split #-}

-- Type theory as a quotient inductive-inductive-recursive type, inspired by the formualtion of natural models
-- whereas the recursion part is impredicative.

module Theory.SC.QIIT2.Syntax where

open import Cubical.Foundations.Prelude
  hiding (Sub)
open import Cubical.Data.Sigma
  hiding (Sub)
  
infixl 20 _[_]
infixr 10 _∘_
infixl 4 _,_ _,_∶[_]

interleaved mutual
  data Ctx : Set
  data Sub : Ctx → Ctx → Set
  data Ty  : Ctx → Set
  data Tm  : (Γ : Ctx) → Set

  variable
      Γ Δ Θ Ξ : Ctx
      A B C : Ty Γ
      t u   : Tm Γ
      σ τ δ : Sub Γ Δ
  
  data Ctx where
    ∅
      : Ctx
    _,_
      : (Γ : Ctx)(A : Ty Γ)
      → Ctx
      
  tyOf   : Tm Γ → Σ[ Δ ∈ Ctx ] (Sub Γ Δ × Ty Δ)
  idS' : Sub Γ Γ
  _∘'_
    : Sub Δ Θ → Sub Γ Δ
    → Sub Γ Θ
  _,'_∶[_]
    : (σ : Sub Γ Δ) (t : Tm Γ) → tyOf t ≡ (_ , (σ , A))
    → Sub Γ (Δ , A)
      
  data Tm where
    _[_]
      : (t : Tm Δ) (σ : Sub Γ Δ)
      → Tm Γ
    π₂
      : (σ : Sub Γ (Δ , A))
      → Tm Γ
    [idS]tm
      : (t : Tm Γ)
      → t [ idS' ] ≡ t
    [∘]tm
      : (t : Tm Γ)
      → t [ σ ] [ τ ] ≡ t [ σ ∘' τ ]
    βπ₂
      : (t : Tm Γ) (p : tyOf t ≡ (Δ , (σ , A)))
      → π₂ (σ ,' t ∶[ p ]) ≡ t

  data Sub where
    ∅
      : Sub Γ ∅
    _,_∶[_]
      : (σ : Sub Γ Δ) (t : Tm Γ) → tyOf t ≡ (_ , (σ , A))
      → Sub Γ (Δ , A)
    idS
      : Sub Γ Γ
    _∘_
      : Sub Δ Θ → Sub Γ Δ
      → Sub Γ Θ
    π₁
      : Sub Γ (Δ , A)
      → Sub Γ Δ
    idS∘_ 
      : (σ : Sub Γ Δ)
      → idS ∘ σ ≡ σ
    _∘idS
      : (σ : Sub Γ Δ)
      → σ ∘ idS ≡ σ
    assocS
      : (δ ∘ τ) ∘ σ ≡ δ ∘ (τ ∘ σ)
    ,∘
      : (σ : Sub Δ Θ) (t : Tm Δ) (τ : Sub Γ Δ) (p : tyOf t ≡ (_ , (σ , A)))
      → (σ , t ∶[ p ]) ∘ τ ≡ (σ ∘ τ , t [ τ ] ∶[ {!!} ])
    βπ₁
      : (σ : Sub Γ Δ) (t : Tm Γ) (p : tyOf t ≡ (_ , (σ , A)))
      → π₁ (σ , t ∶[ p ]) ≡ σ
    ηπ
      : σ ≡ (π₁ σ , π₂ σ ∶[ {!!} ]) -- refl?
    η∅
      : σ ≡ ∅

  idS' = idS
  _∘'_ = _∘_
  _,'_∶[_] = _,_∶[_]

  data Ty where
    _[_]
      : (A : Ty Δ)(σ : Sub Γ Δ)
      → Ty Γ
    U
      : Ty Γ
    U[]
      : U [ σ ] ≡ U
    [∘]
      : A [ τ ∘ σ ] ≡ A [ τ ] [ σ ]
      
  tyOf (t [ σ ]) =
    let  (Θ , (τ , A)) = tyOf t
    in _ , (τ ∘ σ , A)
  tyOf (π₂ {A = A} σ)  = _ , (π₁ σ , A) -- π₁ σ , {!!} -- A [ π₁ σ ]
  tyOf ([idS]tm t i)   = {!!}
  tyOf ([∘]tm   t i)   = {!!}
  tyOf (βπ₂     t p i) = {!!}

π₁∘
  : (σ : Sub Δ (Γ , A))(τ : Sub Θ Δ)
  → π₁ (σ ∘ τ) ≡ π₁ σ ∘ τ
π₁∘ σ τ = {!!}

π₂∘
  : (τ : Sub Δ (Θ , A))(σ : Sub Γ Δ)
  → π₂ (τ ∘ σ) ≡ (π₂ τ) [ σ ]
π₂∘ τ σ = 
  π₂ (τ ∘ σ)
    ≡⟨ {!!} ⟩
  π₂ ((π₁ τ , π₂ τ ∶[ {!!} ]) ∘ σ)
    ≡⟨ {!!} ⟩
  π₂ (π₁ τ ∘ σ , π₂ τ [ σ ] ∶[ {!!} ])
    ≡⟨ βπ₂ (π₂ τ [ σ ]) {!!} ⟩
  π₂ τ [ σ ]
    ∎

-- syntax abbreviations
wk : Sub (Δ , A) Δ
wk = π₁ idS

vz : Tm (Γ , A)
vz = π₂ idS

vs : Tm Γ → Tm (Γ , B)
vs x = x [ wk ]
-- vs (vs ... (vs vz) ...) = π₂ idS [ π₁ idS ]tm .... [ π₁ idS ]tm

vz:= : (t : Tm Γ) → let (_ , (σ , A)) = tyOf t in Sub Γ (Γ , A [ σ ])
vz:= {Γ} t = idS , t ∶[ {!!} ]
