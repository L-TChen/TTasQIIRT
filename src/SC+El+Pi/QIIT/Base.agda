module SC+El+Pi.QIIT.Base where

open import Prelude
  hiding (_,_)

infixl 20 _↑_
infixr 15 [_]_ [_]tm_
infixl 10 _⨟_
infixl 6 _,_

interleaved mutual
  data Ctx : Set
  data Ty  (Γ : Ctx) : Set
  data Sub (Γ : Ctx) : Ctx → Set
  data Tm : (Γ : Ctx) → Ty Γ → Set
 
  variable
      Γ Δ Θ : Ctx
      A B C : Ty Γ
      t u   : Tm Γ A
      σ τ γ : Sub Γ Δ

  data _ where
    ∅
      : Ctx
    _,_
      : (Γ : Ctx) (A : Ty Γ)
      → Ctx
    [_]_
      : (σ : Sub Γ Δ) (A : Ty Δ)
      → Ty Γ
    ∅
      : Sub Γ ∅
    _,_
      : (σ : Sub Γ Δ) {A : Ty Δ} (t : Tm Γ ([ σ ] A))
      → Sub Γ (Δ , A) 
    idS
      : Sub Γ Γ
    _⨟_
      : (σ : Sub Γ Δ) (τ : Sub Δ Θ) 
      → Sub Γ Θ
    π₁
      : Sub Γ (Δ , A)
      → Sub Γ Δ
    π₂
      : (σ : Sub Γ (Δ , A))
      → Tm Γ ([ π₁ σ ] A)
    [_]tm_
      : (σ : Sub Γ Δ) {A : Ty Δ}
      → Tm Δ        A
      → Tm Γ ([ σ ] A)
    U
      : Ty Γ
    Π
      : (A : Ty Γ) → Ty (Γ , A)
      → Ty Γ
    El
      : Tm Γ U
      → Ty Γ
    abs
      : Tm (Γ , A) B → Tm Γ (Π A B)
    app
      : Tm Γ (Π A B) → Tm (Γ , A) B
      
  pattern wk   = π₁ idS
  pattern vz   = π₂ idS
  pattern vs x = [ wk ]tm x

  postulate
    [idS]
      : [ idS ]   A ≡ A
    [⨟]
      : [ σ ⨟ τ ] A ≡ [ σ ] [ τ ] A

  -- Equality constructors for substitutions
    _⨟idS
      : (σ : Sub Γ Δ)
      → σ ⨟ idS ≡ σ
    idS⨟_
      : (σ : Sub Γ Δ)
      → idS ⨟ σ ≡ σ
    assocS
      :  σ ⨟ (τ ⨟ γ) ≡ (σ ⨟ τ) ⨟ γ
    ⨟,
      : (σ ⨟ (τ , t)) ≡ (σ ⨟ τ) , tr (Tm Γ) (sym [⨟]) ([ σ ]tm t)
    π₁,
      : π₁ (σ , t) ≡ σ
    η∅
      : {σ : Sub Γ ∅}
      → σ ≡ ∅
    η,
      : {σ : Sub Γ (Δ , A)}
      → σ ≡ (π₁ σ , π₂ σ)
    [id]tm
      : tr (Tm Γ) [idS] ([ idS ]tm t) ≡ t
    [∘]tm
      : tr (Tm Γ) [⨟]   ([ σ ⨟ τ ]tm t) ≡ [ σ ]tm ([ τ ]tm t)
    π₂,
      : {σ : Sub Γ Δ}{A : Ty Δ}{t : Tm Γ ([ σ ] A)}
      →  tr (Tm Γ) (cong ([_] A) π₁,) (π₂ (σ , t)) ≡ t

  _↑_ : (σ : Sub Γ Δ) (A : Ty Δ) → Sub (Γ , [ σ ] A) (Δ , A)
  σ ↑ A = π₁ idS ⨟ σ , tr (Tm _) (sym [⨟]) vz

  postulate
    []U
      : [ σ ] U ≡ U
    []El
      : [ σ ] (El u) ≡ El (tr (Tm Γ) []U ([ σ ]tm u))
    []Π
      : [ σ ] (Π A B) ≡ Π ([ σ ] A) ([ σ ↑ A ] B)
    Πβ
      : app (abs t) ≡ t
    Πη
      : abs (app t) ≡ t
    []abs
      : tr (Tm Γ) []Π ([ σ ]tm (abs t)) ≡ abs ([ σ ↑ A ]tm t)
    
    
