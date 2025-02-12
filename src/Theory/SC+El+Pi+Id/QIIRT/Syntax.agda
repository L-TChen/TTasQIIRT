module Theory.SC+El+Pi+Id.QIIRT.Syntax where
 
open import Prelude

infixl 20 _↑_ _⁺
infixr 15 [_]_ [_]t_ [_]tm_
infixl 10 _⨟_
infixl 4 _,_

interleaved mutual
  data Ctx            : Set
  data Ty   (Γ : Ctx) : Set
  data Sub  (Γ : Ctx) : Ctx → Set
  data Tm             : (Γ : Ctx) → Ty Γ → Set
  
  variable
    Γ Δ Θ : Ctx
    A B C : Ty Γ
    t u a : Tm Γ A
    σ τ γ : Sub Γ Δ

  postulate
    [_]_ : (σ : Sub Γ Δ) (A : Ty Δ) → Ty Γ

  data _ where
    ∅
      : Ctx
    _,_
      : (Γ : Ctx) (A : Ty Γ)
      → Ctx
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

  postulate
    [id]    : [ idS        ] A ≡ A
    [⨟]     : [ σ ⨟ τ      ] A ≡ [ σ ] [ τ ] A
    [π₁,]   : [ π₁ (σ , t) ] A ≡ [ σ ] A
    [π₁⨟]   : [ π₁ (σ ⨟ τ) ] A ≡ [ σ ] [ π₁ τ ] A
    {-# REWRITE [id] [⨟] [π₁,] [π₁⨟] #-}

  data _ where
    U
      : Ty Γ
    El
      : Tm Γ U
      → Ty Γ
    Π
      : (A : Ty Γ) → Ty (Γ , A)
      → Ty Γ
    Id
      : (a : Tm Γ U) (t u : Tm Γ (El a)) 
      → Ty Γ
    π₂
      : (σ : Sub Γ (Δ , A))
      → Tm Γ ([ π₁ σ ] A)
    [_]tm_
      : (σ : Sub Γ Δ) {A : Ty Δ}
      → Tm Δ A
      → Tm Γ ([ σ ] A)
    ƛ_
      : Tm (Γ , A) B → Tm Γ (Π A B)
    app
      : Tm Γ (Π A B) 
      → Tm (Γ , A) B

  pattern wk   = π₁ idS
  pattern vz   = π₂ idS
  pattern vs x = [ wk ]tm x

  _⁺ : (σ : Sub Γ Δ) → {A : Ty Δ} → Sub (Γ , [ σ ] A) (Δ , A)
  _⁺ σ {A} = π₁ idS ⨟ σ , π₂ idS

  _↑_
    : (σ : Sub Γ Δ) (A : Ty Δ)
    → Sub (Γ , [ σ ] A) (Δ , A)
  idS           ↑ A = idS
  (σ ⨟ τ)       ↑ A = σ ↑ ([ τ ] A) ⨟ (τ ↑ A)
  π₁ (σ , t)    ↑ A = σ ↑ A
  π₁ (σ ⨟ τ)    ↑ A = σ ↑ ([ π₁ τ ] A) ⨟ (π₁ τ ↑ A)
  τ@∅           ↑ A = τ ⁺
  τ@(σ , t)     ↑ A = τ ⁺
  τ@(π₁ idS)    ↑ A = τ ⁺
  τ@(π₁ (π₁ σ)) ↑ A = τ ⁺

  [_]t_ : {Γ Δ : Ctx} (σ : Sub Γ Δ) {A : Ty Δ} (u : Tm Δ A)
    → Tm Γ ([ σ ] A)
  [ idS           ]t u = u
  [ σ ⨟ τ         ]t u = [ σ ]t [ τ ]t u
  [ π₁ (σ , t)    ]t u = [ σ ]t u
  [ π₁ (σ ⨟ τ)    ]t u = [ σ ]t [ π₁ τ ]t u
  [ τ@∅           ]t u = [ τ ]tm u
  [ τ@(σ , t)     ]t u = [ τ ]tm u
  [ τ@(π₁ idS)    ]t u = [ τ ]tm u
  [ τ@(π₁ (π₁ σ)) ]t u = [ τ ]tm u

  postulate
  -- Equality constructors for substitutions
    _⨟idS
      : (σ : Sub Γ Δ)
      → σ ⨟ idS ≡ σ
    idS⨟_
      : (σ : Sub Γ Δ)
      → idS ⨟ σ ≡ σ
    ⨟-assoc
      : σ ⨟ (τ ⨟ γ) ≡ (σ ⨟ τ) ⨟ γ
    π₁,
      : π₁ (σ , t) ≡ σ
    ⨟,
      : (σ ⨟ (τ , t)) ≡ (σ ⨟ τ , [ σ ]t t)
    η∅
      : {σ : Sub Γ ∅}
      → σ ≡ ∅
    η,
      : {σ : Sub Γ (Δ , A)}
      → σ ≡ (π₁ σ , π₂ σ)
  -- Equality constructors for terms
    [idS]tm
      : [ idS   ]tm t ≡ t
    [⨟]tm
      : [ σ ⨟ τ ]tm t ≡ [ σ ]tm [ τ ]tm t
    π₂,
      : {σ : Sub Γ Δ}{A : Ty Δ}{t : Tm Γ ([ σ ] A)}
      →  π₂ (σ , t) ≡ t 

  -- Structural rules for type formers
    []U
      : [ σ ] U ≡ U
    {-# REWRITE []U #-}
    []El
      : (σ : Sub Γ Δ) (u : Tm Δ U)
      → [ σ ] (El u) ≡ El ([ σ ]t u)
    {-# REWRITE []El #-}
    []Π
      : [ σ ] Π A B ≡ Π ([ σ ] A) ([ σ ↑ A ] B)
    {-# REWRITE []Π #-}
    []Id
      : {σ : Sub Γ Δ} {a : Tm Δ U} {t u : Tm Δ (El a)}
      → [ σ ] (Id a t u)
      ≡ Id ([ σ ]t a) ([ σ ]t t) ([ σ ]t u)
    {-# REWRITE []Id #-}
  -- Structural rules for term formers
    []ƛ
      : (σ : Sub Γ Δ) (t : Tm (Δ , A) B)
      → [ σ ]tm (ƛ t) ≡ ƛ ([ σ ↑ _ ]tm t )
  -- Computational rules
    reflect
      : {a : Tm Γ U} {t u : Tm Γ (El a)} → Tm Γ (Id a t u)
      → t ≡ u
    Πβ
      : app (ƛ t) ≡ t
    Πη
      : ƛ (app t) ≡ t
