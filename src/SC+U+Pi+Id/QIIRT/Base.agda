module SC+U+Pi+Id.QIIRT.Base where
 
open import Prelude
  hiding (_,_)


infixl 20 _↑_ _⁺ _⇈_
infixr 15 [_]_ [_]t_ [_]tm_ [_]l_
infixl 10 _⧺_
infixl 10 _⨟_
infixl 6 _,_

variable
  i j k : ℕ

interleaved mutual
  data Ctx            : Set
  data Ty   (Γ : Ctx) : ℕ → Set
  data Sub  (Γ : Ctx) : Ctx → Set
  data Tm             : (Γ : Ctx) → Ty Γ i → Set
  
  variable
    Γ Δ Θ : Ctx
    A B C : Ty Γ i
    t u a : Tm Γ A
    σ τ γ : Sub Γ Δ

  postulate
    [_]_ : (σ : Sub Γ Δ) (A : Ty Δ i) → Ty Γ i

  data _ where
    ∅
      : Ctx
    _,_
      : (Γ : Ctx) (A : Ty Γ i)
      → Ctx
    ∅
      : Sub Γ ∅
    _,_
      : (σ : Sub Γ Δ) {A : Ty Δ i} (t : Tm Γ ([ σ ] A))
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

  -- ⟨_⟩ : Tm Γ A → Sub Γ (Γ , A)
  -- pattern ⟨_⟩ t = idS , t 
  -- ⟨_⟩ : Tm Γ A → Sub Γ (Γ , A)
  -- ⟨ t ⟩ = idS , {!t!}

  data _ where
    U
      : (i : ℕ)
      → Ty Γ (suc i)
    El
      : Tm Γ (U i) 
      → Ty Γ i
    Lift
      : Ty Γ i
      → Ty Γ (suc i)
    Π
      : (A : Ty Γ i) → Ty (Γ , A) i
      → Ty Γ i
    Id
      : (a : Tm Γ (U i)) (t u : Tm Γ (El a)) 
      → Ty Γ i
    π₂
      : (σ : Sub Γ (Δ , A))
      → Tm Γ ([ π₁ σ ] A)
    [_]tm_
      : (σ : Sub Γ Δ) {A : Ty Δ i}
      → Tm Δ A
      → Tm Γ ([ σ ] A)
    c
      : Ty Γ i
      → Tm Γ (U i)
    mk
      : Tm Γ A
      → Tm Γ (Lift A)
    un
      : Tm Γ (Lift A)
      → Tm Γ A
    ƛ_
      : Tm (Γ , A) B → Tm Γ (Π A B)
    app
      : Tm Γ (Π A B) 
      → Tm (Γ , A) B

  pattern wk   = π₁ idS
  pattern vz   = π₂ idS
  pattern vs x = [ wk ]tm x

  _⁺ : (σ : Sub Γ Δ) → {A : Ty Δ i} → Sub (Γ , [ σ ] A) (Δ , A)
  _⁺ σ {A} = π₁ idS ⨟ σ , π₂ idS

  _↑_
    : (σ : Sub Γ Δ) (A : Ty Δ i)
    → Sub (Γ , [ σ ] A) (Δ , A)
  idS           ↑ A = idS
  (σ ⨟ τ)       ↑ A = σ ↑ ([ τ ] A) ⨟ (τ ↑ A)
  π₁ (σ , t)    ↑ A = σ ↑ A
  π₁ (σ ⨟ τ)    ↑ A = σ ↑ ([ π₁ τ ] A) ⨟ (π₁ τ ↑ A)
  τ@∅           ↑ A = τ ⁺
  τ@(σ , t)     ↑ A = τ ⁺
  τ@(π₁ idS)    ↑ A = τ ⁺
  τ@(π₁ (π₁ σ)) ↑ A = τ ⁺

  [_]t_ : {Γ Δ : Ctx} (σ : Sub Γ Δ) {A : Ty Δ i} (u : Tm Δ A)
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
      : (σ ⨟ (τ , t)) ≡ (σ ⨟ τ , [ σ ]tm t)
    η∅
      : {σ : Sub Γ ∅}
      → σ ≡ ∅
    η,
      : {σ : Sub Γ (Δ , A)}
      → σ ≡ (π₁ σ , π₂ σ)
  -- Equality constructors for terms
    [id]tm
      : [ idS   ]tm t ≡ t
    [⨟]tm
      : [ σ ⨟ τ ]tm t ≡ [ σ ]tm [ τ ]tm t
    π₂,
      : {σ : Sub Γ Δ}{A : Ty Δ i}{t : Tm Γ ([ σ ] A)}
      →  π₂ (σ , t) ≡ t 

  -- Structural rules for type formers
    []U
      : [ σ ] (U i) ≡ U i
    {-# REWRITE []U #-}
    []El
      : (σ : Sub Γ Δ) (u : Tm Δ (U i))
      → [ σ ] (El u) ≡ El ([ σ ]t u)
    {-# REWRITE []El #-}
    []Lift
      : [ σ ] (Lift A) ≡ Lift ([ σ ] A)
    {-# REWRITE []Lift #-}
    []Π
      : [ σ ] Π A B ≡ Π ([ σ ] A) ([ σ ↑ A ] B)
    {-# REWRITE []Π #-}
    []Id
      : {σ : Sub Γ Δ} {a : Tm Δ (U i)} {t u : Tm Δ (El a)}
      → [ σ ] (Id a t u)
      ≡ Id ([ σ ]t a) ([ σ ]t t) ([ σ ]t u)
    {-# REWRITE []Id #-}

  -- Structural rules for term formers
    []tc    : (σ : Sub Γ Δ) (A : Ty Δ i)
      → [ σ ]tm (c A) ≡ c ([ σ ] A)
    []mk
      : [ σ ]tm (mk t) ≡ mk ([ σ ]tm t)
    []un
      : (σ : Sub Γ Δ) (A : Ty Δ i) (t : Tm Δ (Lift A))
      → [ σ ]tm un t ≡ un ([ σ ]tm t)
  -- Computational rules
    Uβ
      : El (c A) ≡ A
    Uη
      : c (El u) ≡ u
    Liftβ
      : un (mk u) ≡ u
    Liftη
      : mk (un u) ≡ u
    reflect
      : {a : Tm Γ (U i)} {t u : Tm Γ (El a)} → Tm Γ (Id a t u)
      → t ≡ u
    []ƛ
      : [ σ ]tm (ƛ t) ≡ ƛ ([ σ ↑ _ ]tm t )
    Πβ
      : app (ƛ t) ≡ t
    Πη
      : ƛ (app t) ≡ t

data Tel (Γ : Ctx) : Set
_⧺_ : (Γ : Ctx) (Ξ : Tel Γ) → Ctx

data Tel Γ where
  ∅ : Tel Γ
  _,_ : (Ξ : Tel Γ) (A : Ty (Γ ⧺ Ξ) i) → Tel Γ

Γ ⧺ ∅       = Γ
Γ ⧺ (Ξ , A) = (Γ ⧺ Ξ) , A

[_]l_ : Sub Γ Δ → Tel Δ → Tel Γ
_⇈_   : (σ : Sub Γ Δ) → (Ξ : Tel Δ) → Sub (Γ ⧺ ([ σ ]l Ξ)) (Δ ⧺ Ξ)

[ σ ]l ∅       = ∅
[ σ ]l (Ξ , A) = [ σ ]l Ξ , [ σ ⇈ Ξ ] A

σ ⇈ ∅       = σ
σ ⇈ (Ξ , A) = (σ ⇈ Ξ) ↑ A
