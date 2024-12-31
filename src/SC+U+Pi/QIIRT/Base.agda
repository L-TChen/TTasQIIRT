module SC+U+Pi.QIIRT.Base where
 
open import Prelude
  hiding (_,_)

open import Data.Nat

infixr 20 [_]_ [_]t_ [_]tm_
infixl 20 _↑_ _⁺
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
    t u   : Tm Γ A
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
    [id]  : [ idS        ] A ≡ A
    [⨟]   : [ σ ⨟ τ      ] A ≡ [ σ ] [ τ ] A
    [π₁,] : [ π₁ (σ , t) ] A ≡ [ σ ] A
    [π₁⨟] : [ π₁ (σ ⨟ τ) ] A ≡ [ σ ] [ π₁ τ ] A
    {-# REWRITE [id] [⨟] [π₁,] [π₁⨟] #-}

  data _ where
    U
      : (i : ℕ)
      → Ty Γ (suc i)
    Π
      : (A : Ty Γ i) → Ty (Γ , A) i
      → Ty Γ i
    El
      : Tm Γ (U i) 
      → Ty Γ i
    π₂
      : (σ : Sub Γ (Δ , A))
      → Tm Γ ([ π₁ σ ] A)
    [_]tm_
      : {Γ Δ : Ctx} (σ : Sub Γ Δ) {A : Ty Δ i}
      → Tm Δ A
      → Tm Γ ([ σ ] A)
    c
      : Ty Γ i
      → Tm Γ (U i)
    ƛ_
      : Tm (Γ , A) B → Tm Γ (Π A B)
    app
      : Tm Γ (Π A B) 
      → Tm (Γ , A) B

  pattern wk   = π₁ idS
  pattern vz   = π₂ idS
  pattern vs x = [ wk ]tm x

  _⁺ : (σ : Sub Γ Δ) {A : Ty Δ i} → Sub (Γ , [ σ ] A) (Δ , A)
  σ ⁺ = wk ⨟ σ , vz

  _↑_
    : (σ : Sub Γ Δ) (A : Ty Δ i)
    → Sub (Γ , [ σ ] A) (Δ , A)
  idS        ↑ A = idS
  (σ ⨟ τ)    ↑ A = σ ↑ ([ τ ] A) ⨟ (τ ↑ A)
  π₁ (σ , t) ↑ A = σ ↑ A
  π₁ (σ ⨟ τ) ↑ A = σ ↑ ([ π₁ τ ] A) ⨟ (π₁ τ ↑ A)
  {-# CATCHALL #-}
  σ          ↑ A = σ ⁺

-- {-
--   [_]t_ : {Γ Δ : Ctx} (σ : Sub Γ Δ) {A : Ty Δ} (u : Tm Δ A)
--     → Tm Γ ([ σ ] A)
--   [ idS        ]t u = u
--   [ σ ⨟ τ      ]t u = [ σ ]t [ τ ]t u
--   [ π₁ (σ , t) ]t u = [ σ ]t u
--   [ π₁ (σ ⨟ τ) ]t u = [ σ ]t [ π₁ τ ]t u
--   {-# CATCHALL #-}
--   [ σ          ]t u = [ σ ]tm u
-- -}

  postulate
    [_]t_ : {Γ Δ : Ctx} (σ : Sub Γ Δ) {A : Ty Δ i} (u : Tm Δ A)
      → Tm Γ ([ σ ] A)
    [id]t   : [ idS        ]t u ≡ u
    [⨟]t    : [ σ ⨟ τ      ]t u ≡ [ σ ]t [ τ ]t u
    [π₁,]t  : [ π₁ (σ , t) ]t u ≡ [ σ ]t u
    [π₁⨟]t  : [ π₁ (σ ⨟ τ) ]t u ≡ [ σ ]t [ π₁ τ ]t u
    {-# REWRITE [id]t [⨟]t [π₁,]t [π₁⨟]t #-}
    [∅]t    : [ ∅ {Γ}            ]t u ≡ [ ∅ {Γ}     ]tm u
    [,]t    : [ σ , t            ]t u ≡ [ σ , t     ]tm u
    [π₁id]  : [ π₁ (idS {Γ , A}) ]t u ≡ [ π₁ idS    ]tm u
    [π₁π₁σ] : [ π₁ (π₁ σ)        ]t u ≡ [ π₁ (π₁ σ) ]tm u
    {-# REWRITE [∅]t [,]t [π₁id] [π₁π₁σ] #-}

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
    [id]tm
      : [ idS   ]tm t ≡ t
    [⨟]tm
      : [ σ ⨟ τ ]tm t ≡ [ σ ]tm [ τ ]tm t
    π₂,
      : {σ : Sub Γ Δ}{A : Ty Δ i}{t : Tm Γ ([ σ ] A)}
      →  π₂ (σ , t) ≡ t 

  postulate
    U[]
      : [ σ ] (U i) ≡ U i
    {-# REWRITE U[] #-}
    c[]t    : (σ : Sub Γ Δ) (A : Ty Δ i)
      → [ σ ]t (c A) ≡ c ([ σ ] A)
    El[]
      : (σ : Sub Γ Δ) (u : Tm Δ (U i))
      → [ σ ] (El u) ≡ El ([ σ ]t u)
    {-# REWRITE El[] #-}
    Uβ
      : El (c A) ≡ A
    Uη
      : c (El u) ≡ u
    Lift
      : Ty Γ i
      → Ty Γ (suc i)
    Lift[]
      : [ σ ] (Lift A) ≡ Lift ([ σ ] A)
    {-# REWRITE Lift[] #-}
    mk
      : Tm Γ A
      → Tm Γ (Lift A)
    []mk
      : [ σ ]tm (mk t) ≡ mk ([ σ ]tm t)
    un
      : Tm Γ (Lift A)
      → Tm Γ A
    []un
      : (σ : Sub Γ Δ) (A : Ty Δ i) (t : Tm Δ (Lift A))
      → [ σ ]tm un t ≡ un ([ σ ]tm t)
    Liftβ
      : un (mk u) ≡ u
    Liftη
      : mk (un u) ≡ u
    Π[]
      : [ σ ] Π A B ≡ Π ([ σ ] A) ([ σ ↑ A ] B)
    {-# REWRITE Π[] #-}
    []ƛ
      : [ σ ]tm (ƛ t) ≡ ƛ ([ σ ↑ _ ]tm t )
    Πβ
      : app (ƛ t) ≡ t
    Πη
      : ƛ (app t) ≡ t

vz↦ : Tm Γ A → Sub Γ (Γ , A)
vz↦ t = idS , t
