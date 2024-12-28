module SC+El+Pi.QIIRT-Lift.Base where
 
open import Prelude
  hiding (_,_)

infixr 15 [_]l_ [_⇈_]_ [_]_ [_⇈_]t_ [_]t_ [_⇈_]tm_ [_]tm_
infixl 10 _⨟_ _++_
infixl 6 _,_

interleaved mutual
  data Ctx            : Set
  data Lift (Γ : Ctx) : Set
  data Ty   (Γ : Ctx) : Set
  data Sub  (Γ : Ctx) : Ctx → Set
  data Tm             : (Γ : Ctx) → Ty Γ → Set
  
  variable
    Γ Δ Θ : Ctx
    Ξ Ξ'  : Lift Γ
    A B C : Ty Γ
    t u   : Tm Γ A
    σ τ γ : Sub Γ Δ

  _++_ : (Γ : Ctx) → Lift Γ → Ctx

  postulate
    [_]l_  : Sub Γ Δ → Lift Δ → Lift Γ 
    [_⇈_]_ : (σ : Sub Γ Δ) (Ξ : Lift Δ) (A : Ty (Δ ++ Ξ))
      → Ty (Γ ++ [ σ ]l Ξ)

  data _ where
    ∅
      : Ctx
    _,_
      : (Γ : Ctx) (A : Ty Γ)
      → Ctx
    ∅
      : Lift Γ
    _,_
      : (Ξ : Lift Γ)(A : Ty (Γ ++ Ξ)) → Lift Γ

  Γ ++ ∅       = Γ
  Γ ++ (Ξ , A) = Γ ++ Ξ , A

  postulate
    []l∅ : [ σ ]l ∅       ≡ ∅
    -- [TODO]: Making this a function cannot pass the local confluence check. Why?
    []l, : [ σ ]l (Ξ , A) ≡ [ σ ]l Ξ , [ σ ⇈ Ξ ] A
    {-# REWRITE []l∅ #-}

  [_]_ : (σ : Sub Γ Δ) (A : Ty Δ) → Ty Γ
  [ σ ] A = [ σ ⇈ ∅ ] A

  data _ where
    U
      : Ty Γ
    Π
      : (A : Ty Γ) → Ty (Γ , A)
      → Ty Γ
    El
      : Tm Γ U
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
    [_⇈_]tm_
      : {Γ Δ : Ctx} (σ : Sub Γ Δ) (Ξ : Lift Δ) {A : Ty (Δ ++ Ξ)}
      → Tm (Δ ++ Ξ)        A
      → Tm (Γ ++ [ σ ]l Ξ) ([ σ ⇈ Ξ ] A)
    abs
      : Tm (Γ , A) B → Tm Γ (Π A B)
    app
      : Tm Γ (Π A B) → Tm (Γ , A) B
  pattern wk   = π₁ idS
  pattern vz   = π₂ idS
  pattern vs x = [ wk ⇈ ∅ ]tm x

  [_]tm_
      : {Γ Δ : Ctx} (σ : Sub Γ Δ) {A : Ty Δ}
      → Tm Δ A
      → Tm Γ ([ σ ] A)
  [ σ ]tm u = [ σ ⇈ ∅ ]tm u

{-
  We'd like to define _[_] by overlapping patterns

  [ idS        ] A = A
  [ σ ⨟ τ      ] A = [ σ ] [ τ ] A
  [ π₁ (σ , t) ] A = [ σ ] A
  [ π₁ (τ ⨟ σ) ] A = [ π₁ τ ] [ σ ] A
  [ σ ] U          = U
  [ σ ] (Π A B)    = Π (A [ σ ]) (B [ σ ↑ A ])
  [ σ ] (El u)     = El ([ σ ]t u)
-}

  postulate
    [idS]l : [ idS        ]l Ξ ≡ Ξ
    [⨟]l   : [ σ ⨟ τ      ]l Ξ ≡ [ σ ]l [ τ ]l Ξ
    [π₁,]l : [ π₁ (σ , t) ]l Ξ ≡ [ σ ]l Ξ
    {-# REWRITE [idS]l [⨟]l [π₁,]l #-}
    [π₁⨟]l : [ π₁ (σ ⨟ τ) ]l Ξ ≡ [ σ ]l [ π₁ τ ]l Ξ
    {-# REWRITE [π₁⨟]l #-}

    [id]  : [ idS        ⇈ Ξ ] A ≡ A
    [⨟]   : [ σ ⨟ τ      ⇈ Ξ ] A ≡ [ σ ⇈ [ τ ]l Ξ ] [ τ ⇈ Ξ ] A
    [π₁,] : [ π₁ (σ , t) ⇈ Ξ ] A ≡ [ σ ⇈        Ξ ] A
    [π₁⨟] : [ π₁ (σ ⨟ τ) ⇈ Ξ ] A ≡ [ σ ⇈ [ π₁ τ ]l Ξ ] [ π₁ τ ⇈ Ξ ] A
    {-# REWRITE [id] [⨟] [π₁,] [π₁⨟] #-}
    {-# REWRITE []l, #-}

  [_⇈_]t_ : {Γ Δ : Ctx} (σ : Sub Γ Δ) (Ξ : Lift Δ) {A : Ty (Δ ++ Ξ)}
    → Tm (Δ ++ Ξ)        A
    → Tm (Γ ++ [ σ ]l Ξ) ([ σ ⇈ Ξ ] A)

  [_]t_
    : (σ : Sub Γ Δ) {A : Ty Δ}
    → Tm Δ A
    → Tm Γ ([ σ ] A)
  [ σ ]t t = [ σ ⇈ ∅ ]t t

  postulate
  -- Equality constructors for substitutions
    _⨟idS
      : (σ : Sub Γ Δ)
      → σ ⨟ idS ≡ σ
    idS⨟_
      : (σ : Sub Γ Δ)
      → idS ⨟ σ ≡ σ
    assocS
      :  σ ⨟ (τ ⨟ γ) ≡ (σ ⨟ τ) ⨟ γ
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
      : [ idS   ⇈ Ξ ]tm t ≡ t
    [⨟]tm
      : [ σ ⨟ τ ⇈ Ξ ]tm t ≡ [ σ ⇈ [ τ ]l Ξ ]tm [ τ ⇈ Ξ ]tm t
    π₂,
      : {σ : Sub Γ Δ}{A : Ty Δ}{t : Tm Γ ([ σ ] A)}
      →  π₂ (σ , t) ≡ t 

  [ idS        ⇈ Ξ ]t u = u
  [ σ ⨟ τ      ⇈ Ξ ]t u = [ σ ⇈ [ τ ]l Ξ ]t [ τ ⇈ Ξ ]t u
  [ π₁ (σ , t) ⇈ Ξ ]t u = [ σ ⇈ Ξ ]t u
  [ π₁ (σ ⨟ τ) ⇈ Ξ ]t u = [ σ ⇈ [ π₁ τ ]l Ξ ]t [ π₁ τ ⇈ Ξ ]t u
  {-# CATCHALL #-}
  [ σ          ⇈ Ξ ]t u = [ σ ⇈ Ξ ]tm u
{-
  postulate
    [id]t   : [ idS        ⇈ Ξ ]t u ≡ u
    [⨟]t    : [ σ ⨟ τ      ⇈ Ξ ]t u ≡ [ σ ⇈ [ τ ]l Ξ ]t [ τ ⇈ Ξ ]t u
    [π₁,]t  : [ π₁ (σ , t) ⇈ Ξ ]t u ≡ [ σ ⇈ Ξ ]t u
    [π₁⨟]t  : [ π₁ (σ ⨟ τ) ⇈ Ξ ]t u ≡ [ σ ⇈ [ π₁ τ ]l Ξ ]t [ π₁ τ ⇈ Ξ ]t u
    {-# REWRITE [id]t [⨟]t [π₁,]t [π₁⨟]t #-}
    [∅]t    : [ ∅ {Γ} ⇈ Ξ ]t u ≡ [ ∅ {Γ} ⇈ Ξ ]tm u
    [,]t    : [ σ , t ⇈ Ξ ]t u ≡ [ σ , t ⇈ Ξ ]tm u
    [π₁id]  : [ π₁ (idS {Γ , A}) ⇈ Ξ ]t u ≡ [ π₁ (idS {Γ , A}) ⇈ Ξ ]tm u
    [π₁π₁σ] : [ π₁ (π₁ σ) ⇈ Ξ ]t u ≡ [ π₁ (π₁ σ) ⇈ Ξ ]tm u
    {-# REWRITE [∅]t [,]t [π₁id] [π₁π₁σ] #-}
-}

  postulate
    U[]
      : [ σ ⇈ Ξ ] U ≡ U
    {-# REWRITE U[] #-}
    El[]
      : {Ξ : Lift Δ} (σ : Sub Γ Δ) (u : Tm (Δ ++ Ξ) U)
      → [ σ ⇈ Ξ ] (El u) ≡ El ([ σ ⇈ Ξ ]t u)
    {-# REWRITE El[] #-}
    Π[]
      : [ σ ⇈ Ξ ] Π A B ≡ Π ([ σ ⇈ Ξ ] A) ([ σ ⇈ Ξ , A ] B)
    {-# REWRITE Π[] #-}
    Πβ
      : app (abs t) ≡ t
    Πη
      : abs (app t) ≡ t
    []tabs
      : [ σ ⇈ Ξ ]t (abs t) ≡ abs ([ σ ⇈ Ξ , _ ]t t )

infixl 20 _↑_

_↑_
  : (σ : Sub Γ Δ) (A : Ty Δ)
  → Sub (Γ , [ σ ] A) (Δ , A)
σ ↑ A = π₁ idS ⨟ σ , vz

-- vs (vs ... (vs vz) ...) = π₂ idS [ π₁ idS ]tm .... [ π₁ idS ]tm
vz↦ : Tm Γ A → Sub Γ (Γ , A)
vz↦ t = idS , t
