module SC+U+Pi+Id.QIIT.Syntax where
 
open import Prelude

-- infixl 20 _⁺
infixr 15 [_]_ [_]tm_
infixl 10 _⨟_
infixl 4 _,_

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

  data _ where
    ∅
      : Ctx
    _,_
      : (Γ : Ctx) (A : Ty Γ i)
      → Ctx
    [_]_
      : (σ : Sub Γ Δ) (A : Ty Δ i) → Ty Γ i
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
    [idS]   : [ idS        ] A ≡ A
    [⨟]     : [ σ ⨟ τ      ] A ≡ [ σ ] [ τ ] A

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

  _↑_ : (σ : Sub Γ Δ) (A : Ty Δ i) → Sub (Γ , [ σ ] A) (Δ , A)
  σ ↑ A = π₁ idS ⨟ σ , tr (Tm _) (sym [⨟]) (π₂ idS)

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
      : (σ ⨟ (τ , t)) ≡ (σ ⨟ τ , tr (Tm _) (sym [⨟]) ([ σ ]tm t))
    η∅
      : {σ : Sub Γ ∅}
      → σ ≡ ∅
    η,
      : {σ : Sub Γ (Δ , A)}
      → σ ≡ (π₁ σ , π₂ σ)
  -- Equality constructors for terms
    [idS]tm
      : tr (Tm Γ) [idS] ([ idS   ]tm t) ≡ t
    [⨟]tm
      : tr (Tm Γ) [⨟] ([ σ ⨟ τ ]tm t) ≡ [ σ ]tm [ τ ]tm t
    π₂,
      : {σ : Sub Γ Δ}{A : Ty Δ i}{t : Tm Γ ([ σ ] A)}
      →  tr (λ σ → Tm Γ ([ σ ] A)) π₁, (π₂ (σ , t)) ≡ t

  -- Structural rules for type formers
    []U
      : [ σ ] (U i) ≡ U i
    []El
      : (σ : Sub Γ Δ) (u : Tm Δ (U i))
      → [ σ ] (El u) ≡ El (tr (Tm Γ) []U ([ σ ]tm u))
    []Lift
      : [ σ ] (Lift A) ≡ Lift ([ σ ] A)
    []Π
      : [ σ ] Π A B ≡ Π ([ σ ] A) ([ σ ↑ A ] B)
    []Id
      : {σ : Sub Γ Δ} {a : Tm Δ (U i)} {t u : Tm Δ (El a)}
      → [ σ ] (Id a t u)
      ≡ Id (tr (Tm Γ) []U ([ σ ]tm a))
        (tr (Tm Γ) ([]El σ a) ([ σ ]tm t))
        (tr (Tm Γ) ([]El σ a) ([ σ ]tm u))

  -- Structural rules for term formers
    []tc
      : (σ : Sub Γ Δ) (A : Ty Δ i)
      → tr (Tm Γ) []U ([ σ ]tm (c A))
      ≡ c ([ σ ] A)
    []mk
      : (σ : Sub Γ Δ) (t : Tm Δ A)
      → tr (Tm Γ) []Lift ([ σ ]tm (mk t))
      ≡ mk ([ σ ]tm t) -- mk ([ σ ]tm t)
    []un
      : (σ : Sub Γ Δ) (A : Ty Δ i) (t : Tm Δ (Lift A))
      → [ σ ]tm un t ≡ un (tr (Tm Γ) []Lift $ [ σ ]tm t)
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
      : (σ : Sub Γ Δ) (t : Tm (Δ , A) B)
      → tr (Tm Γ) []Π ([ σ ]tm (ƛ t)) ≡ (ƛ ([ σ ↑ A ]tm t))
    Πβ
      : app (ƛ t) ≡ t
    Πη
      : ƛ (app t) ≡ t

TmFam : (A : Ty Γ i) → Set
TmFam = Tm _

TmFamₛ : {A : Ty Δ i} → Sub Γ Δ → Set
TmFamₛ {A = A} σ = Tm _ ([ σ ] A)