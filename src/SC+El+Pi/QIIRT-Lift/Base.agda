module SC+El+Pi.QIIRT-Lift.Base where
 
open import Prelude
  hiding (_,_)

infixr 20 [_]l_
infixl 20 _↑_ _⇈S_
infixr 15 [_⇈_]_ [_]_ [_⇈_]t_ [_]t_ [_⇈_]tm_ [_]tm_
infixl 10 _⨟_
infixl 10 _++_
infixl 6 _,_

interleaved mutual
  data Ctx  : Set
  data Lift (Γ : Ctx) : Set
  data Ty   (Γ : Ctx) : Set
  data Sub  (Γ : Ctx) : Ctx → Set
  data Tm  : (Γ : Ctx) → Ty Γ → Set
  
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

  _↑_
    : (σ : Sub Γ Δ) (A : Ty Δ)
    → Sub (Γ , [ σ ] A) (Δ , A)
  σ ↑ A = π₁ idS ⨟ σ , vz

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

U-cong : Γ ≡ Δ → U {Γ} ≅ U {Δ}
U-cong refl = refl

_⇈S_
  : (σ : Sub Γ Δ) (Ξ : Lift Δ) → Sub (Γ ++ [ σ ]l Ξ) (Δ ++ Ξ)
[⇈S]=[⇈]
  : (σ : Sub Γ Δ) (Ξ : Lift Δ) (B : Ty (Δ ++ Ξ))
  → [ σ ⇈ Ξ ] B ≅  [ σ ⇈S Ξ ] B
[⇈S]tm=[⇈]tm
  : (σ : Sub Γ Δ) (Ξ : Lift Δ) (B : Ty (Δ ++ Ξ)) (u : Tm (Δ ++ Ξ) B)
  → tr (Tm (Γ ++ [ σ ]l Ξ)) (≅-to-≡ ([⇈S]=[⇈] σ Ξ B)) ([ σ ⇈ Ξ ]t u)
  ≅ [ σ ⇈S Ξ ]t u
  
-- we should find out what equality constructors are needed in the end of this proof
σ ⇈S ∅       = σ
σ ⇈S (Ξ , A) = tr (λ B → Sub (_ ++ [ σ ]l Ξ , B) (_ ++ Ξ , A))
  (sym $ ≅-to-≡ $ [⇈S]=[⇈] σ Ξ A) (σ ⇈S Ξ ↑ A)

[⇈S]=[⇈] σ ∅       B               = refl
[⇈S]=[⇈] {Γ} {Δ} σ (Ξ , A) U       = U-cong refl
[⇈S]=[⇈] {Γ} {Δ} σ (Ξ , A) (Π B C) = hcong₂ Π
  ([⇈S]=[⇈] σ (Ξ , A) B) {![⇈S]=[⇈] σ (Ξ , A , B) C!}
[⇈S]=[⇈] {Γ} {Δ} σ (Ξ , A) (El u)  = hcong El
  ([⇈S]tm=[⇈]tm σ (Ξ , A) U u)
  where open ≡-Reasoning

[⇈S]tm=[⇈]tm σ ∅       B u = refl
[⇈S]tm=[⇈]tm σ (Ξ , A) B u = {!!}
  
-- we no longer need another transportation for the following rule:
[]tapp : (σ : Sub Γ Δ) (Ξ : Lift Δ)
  → (A : Ty (Δ ++ Ξ)) (B : Ty (Δ ++ Ξ , A)) (t : Tm (Δ ++ Ξ) (Π A B))
  → app ([ σ ⇈ Ξ ]t t) ≡ [ σ ⇈ Ξ , A ]t (app t)
[]tapp σ Ξ A B t = begin
  app ([ σ ⇈ Ξ ]t t)                 ≡⟨ cong app (cong ([ σ ⇈ Ξ ]t_) (sym Πη)) ⟩
  app ([ σ ⇈ Ξ ]t (abs (app t)))     ≡⟨ cong app ([]tabs {σ = σ}) ⟩
  app (abs ([ σ ⇈ Ξ , A ]t (app t))) ≡⟨ Πβ ⟩
  [ σ ⇈ Ξ , A ]t (app t)             ∎
  where open ≡-Reasoning

-- derived computation rules on composition
π₁⨟ : (σ : Sub Γ Δ) (τ : Sub Δ (Θ , A)) → π₁ (σ ⨟ τ) ≡ σ ⨟ π₁ τ
π₁⨟ σ τ = begin
  π₁ (σ ⨟ τ)                    ≡⟨ cong (λ τ → π₁ (σ ⨟ τ)) η, ⟩
  π₁ (σ ⨟ (π₁ τ , π₂ τ))        ≡⟨ cong π₁ ⨟, ⟩ 
  π₁ (σ ⨟ π₁ τ , [ σ ]t π₂ τ)   ≡⟨ π₁, ⟩
  σ ⨟ π₁ τ                      ∎
  where open ≡-Reasoning

π₁idS⨟ : (σ : Sub Γ (Δ , A)) → σ ⨟ π₁ idS ≡ π₁ σ
π₁idS⨟ σ = begin
  σ ⨟ π₁ idS   ≡⟨ sym (π₁⨟ σ idS) ⟩
  π₁ (σ ⨟ idS) ≡⟨ cong π₁ (σ ⨟idS) ⟩
  π₁ σ         ∎
  where open ≡-Reasoning
  
π₂⨟ : (σ : Sub Γ Δ) (τ : Sub Δ (Θ , A))
  → π₂ (σ ⨟ τ) ≡ [ σ ]t (π₂ τ)
π₂⨟ {Γ} {Δ} {Θ} {A} σ τ = ≅-to-≡ $ begin
  π₂ (σ ⨟ τ)                      ≅⟨ hcong (λ ν → π₂ (σ ⨟ ν)) (≡-to-≅ η,) ⟩
  π₂ (σ ⨟ (π₁ τ , π₂ τ))          ≅⟨ hcong π₂ (≡-to-≅ ⨟,) ⟩
  π₂ ((σ ⨟ π₁ τ) , [ σ ]t (π₂ τ)) ≡⟨ π₂, ⟩
  [ σ ]t π₂ τ ∎
  where open ≅-Reasoning

-- vs (vs ... (vs vz) ...) = π₂ idS [ π₁ idS ]tm .... [ π₁ idS ]tm
vz:= : Tm Γ A → Sub Γ (Γ , A)
vz:= t = idS , t
