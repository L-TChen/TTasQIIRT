{-# OPTIONS --local-confluence-check #-}

module SC+Pi+Lift.Base where

open import Prelude
  hiding (_,_)


infixl 30 _[_]l subTy subTm -- subTmR 
infixl 5 _,_

interleaved mutual
  data Ctx : Set
  data Lift : Ctx → Set
  data Ty : (Γ : Ctx) → Lift Γ → Set
  data Sub : Ctx → Ctx → Set
  data Tm : (Γ : Ctx) (As : Lift Γ) → Ty Γ As → Set

--  _++_ : (Γ : Ctx) → Lift Γ → Ctx
  
  variable
      Γ Δ Θ Φ   : Ctx
      As Bs     : Lift Γ
      A B A' B' : Ty Γ As
      t u       : Tm Γ As A
      σ τ γ υ   : Sub Δ Γ

  data _ where
    ∅
      : Ctx
    _,_
      : (Γ : Ctx) {As : Lift Γ} (A : Ty Γ As)
      → Ctx
    ∅
      : Lift Γ
    _,_
      : (As : Lift Γ) (A : Ty Γ As) → Lift Γ
      
  postulate 
    _[_]l : Lift Δ → Sub Γ Δ → Lift Γ
    subTy : (As : Lift Δ) (σ : Sub Γ Δ) (A : Ty Δ As) → Ty Γ (As [ σ ]l)
  
  syntax subTy As σ A = A [ σ ⇈ As ]

  postulate
    ∅[]l : ∅        [ σ ]l ≡ ∅
    ,[]l : (As , A) [ σ ]l ≡ As [ σ ]l , subTy As σ A

  {-# REWRITE ∅[]l #-}

  data _ where
    U
      : Ty Γ As
    Π
      : (A : Ty Γ As) → Ty Γ (As , A) → Ty Γ As
    ∅
      : Sub Γ ∅
    _,_
      : {A : Ty Δ As}
        (σ : Sub Γ Δ)(t : Tm Γ (As [ σ ]l) (A [ σ ⇈ As ]))
      ----------------------------------------
      → Sub Γ (Δ , A) 
    idS
      : Sub Γ Γ
    _∘_
      : {Γ Δ Θ : Ctx}
      → (τ : Sub Δ Θ) (σ : Sub Γ Δ)
      → Sub Γ Θ
    π₁
      : (σ : Sub Γ (Δ , A))
      → Sub Γ Δ
    π₂
      : (σ : Sub Γ (Δ , A))
      → Tm Γ (As [ π₁ σ ]l) (A [ π₁ σ ⇈ As ])
    subTm
      : {Γ Δ : Ctx}(As : Lift Δ)(σ : Sub Γ Δ){A : Ty Δ As}
      → Tm Δ As A
      → Tm Γ (As [ σ ]l) (A [ σ ⇈ As ])
    abs
      : Tm Γ (As , A) B → Tm Γ As (Π A B)
    app
      : Tm Γ As (Π A B) → Tm Γ (As , A) B
  
  pattern wk = π₁ idS
  pattern vz = π₂ idS
  pattern vs x = x [ wk ⇈ ∅ ]tm
  syntax subTm As σ t = t [ σ ⇈ As ]tm

-- {-
--   We'd like to define _[_] by overlapping patterns

--   A [ idS        ] = A
--   A [ σ ∘ τ      ] = A [ σ ] [ τ ]
--   A [ π₁ (σ , t) ] = A [ σ ]
--   A [ π₁ (τ ∘ σ) ] = A [ π₁ τ ] [ σ ]
--   U      [ σ ]     = U
--   (El t) [ σ ]     = El (t [ σ ]tm) 
-- -}
  postulate
    [idS]l : As [ idS        ]l ≡ As
    [∘]l   : As [ σ ∘ τ      ]l ≡ As [ σ ]l [ τ ]l
    [π₁,]l : As [ π₁ (σ , t) ]l ≡ As [ σ ]l
    [π₁∘]l : As [ π₁ (τ ∘ σ) ]l ≡ As [ π₁ τ ]l [ σ ]l
    {-# REWRITE [idS]l [∘]l [π₁,]l [π₁∘]l #-}

    [id]
      : A [ idS ⇈ As ]        ≡ A
    [∘]
      : A [ τ ∘ σ ⇈ As ]      ≡ A [ τ ⇈ As ] [ σ ⇈ (As [ τ ]l) ]
    [π₁,]
      : A [ π₁ (σ , t) ⇈ As ] ≡ A [ σ ⇈ As ]
    [π₁∘]
      : A [ π₁ (τ ∘ σ) ⇈ As ] ≡ A [ π₁ τ ⇈ As ] [ σ ⇈ As [ π₁ τ ]l ]
    {-# REWRITE [id] [∘] [π₁,] [π₁∘] ,[]l #-}

  postulate
  -- Equality constructors for terms
    [id]tm : t [ idS ⇈ As   ]tm ≡ t
    [∘]tm  : t [ τ ∘ σ ⇈ As ]tm ≡ t [ τ ⇈ As ]tm [ σ ⇈ As [ τ ]l ]tm

  -- Equality constructors for substitutions
    idS∘_
      : (σ : Sub Γ Δ)
      → idS ∘ σ ≡ σ
    _∘idS
      : (σ : Sub Γ Δ)
      → σ ∘ idS ≡ σ
    assocS
      : (υ ∘ τ) ∘ σ ≡ υ ∘ (τ ∘ σ)
    π₁,
      : π₁ (σ , t) ≡ σ
    π₂,
      :  π₂ (σ , t) ≡ t 
    ,∘
      : {Γ Δ Θ : Ctx} {τ : Sub Γ Δ}
      → {As : Lift Θ} {A : Ty Θ As} {σ : Sub Δ Θ} {t : Tm Δ (As [ σ ]l) (A [ σ ⇈ As ])}
      → ((σ , t) ∘ τ) ≡ ((σ ∘ τ) , t [ τ ⇈ As [ σ ]l ]tm)
    η∅
      : {σ : Sub Γ ∅}
      → σ ≡ ∅
    η,
      : {Γ Δ : Ctx} {As : Lift Δ} {A : Ty Δ As} {σ : Sub Γ (Δ , A)}
      → σ ≡ (π₁ σ , π₂ σ)

  postulate
    U[]
      : (σ : Sub Γ Δ) → U [ σ ⇈ As ] ≡ U
    Π[]
      : (σ : Sub Γ Δ) → Π A B [ σ ⇈ As ] ≡ Π (A [ σ ⇈ As ]) (B [ σ ⇈ (As , A) ])
    {-# REWRITE U[] Π[] #-}

  U[∅] : U [ σ ⇈ ∅ ] ≡ U
  U[∅] = refl

  U[,] : U [ σ ⇈ As , A ] ≡ U
  U[,] = refl -- U[] {Γ} {Δ} {σ}

  Π[∅] : Π A B [ σ ⇈ ∅ ] ≡ Π (A [ σ ⇈ ∅ ]) (B [ σ ⇈ (∅ , A) ])
  Π[∅] = refl -- Π[]  

  Π[,] : Π A B [ σ ⇈ As ] ≡ Π (A [ σ ⇈ As ]) (B [ σ ⇈ As , A ])
  Π[,] = refl -- Π[]

-- derived computation rules on composition
π₁∘ : (σ : Sub Γ Δ) (τ : Sub Δ (Θ , A)) → π₁ (τ ∘ σ) ≡ π₁ τ ∘ σ
π₁∘ σ τ = begin
    π₁ (τ ∘ σ)                         ≡⟨ cong (λ σ' → π₁ (σ' ∘ σ)) η, ⟩
    π₁ ((π₁ τ , π₂ τ) ∘ σ)             ≡⟨ cong π₁ ,∘ ⟩ 
    π₁ (π₁ τ ∘ σ , (π₂ τ) [ σ ⇈ _ ]tm) ≡⟨ π₁, ⟩
    π₁ τ ∘ σ                           ∎
  where open ≡-Reasoning

-- We will need to prove coherence for the following with another rewriting relation:
-- coherence of postulates

coh[idS∘]
  : {As : Lift Δ}{A : Ty Δ As}{σ : Sub Γ Δ}
  → A [ idS ∘ σ ⇈ As ] ≡ A [ σ ⇈ As ]
coh[idS∘] = refl

coh[∘idS]
  : {As : Lift Δ}{A : Ty Δ As}{σ : Sub Γ Δ}
  → A [ σ ∘ idS ⇈ As ] ≡ A [ σ ⇈ As ]
coh[∘idS] = refl

coh[assocS]
  : {As : Lift Φ}{A : Ty Φ As}{γ : Sub Γ Δ}{τ : Sub Δ Θ}{σ : Sub Θ Φ}
  → A [ (σ ∘ τ) ∘ γ ⇈ As ] ≡ A [ σ ∘ (τ ∘ γ) ⇈ As ]
coh[assocS] = refl

coh[,∘]
  : {Γ Δ Θ : Ctx} {τ : Sub Γ Δ} {σ : Sub Δ Θ}
  → {As : Lift Θ} {A : Ty Θ As} {t : Tm Δ (As [ σ ]l) (A [ σ ⇈ As ])}
  → {Bs : Lift (Θ , A)} {B : Ty (Θ , A) Bs}
  → B [ (σ , t) ∘ τ ⇈ Bs ] ≡ {! {!B!} [ σ ∘ τ , t [ τ ⇈ As [ σ ]l ]tm ⇈ Bs ] !} 
coh[,∘] = {!!}
  -- Π A B [ (σ , t) ] [ τ ]        ≡⟨ {!!} ⟩
  -- Π A B [ (σ ∘ τ) , t [ τ ]tm ]  ∎ 
  -- where open ≡-Reasoning

coh[π₁,] : A [ π₁ (σ , t) ⇈ As ] ≡ A [ σ ⇈ As ]
coh[π₁,] = refl

coh[η,] 
  -- : {Γ Δ : Ctx} {As : Lift Δ} {A : Ty Δ As} {σ : Sub Γ (Δ , A)}
  --     → σ ≡ (π₁ σ , π₂ σ)
  : {Γ Δ : Ctx} {As : Lift Δ} {A : Ty Δ As} {σ : Sub Γ (Δ , A)}
  → (Bs : Lift {!!}) (B : Ty {!!} Bs)
  → B [ σ ⇈ Bs ] ≡ {! B [ (π₁ σ , π₂ σ) ⇈ Bs ] !}
coh[η,] = {!   !}
coh[η,] = {!   !}

coh[η∅] : {As : Lift ∅}{σ : Sub Δ ∅} → (A : Ty ∅ As) → A [ σ ⇈ As ] ≡ {! subTy {∅} {Δ} As ∅ A  !} -- A [ ∅ ⇈ As ]l
coh[η∅] U              = {!   !}
coh[η∅] (Π A B)        = {!   !}

π₂∘ : (σ : Sub Γ Δ) {A : Ty Θ As} (τ : Sub Δ (Θ , A))
  → π₂ (τ ∘ σ) ≡ π₂ τ [ σ ⇈ As [ π₁ τ ]l ]tm -- π₂ τ [ σ ⇈ ∅ ]tm
π₂∘ {Γ} {Δ} {Θ} {A} σ τ = {!!}
{- ≅-to-≡ $ begin
  π₂ (τ ∘ σ)                         ≅⟨ HEq.cong (λ ν → π₂ (ν ∘ σ)) (≡-to-≅ η,) ⟩
  π₂ ((π₁ τ , π₂ τ) ∘ σ)             ≅⟨ HEq.cong π₂ (≡-to-≅ ,∘) ⟩
  π₂ ((π₁ τ ∘ σ) , π₂ τ [ σ ⇈ ∅ ]tm) ≡⟨ π₂, ⟩
  π₂ τ [ σ ⇈ ∅ ]tm ∎
  where open ≅-Reasoning
-}

-- vs (vs ... (vs vz) ...) = π₂ idS [ π₁ idS ]tm .... [ π₁ idS ]tm
vz:= : Tm Γ As A → Sub Γ (Γ , A)
vz:= t = idS , t
