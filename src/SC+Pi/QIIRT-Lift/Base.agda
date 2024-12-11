-- inductive-inductive-recursive definition of context, type, term, and type substitution
{-# OPTIONS --local-confluence-check #-}

module SC+Pi.QIIRT-Lift.Base where
 
open import Prelude
  hiding (_,_)


infixl 35 _[_]l subTy subTm subTmR 
infixl 5 _,_

interleaved mutual
  data Ctx : Set
  data Lift : Ctx → Set
  data Ty  : Ctx → Set
  data Sub : Ctx → Ctx → Set
  data Tm  : (Γ : Ctx) → Ty Γ → Set
  _++_ : (Γ : Ctx) → Lift Γ → Ctx

  variable
      Γ Δ Θ Φ   : Ctx
      A B A' B' : Ty Γ
      t u       : Tm Γ A
      σ τ γ υ   : Sub Δ Γ
      As Bs     : Lift Γ

  postulate
    _[_]l : Lift Δ → Sub Γ Δ → Lift Γ
    subTy : (As : Lift Δ) (σ : Sub Γ Δ) (A : Ty (Δ ++ As))
      → Ty (Γ ++ As [ σ ]l)
  
  syntax subTy As σ A = A [ σ ⇈ As ]
  
  data _ where
    ∅
      : Ctx
    _,_
      : (Γ : Ctx) (A : Ty Γ)
      → Ctx
    ∅
      : Lift Γ
    _,_
      : (As : Lift Γ)(A : Ty (Γ ++ As)) → Lift Γ

  Γ ++ ∅        = Γ
  Γ ++ (As , A) = (Γ ++ As) , A

  postulate
    ∅[]l : ∅        [ σ ]l ≡ ∅
    ,[]l : (As , A) [ σ ]l ≡ As [ σ ]l , (A [ σ ⇈ As ])
    {-# REWRITE ∅[]l #-}

  data _ where
    U
      : Ty Γ
    Π
      : (A : Ty Γ) → Ty (Γ , A) → Ty Γ
    ∅
      : Sub Γ ∅
    _,_
      : {A : Ty Δ}
        (σ : Sub Γ Δ)(t : Tm Γ (A [ σ ⇈ ∅ ]))
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
      → Tm (Γ ++ ∅ [ π₁ σ ]l) (A [ π₁ σ ⇈ ∅ ])
    subTm
      : {Γ Δ : Ctx}(As : Lift Δ)(σ : Sub Γ Δ){A : Ty (Δ ++ As)}
      → Tm (Δ ++ As) A
      → Tm (Γ ++ As [ σ ]l) (A [ σ ⇈ As ])
    abs
      : Tm (Γ , A) B → Tm Γ (Π A B)
    app
      : Tm Γ (Π A B) → Tm (Γ , A) B
  
  pattern wk = π₁ idS
  pattern vz = π₂ idS
  pattern vs x = x [ wk ⇈ ∅ ]tm
  syntax subTm As σ t = t [ σ ⇈ As ]tm

{-
  We'd like to define _[_] by overlapping patterns

  A [ idS        ] = A
  A [ σ ∘ τ      ] = A [ σ ] [ τ ]
  A [ π₁ (σ , t) ] = A [ σ ]
  A [ π₁ (τ ∘ σ) ] = A [ π₁ τ ] [ σ ]
  U      [ σ ]     = U
  (El t) [ σ ]     = El (t [ σ ]tm) 
-}
  postulate
    [idS]l : As [ idS        ]l ≡ As
    [∘]l   : As [ σ ∘ τ      ]l ≡ As [ σ ]l [ τ ]l
    [π₁,]l : As [ π₁ (σ , t) ]l ≡ As [ σ ]l
    [π₁∘]l : As [ π₁ (τ ∘ σ) ]l ≡ As [ π₁ τ ]l [ σ ]l
    {-# REWRITE [idS]l [∘]l [π₁,]l [π₁∘]l #-}

    [id]
      : A [ idS ⇈ As ] ≡ A
    [∘]
      : A [ τ ∘ σ ⇈ As ] ≡ A [ τ ⇈ As ] [ σ ⇈ (As [ τ ]l) ]
    [π₁,]
      : A [ π₁ (σ , t) ⇈ As ] ≡ A [ σ ⇈ As ]
    [π₁∘]
      : A [ π₁ (τ ∘ σ) ⇈ As ] ≡ A [ π₁ τ ⇈ As ] [ σ ⇈ As [ π₁ τ ]l ]
    {-# REWRITE [id] [∘] [π₁,] [π₁∘] ,[]l #-}

  {-# TERMINATING #-}
  subTmR : (As : Lift Δ)(σ : Sub Γ Δ){A : Ty (Δ ++ As)} → Tm (Δ ++ As) A → Tm (Γ ++ As [ σ ]l) (A [ σ ⇈ As ])
  subTmR         As idS          t = t
  subTmR         As (τ ∘ σ)      t = subTmR (As [ τ ]l) σ (subTmR As τ t)
  subTmR {Γ = Γ} As ∅            t = subTm {Γ = Γ} As ∅ t
  subTmR         As (σ , u)      t = t [ (σ , u) ⇈ As ]tm
  subTmR         As (π₁ (τ ∘ σ)) t = subTmR (As [ π₁ τ ]l) σ (subTmR As (π₁ τ) t)
  subTmR         ∅  (π₁ (σ , u)) t = subTmR ∅ σ t
  {-# CATCHALL #-}
  subTmR         As (π₁ σ)       t = t [ π₁ σ ⇈ As ]tm

  syntax subTmR As σ t = t [ σ ⇈ As ]t

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
      -- : {Γ Δ : Ctx} {A : Ty Δ}
      -- → {σ : Sub Γ Δ} {t : Tm Γ (A [ σ ⇈ ∅ ])}
      :  π₂ (σ , t) ≡ t 
    ,∘
      : ((σ , t) ∘ τ) ≡ ((σ ∘ τ) , t [ τ ⇈ ∅ ]tm)
    η∅
      : {σ : Sub Γ ∅}
      → σ ≡ ∅
    η,
      : {Γ Δ : Ctx} {A : Ty Δ} {σ : Sub Γ (Δ , A)}
      → σ ≡ (π₁ σ , π₂ σ)

  postulate
    U[]  : U [ σ ⇈ As ] ≡ U

    U[∅] : U [ σ ⇈ ∅ ] ≡ U -- Why is this not an instance of U[∅]?
    {-# REWRITE U[] U[∅] #-}

    Π[]
      : (σ : Sub Γ Δ) → Π A B [ σ ⇈ As ] ≡ Π (A [ σ ⇈ As ]) (B [ σ ⇈ (As , A) ])
    Π[∅] -- why is this not an instance of Π[]?
      : (σ : Sub Γ Δ) → Π A B [ σ ⇈ ∅ ] ≡ Π (A [ σ ⇈ ∅ ]) (B [ σ ⇈ (∅ , A) ])
    {-# REWRITE Π[] Π[∅] #-}

-- derived computation rules on composition
π₁∘ : (σ : Sub Γ Δ) (τ : Sub Δ (Θ , A)) → π₁ (τ ∘ σ) ≡ π₁ τ ∘ σ
π₁∘ σ τ = begin
    π₁ (τ ∘ σ)                    ≡⟨ cong (λ σ' → π₁ (σ' ∘ σ)) η, ⟩
    π₁ ((π₁ τ , π₂ τ) ∘ σ)        ≡⟨ cong π₁ ,∘ ⟩ 
    π₁ (π₁ τ ∘ σ , (π₂ τ) [ σ ⇈ ∅ ]tm) ≡⟨ π₁, ⟩
    π₁ τ ∘ σ                      ∎
  where open ≡-Reasoning

{-# TERMINATING #-} -- the size of σ is decreasing
[]tm≡[]t : {Γ Δ : Ctx}(As : Lift Δ){A : Ty (Δ ++ As)}(t : Tm (Δ ++ As) A)(σ : Sub Γ Δ)
  → t [ σ ⇈ As ]tm ≡ t [ σ ⇈ As ]t 
[]tm≡[]t As t ∅       = refl
[]tm≡[]t As t (_ , _) = refl
[]tm≡[]t As t idS     = [id]tm
[]tm≡[]t ∅ t wk = refl
[]tm≡[]t (As , A) t wk = refl
[]tm≡[]t ∅ t (π₁ (τ ∘ σ)) = ≅-to-≡ $ begin
  t [ π₁ (τ ∘ σ) ⇈ ∅ ]tm       ≅⟨ HEq.cong (λ σ' → t [ σ' ⇈ ∅ ]tm) (≡-to-≅ (π₁∘ σ τ)) ⟩
  t [ π₁ τ ∘ σ ⇈ ∅ ]tm         ≡⟨ [∘]tm ⟩
  t [ π₁ τ ⇈ ∅ ]tm [ σ ⇈ ∅ ]tm ≡⟨ cong (λ t' → t' [ σ ⇈ ∅ ]tm) ([]tm≡[]t ∅ t (π₁ τ)) ⟩
  t [ π₁ τ ⇈ ∅ ]t [ σ ⇈ ∅ ]tm  ≡⟨ []tm≡[]t ∅ (t [ π₁ τ ⇈ ∅ ]t) σ ⟩
  t [ π₁ τ ⇈ ∅ ]t [ σ ⇈ ∅ ]t   ∎
  where open ≅-Reasoning
[]tm≡[]t As@(_ , _) t (π₁ (τ ∘ σ)) = ≅-to-≡ $ begin
  t [ π₁ (τ ∘ σ) ⇈ As ]tm                  ≅⟨ HEq.cong (λ σ' → t [ σ' ⇈ As ]tm) (≡-to-≅ (π₁∘ σ τ)) ⟩
  t [ π₁ τ ∘ σ ⇈ As ]tm                    ≡⟨ [∘]tm ⟩
  t [ π₁ τ ⇈ As ]tm [ σ ⇈ As [ π₁ τ ]l ]tm ≡⟨ cong (λ t' → t' [ σ ⇈ As [ π₁ τ ]l ]tm) ([]tm≡[]t As t (π₁ τ)) ⟩
  t [ π₁ τ ⇈ As ]t [ σ ⇈ As [ π₁ τ ]l ]tm  ≡⟨ []tm≡[]t (As [ π₁ τ ]l) (t [ π₁ τ ⇈ As ]t) σ ⟩
  t [ π₁ τ ⇈ As ]t [ σ ⇈ As [ π₁ τ ]l ]t   ∎
  where open ≅-Reasoning
[]tm≡[]t ∅ t (π₁ (π₁ σ)) = refl
[]tm≡[]t (As , A) t (π₁ (π₁ σ)) = refl
[]tm≡[]t ∅ t (τ ∘ σ) = begin
  t [ τ ∘ σ ⇈ ∅ ]tm                      ≡⟨ [∘]tm ⟩
  t [ τ ⇈ ∅ ]tm [ σ ⇈ ∅ ]tm              ≡⟨ cong (λ t' → t' [ σ ⇈ ∅ ]tm) ([]tm≡[]t ∅ t τ)  ⟩
  t [ τ ⇈ ∅ ]t [ σ ⇈ ∅ ]tm               ≡⟨ []tm≡[]t ∅ (t [ τ ⇈ ∅ ]t) σ ⟩
  t [ τ ⇈ ∅ ]t [ σ ⇈ ∅ ]t                ∎
  where open ≡-Reasoning
[]tm≡[]t As@(_ , _) t (τ ∘ σ) = begin
  t [ τ ∘ σ ⇈ As ]tm                     ≡⟨ [∘]tm ⟩
  t [ τ ⇈ As ]tm [ σ ⇈ As [ τ ]l ]tm     ≡⟨ cong (λ t' → t' [ σ ⇈ As [ τ ]l ]tm) ([]tm≡[]t As t τ)  ⟩
  t [ τ ⇈ As ]t [ σ ⇈ As [ τ ]l ]tm      ≡⟨ []tm≡[]t (As [ τ ]l) (t [ τ ⇈ As ]t) σ ⟩
  t [ τ ⇈ As ]t [ σ ⇈ As [ τ ]l ]t                ∎
  where open ≡-Reasoning
[]tm≡[]t ∅ t (π₁ (σ , u)) = ≅-to-≡ $ begin
  t [ π₁ (σ , u) ⇈ ∅ ]tm                 ≅⟨ HEq.cong (λ σ' → t [ σ' ⇈ ∅ ]tm) (≡-to-≅ π₁,) ⟩
  t [ σ ⇈ ∅ ]tm                          ≡⟨ []tm≡[]t ∅ t σ ⟩
  t [ σ ⇈ ∅ ]t                           ∎
  where open ≅-Reasoning
[]tm≡[]t As@(_ , _) t (π₁ (σ , u)) = refl

-- We will need to prove coherence for the following with another rewriting relation:
-- coherence of postulates

coh[idS∘]
  : {As : Lift Δ}{A : Ty (Δ ++ As)}{σ : Sub Γ Δ}
  → A [ idS ∘ σ ⇈ As ] ≡ A [ σ ⇈ As ]
coh[idS∘] = refl

coh[∘idS]
  : {As : Lift Δ}{A : Ty (Δ ++ As)}{σ : Sub Γ Δ}
  → A [ σ ∘ idS ⇈ As ] ≡ A [ σ ⇈ As ]
coh[∘idS] = refl

coh[assocS]
  : {As : Lift Φ}{A : Ty (Φ ++ As)}{γ : Sub Γ Δ}{τ : Sub Δ Θ}{σ : Sub Θ Φ}
  → A [ (σ ∘ τ) ∘ γ ⇈ As ] ≡ A [ σ ∘ (τ ∘ γ) ⇈ As ]
coh[assocS] = refl

coh[,∘]
  : {A' : Ty Θ}{As : Lift (Θ , A')}{A : Ty ((Θ , A') ++ As)}
    {σ : Sub Δ Θ}{t : Tm Δ (A' [ σ ⇈ ∅ ])}{τ : Sub Γ Δ}
  → A [ (σ , t) ∘ τ ⇈ As ] ≡ {! A [ (σ ∘ τ , t [ τ ⇈ ∅ ]tm) ⇈ As ]  !} -- A [ (σ , t) ∘ τ ⇈ As ] ≡ A [ (σ ∘ τ , t [ τ ⇈ ∅ ]tm) ⇈ As ]
coh[,∘] {A = U}     = {!   !}
coh[,∘] {A = Π A B} = {!   !} -- begin
  -- Π A B [ (σ , t) ] [ τ ]        ≡⟨ {!!} ⟩
  -- Π A B [ (σ ∘ τ) , t [ τ ]tm ]  ∎ 
  -- where open ≡-Reasoning

coh[βπ₁] : A [ π₁ (σ , t) ⇈ As ] ≡ A [ σ ⇈ As ]
coh[βπ₁] = refl

coh[βπ₂] : π₂ (σ , t) [ τ ⇈ As ]t ≡ t [ τ ⇈ As ]t
coh[βπ₂] {As = As} {σ = σ} {t = t} {τ = τ} = begin
  π₂ (σ , t) [ τ ⇈ As ]t         ≡⟨ sym ([]tm≡[]t _ _ _) ⟩
  π₂ (σ , t) [ τ ⇈ As ]tm        ≡⟨ cong (λ t' → t' [ τ ⇈ As ]tm) π₂, ⟩
  t [ τ ⇈ As ]tm                 ≡⟨ []tm≡[]t _ _ _ ⟩
  t [ τ ⇈ As ]t                  ∎
  where open ≡-Reasoning

coh[η,] 
  : {A' : Ty Δ}{As : Lift (Δ , A')}{A : Ty ((Δ , A') ++ As)}{σ : Sub Γ (Δ , A')}
  → A [ σ ⇈ As ] ≡ {!   !} -- A [ π₁ σ , π₂ σ ⇈ As ]
coh[η,] {A = U}     = {!   !}
coh[η,] {A = Π A B} = {!   !}

coh[η∅] : {As : Lift ∅}{σ : Sub Δ ∅} → (A : Ty (∅ ++ As)) → A [ σ ⇈ As ] ≡ {! subTy {∅} {Δ} As ∅ A  !} -- A [ ∅ ⇈ As ]l
coh[η∅] U              = {!   !}
coh[η∅] (Π A B)        = {!   !}

π₂∘ : (σ : Sub Γ Δ) (τ : Sub Δ (Θ , A))
  → π₂ (τ ∘ σ) ≡ π₂ τ [ σ ⇈ ∅ ]tm
π₂∘ {Γ} {Δ} {Θ} {A} σ τ = ≅-to-≡ $ begin
  π₂ (τ ∘ σ)                         ≅⟨ HEq.cong (λ ν → π₂ (ν ∘ σ)) (≡-to-≅ η,) ⟩
  π₂ ((π₁ τ , π₂ τ) ∘ σ)             ≅⟨ HEq.cong π₂ (≡-to-≅ ,∘) ⟩
  π₂ ((π₁ τ ∘ σ) , π₂ τ [ σ ⇈ ∅ ]tm) ≡⟨ π₂, ⟩
  π₂ τ [ σ ⇈ ∅ ]tm ∎
  where open ≅-Reasoning

-- vs (vs ... (vs vz) ...) = π₂ idS [ π₁ idS ]tm .... [ π₁ idS ]tm
vz:= : Tm Γ A → Sub Γ (Γ , A)
vz:= t = idS , t
