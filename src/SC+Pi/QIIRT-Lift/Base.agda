-- inductive-inductive-recursive definition of context, type, term, and type substitution
--{-# OPTIONS --confluence-check #-}
-- {-# OPTIONS --local-confluence-check --with-K #-}

module SC+Pi.QIIRT-Lift.Base where
 
open import Prelude
  hiding (_,_)


infixl 35 _[_]l _[_] _[_]tm _[_]t 
infixl 5 _,_

interleaved mutual
  data Ctx : Set
  data Lift : Ctx → Set
  data Ty  : Ctx → Set
  data Sub : Ctx → Ctx → Set
  data Tm  : (Γ : Ctx) → Ty Γ → Set
  _++_ : (Γ : Ctx) → Lift Γ → Ctx

  variable
      Γ Δ Θ     : Ctx
      A B A' B' : Ty Γ
      t u       : Tm Γ A
      σ τ γ υ σ' τ' : Sub Δ Γ
      As Bs : Lift Γ

  postulate
    _[_]l  : {Γ Δ : Ctx} → Lift Δ → Sub Γ Δ → Lift Γ
    subTy : (As : Lift Δ)(σ : Sub Γ Δ) → Ty (Δ ++ As) → Ty (Γ ++ As [ σ ]l)
  
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

  Γ ++ ∅ = Γ
  Γ ++ (As , A) = (Γ ++ As) , A

  postulate
    ∅[]l : ∅ [ σ ]l ≡ ∅
    ,[]l : {As : Lift Δ}{A : Ty (Δ ++ As)}{σ : Sub Γ Δ} → (As , A) [ σ ]l ≡ As [ σ ]l , (A [ σ ⇈ As ])
    {-# REWRITE ∅[]l ,[]l #-}

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
      → Tm (Δ ++ As) A → Tm (Γ ++ As [ σ ]l) (A [ σ ⇈ As ])
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
    [idS]l : As [ idS ]l ≡ As
    [∘]l : As [ σ ∘ τ ]l ≡ As [ σ ]l [ τ ]l
    [π₁,]l : As [ π₁ (σ , t) ]l ≡ As [ σ ]l
    [π₁∘]l : As [ π₁ (τ ∘ σ) ]l ≡ As [ π₁ τ ]l [ σ ]l
    {-# REWRITE [idS]l [∘]l [π₁,]l [π₁∘]l #-}
  
  postulate
    [id]
      : {A : Ty (Γ ++ As)}
      → A [ idS ⇈ As ] ≡ A
    [∘]
      : {A : Ty (Θ ++ As)}{σ : Sub Γ Δ}{τ : Sub Δ Θ}
      → A [ τ ∘ σ ⇈ As ] ≡ A [ τ ⇈ As ] [ σ ⇈ (As [ τ ]l) ]
    [π₁,]
      : {A' : Ty Δ}{σ : Sub Γ Δ}{t : Tm Γ (A' [ σ ⇈ ∅ ])}
        {As : Lift Δ}{A : Ty (Δ ++ As)}
      → A [ π₁ (σ , t) ⇈ As ] ≡ A [ σ ⇈ As ]
    [π₁∘]
      : {As : Lift Θ}{A' : Ty Θ}{σ : Sub Γ Δ}{τ : Sub Δ (Θ , A')}{A : Ty (Θ ++ As)}
      → A [ π₁ (τ ∘ σ) ⇈ As ] ≡ A [ π₁ τ ⇈ As ] [ σ ⇈ As [ π₁ τ ]l ]
    {-# REWRITE [id] [∘] [π₁,] [π₁∘] #-}

  -- _↑_ : (σ : Sub Γ Δ) (A : Ty Δ) → Sub (Γ , A [ σ ]) (Δ , A)
  -- _↑_ σ A = _↑_ {A = A} (σ ∘ wk) vz
  {-# TERMINATING #-}
  subTmR : (As : Lift Δ)(σ : Sub Γ Δ){A : Ty (Δ ++ As)} → Tm (Δ ++ As) A → Tm (Γ ++ As [ σ ]l) (A [ σ ⇈ As ])
  subTmR As idS t = t
  subTmR As (τ ∘ σ) t = subTmR (As [ τ ]l) σ (subTmR As τ t)
  subTmR {Γ = Γ} As ∅ t = subTm {Γ = Γ} As ∅ t
  subTmR As (σ , u) t = t [ (σ , u) ⇈ As ]tm
  subTmR ∅ (π₁ (σ , u)) t = subTmR ∅ σ t
  subTmR As (π₁ (τ ∘ σ)) t = subTmR (As [ π₁ τ ]l) σ (subTmR As (π₁ τ) t)
  {-# CATCHALL #-}
  subTmR As (π₁ σ) t = t [ π₁ σ ⇈ As ]tm

  syntax subTmR As σ t = t [ σ ⇈ As ]t

  postulate
  -- Equality constructors for terms
    [id]tm : t [ idS ⇈ As ]tm ≡ t
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
      : {σ : Sub Γ Δ} {t : Tm Γ (A [ σ ⇈ ∅ ])}
      → π₁ (σ , t) ≡ σ
    π₂,
      : {Γ Δ : Ctx} {A : Ty Δ}
      → {σ : Sub Γ Δ} {t : Tm Γ (A [ σ ⇈ ∅ ])}
      →  π₂ (σ , t) ≡ t 
    ,∘
      : ((σ , t) ∘ τ) ≡ ((σ ∘ τ) , t [ τ ⇈ ∅ ]tm)
    η∅
      : {σ : Sub Γ ∅}
      → σ ≡ ∅
    η,
      : {Γ Δ : Ctx} {A : Ty Δ} {σ : Sub Γ (Δ , A)}
      → σ ≡ (π₁ σ , π₂ σ)

  -- idS↑A≡idS
  --   : {A : Ty Γ}
  --   → idS ↑ A ≡ idS
  -- idS↑A≡idS {Γ} {A} = ≅-to-≡ $ begin
  --   idS ∘ wk , π₂ idS   ≅⟨ HEq.cong₂ {C = λ (σ : Sub (Γ , A) Γ) (t : Tm (Γ , A) (A [ σ ])) → Sub (Γ , A) (Γ , A)} _,_ (≡-to-≅ (idS∘ _)) refl ⟩
  --   π₁ idS , π₂ idS     ≡⟨ sym (η, {A = A}) ⟩
  --   idS                 ∎
  --   where open ≅-Reasoning
  
  -- [id↑A] : A [ idS ↑ B ] ≡ A
  -- [id↑A] {B = B} {A = A} = begin
  --   A [ idS ↑ B ] ≡⟨ cong (A [_]) idS↑A≡idS ⟩
  --   A [ idS ]     ≡⟨⟩
  --   A             ∎
  --   where open ≡-Reasoning

--  {-# REWRITE [id↑A] #-}
--  postulate
--    [id↑A]t
--      : (t : Tm (Γ , A) B)
--      → (t [ idS ↑ A ]t) ≡ t

--  {-# REWRITE [id↑A]t #-}

  postulate
    U[]   : U [ σ ⇈ As ] ≡ U
-- [TODO] Figure out why the triangle property cannot be satisfied:    
--    U[∘]  : U [ τ ∘ σ ] ≡ U
--    U[π,] : U [ π₁ (σ , t) ] ≡ U
--    U[π∘] : U [ π₁ (τ ∘ σ) ] ≡ U
--    U[][] : U [ idS ] [ σ ] ≡ U
--    U[π∘][] : U [ π₁ (τ ∘ σ) ] [ σ ] ≡ U
--    U[π][] : U [ π₁ τ ] [ σ ] ≡ U
--    {-# REWRITE U[∘] U[] U[π,] U[π∘] U[][] U[π∘][] U[π][] #-}
    {-# REWRITE U[] #-}

    Π[]
      : {As : Lift Δ}{A : Ty (Δ ++ As)}{B : Ty ((Δ ++ As) , A)}
      → (σ : Sub Γ Δ) → Π A B [ σ ⇈ As ] ≡ Π (A [ σ ⇈ As ]) (B [ σ ⇈ (As , A) ])
    {-# REWRITE Π[] #-}

-- derived computation rules on composition
π₁∘ : (σ : Sub Γ Δ) (τ : Sub Δ (Θ , A)) → π₁ (τ ∘ σ) ≡ π₁ τ ∘ σ
π₁∘ σ τ = begin
    π₁ (τ ∘ σ)                    ≡⟨ cong (λ σ' → π₁ (σ' ∘ σ)) η, ⟩
    π₁ ((π₁ τ , π₂ τ) ∘ σ)        ≡⟨ cong π₁ ,∘ ⟩ 
    π₁ (π₁ τ ∘ σ , (π₂ τ) [ σ ⇈ ∅ ]tm) ≡⟨ π₁, ⟩
    π₁ τ ∘ σ                      ∎
  where open ≡-Reasoning
{-
{-# TERMINATING #-} -- the size of σ is decreasing
[]tm≡[]t : {Γ Δ : Ctx} {A : Ty Δ} (t : Tm Δ A) (σ : Sub Γ Δ) → t [ σ ]tm ≡ t [ σ ]t 
[]tm≡[]t t ∅       = refl
[]tm≡[]t t (_ , _) = refl
[]tm≡[]t t idS     = [id]tm
[]tm≡[]t t (π₁ idS)     = refl
[]tm≡[]t t (π₁ (τ ∘ σ)) = ≅-to-≡ $ begin
  t [ π₁ (τ ∘ σ) ]tm                                       ≅⟨ HEq.cong (t [_]tm) (≡-to-≅ (π₁∘ σ τ)) ⟩
  t [ π₁ τ ∘ σ ]tm                                         ≡⟨ [∘]tm ⟩
  t [ π₁ τ ]tm [ σ ]tm                                     ≡⟨ cong (_[ σ ]tm) ([]tm≡[]t t (π₁ τ)) ⟩
  t [ π₁ τ ]t [ σ ]tm                                      ≡⟨ []tm≡[]t (t [ π₁ τ ]t) σ ⟩
  t [ π₁ τ ]t [ σ ]t                                       ∎
  where open ≅-Reasoning
[]tm≡[]t t (π₁ (π₁ σ))  = refl
[]tm≡[]t t (τ ∘ σ) = begin
  t [ τ ∘ σ ]tm                                            ≡⟨ [∘]tm ⟩
  t [ τ ]tm [ σ ]tm                                        ≡⟨ cong (_[ σ ]tm) ([]tm≡[]t t τ)  ⟩
  t [ τ ]t [ σ ]tm                                         ≡⟨ []tm≡[]t (t [ τ ]t) σ ⟩
  t [ τ ]t [ σ ]t                                          ∎
  where open ≡-Reasoning
[]tm≡[]t t (π₁ (σ , u)) = ≅-to-≡ $ begin
  t [ π₁ (σ , u) ]tm                                       ≅⟨ HEq.cong (t [_]tm) (≡-to-≅ π₁,) ⟩
  t [ σ ]tm                                                ≡⟨ []tm≡[]t t σ ⟩
  t [ σ ]t                                                 ∎
  where open ≅-Reasoning

-- We will need to prove coherence for the following with another rewriting relation:
-- coherence of postulates

coh[idS∘] : A [ idS ∘ σ ] ≡ A [ σ ]
coh[idS∘] = refl

coh[∘idS] : A [ σ ∘ idS ] ≡ A [ σ ]
coh[∘idS] = refl

coh[assocS] : A [ (σ ∘ τ) ∘ γ ] ≡ A [ σ ∘ (τ ∘ γ) ]
coh[assocS] = refl

coh[,∘] : A [ (σ , t) ∘ τ ] ≡ A [ σ ∘ τ , t [ τ ]tm ]
coh[,∘] {A = U}     = refl
coh[,∘] {A = Π A B} {_} {σ} {t} {_} {τ} = begin
  Π A B [ (σ , t) ] [ τ ]        ≡⟨ {!!} ⟩
  Π A B [ (σ ∘ τ) , t [ τ ]tm ]  ∎ 
  where open ≡-Reasoning

coh[βπ₁] : A [ π₁ (σ , t) ] ≡ A [ σ ]
coh[βπ₁] = refl

coh[βπ₂] : π₂ (σ , t) [ τ ]t ≡ t [ τ ]t
coh[βπ₂] {σ = σ} {t = t} {τ = τ} = begin
  π₂ (σ , t) [ τ ]t         ≡⟨ sym ([]tm≡[]t _ _) ⟩
  π₂ (σ , t) [ τ ]tm        ≡⟨ cong (_[ τ ]tm) π₂, ⟩
  t [ τ ]tm                 ≡⟨ []tm≡[]t _ _ ⟩
  t [ τ ]t                  ∎
  where open ≡-Reasoning

coh[η,] : A [ σ ] ≡ A [ π₁ σ , π₂ σ ]
coh[η,] {A = U}     = refl
coh[η,] {A = Π A B} = {!!}

coh[η∅] : {σ : Sub Δ ∅} → (A : Ty ∅) → A [ σ ] ≡ A [ ∅ ]
coh[η∅] U              = refl
coh[η∅] (Π A B)        = {!!}

π₂∘ : (σ : Sub Γ Δ) (τ : Sub Δ (Θ , A))
  → π₂ (τ ∘ σ) ≡ π₂ τ [ σ ]tm
π₂∘ {Γ} {Δ} {Θ} {A} σ τ = ≅-to-≡ $ begin
  π₂ (τ ∘ σ)                         ≅⟨ HEq.cong (λ ν → π₂ (ν ∘ σ)) (≡-to-≅ η,) ⟩
  π₂ (((π₁ τ) , (π₂ τ)) ∘ σ)         ≅⟨ HEq.cong π₂ (≡-to-≅ ,∘) ⟩
  π₂ (((π₁ τ ∘ σ) , (π₂ τ [ σ ]tm))) ≡⟨ π₂, ⟩
  π₂ τ  [ σ ]tm ∎
  where open ≅-Reasoning

-- vs (vs ... (vs vz) ...) = π₂ idS [ π₁ idS ]tm .... [ π₁ idS ]tm

vz:= : Tm Γ A → Sub Γ (Γ , A)
vz:= t = idS , t
-}     