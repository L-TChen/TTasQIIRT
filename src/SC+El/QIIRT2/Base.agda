-- inductive-inductive-recursive definition of context, type, term, and type substitution
--{-# OPTIONS --confluence-check #-}

module SC+El.QIIRT2.Base where
 
open import Prelude
  hiding (_,_)


infixl 35 _[_] _[_]t _[_]tm
infixl 10 _,_

interleaved mutual
  data Ctx : Set
  data Ty  (Γ : Ctx) : Set
  data Sub (Γ : Ctx) : Ctx → Set
  data Tm  : (Γ : Ctx) → Ty Γ → Set

  variable
      Γ Δ Θ     : Ctx
      A B A' B' : Ty Γ
      t u       : Tm Γ A
      σ τ γ υ σ' τ' : Sub Δ Γ

  postulate
    _[_]  : Ty Γ → Sub Δ Γ → Ty Δ
  
  data _ where
    ∅
      : Ctx
    _,_
      : (Γ : Ctx) (A : Ty Γ)
      → Ctx
    ∅
      ---------
      : Sub Γ ∅
    _,_
      : (σ : Sub Γ Δ) (t : Tm Γ (A [ σ ]))
      ------------------------------------
      → Sub Γ (Δ , A)
    idS
      : Sub Γ Γ
    _∘_
      : {Δ Θ : Ctx}
      → (τ : Sub Δ Θ) (σ : Sub Γ Δ)
      → Sub Γ Θ
    π₁
      : (σ : Sub Γ (Δ , A))
      → Sub Γ Δ
    π₂
      : (σ : Sub Γ (Δ , A))
      → Tm Γ (A [ π₁ σ ])
    _[_]tm
      : {Γ Δ : Ctx} {A : Ty Δ}
      → Tm Δ A → (σ : Sub Γ Δ)
      → Tm Γ (A [ σ ])
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
    [id]  : A [ idS ]        ≡ A
    [∘]   : A [ τ ∘ σ ]      ≡ A [ τ ] [ σ ]
    [π₁,] : A [ π₁ (σ , t) ] ≡ A [ σ ]
    [π₁∘] : A [ π₁ (τ ∘ σ) ] ≡ A [ π₁ τ ] [ σ ]
    {-# REWRITE [id] [∘] [π₁,] [π₁∘] #-}

  {-# TERMINATING #-}
  _[_]t : Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ])
  t [ idS        ]t = t
  t [ τ ∘ σ      ]t = t [ τ ]t [ σ ]t
  t [ ∅          ]t = t [ ∅ ]tm
  t [ σ , u      ]t = t [ σ , u ]tm
  t [ π₁ (σ , u) ]t = t [ σ ]t
  t [ π₁ (τ ∘ σ) ]t = t [ π₁ τ ]t [ σ ]t
  {-# CATCHALL #-}
  t [ π₁ σ       ]t = t [ π₁ σ ]tm
    
  postulate
    [id]tm : t [ idS   ]tm ≡ t
    [∘]tm  : t [ τ ∘ σ ]tm ≡ t [ τ ]tm [ σ ]tm

  postulate
-- Equality constructors
    idS∘_
      : (σ : Sub Γ Δ)
      → idS ∘ σ ≡ σ
    _∘idS
      : (σ : Sub Γ Δ)
      → σ ∘ idS ≡ σ
    assocS
      : (υ ∘ τ) ∘ σ ≡ υ ∘ (τ ∘ σ)
    π₁,
      : {σ : Sub Γ Δ} {t : Tm Γ (A [ σ ])}
      → π₁ (σ , t) ≡ σ
    π₂,
      : {Γ Δ : Ctx} {A : Ty Δ}
      → {σ : Sub Γ Δ} {t : Tm Γ (A [ σ ])}
      →  π₂ (σ , t) ≡ t 
    ,∘
      : ((σ , t) ∘ τ) ≡ ((σ ∘ τ) , t [ τ ]t)
    η∅
      : {σ : Sub Γ ∅}
      → σ ≡ ∅
    η,
      : σ ≡ (π₁ σ , π₂ σ)

  data _ where
    U
      : Ty Γ
    El
      : Tm Γ U → Ty Γ
      
  postulate
    U[]   : U [ σ ] ≡ U
-- [TODO] Figure out why the triangle property cannot be satisfied:    
--    U[∘]  : U [ τ ∘ σ ] ≡ U
--    U[π,] : U [ π₁ (σ , t) ] ≡ U
--    U[π∘] : U [ π₁ (τ ∘ σ) ] ≡ U
--    U[][] : U [ idS ] [ σ ] ≡ U
--    U[π∘][] : U [ π₁ (τ ∘ σ) ] [ σ ] ≡ U
--    U[π][] : U [ π₁ τ ] [ σ ] ≡ U
--    {-# REWRITE U[∘] U[] U[π,] U[π∘] U[][] U[π∘][] U[π][] #-}
    {-# REWRITE U[] #-}

    El[] : (σ : Sub Γ Δ) → (El t) [ σ ] ≡ El (t [ σ ]t)
    {-# REWRITE El[] #-}

-- derived computation rules on composition
π₁∘ : (σ : Sub Γ Δ) (τ : Sub Δ (Θ , A)) → π₁ (τ ∘ σ) ≡ π₁ τ ∘ σ
π₁∘ σ τ = begin
    π₁ (τ ∘ σ)                    ≡⟨ cong (λ σ' → π₁ (σ' ∘ σ)) η, ⟩
    π₁ ((π₁ τ , π₂ τ) ∘ σ)        ≡⟨ cong π₁ ,∘ ⟩ 
    π₁ (π₁ τ ∘ σ , (π₂ τ) [ σ ]t) ≡⟨ π₁, ⟩
    π₁ τ ∘ σ                      ∎
  where open ≡-Reasoning

π₁idS∘ : {A : Ty Γ}(σ : Sub Δ (Γ , A)) → π₁ idS ∘ σ ≡ π₁ σ
π₁idS∘ σ = begin
  π₁ idS ∘ σ      ≡⟨ sym (π₁∘ σ idS) ⟩
  π₁ (idS ∘ σ)    ≡⟨ cong π₁ (idS∘ σ) ⟩
  π₁ σ            ∎
  where open ≡-Reasoning

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

coh[,∘] : A [ (σ , t) ∘ τ ] ≡ A [ σ ∘ τ , t [ τ ]t ]
coh[,∘] {A = U}     = refl
coh[,∘] {A = El u} {σ = σ} {t = t} {τ = τ} = cong El $ begin
  u [ σ , t ]tm [ τ ]t       ≡⟨ sym ([]tm≡[]t (u [ σ , t ]tm) τ) ⟩
  u [ σ , t ]tm [ τ ]tm      ≡⟨ sym ([∘]tm) ⟩
  u [ (σ , t) ∘ τ ]tm        ≡⟨ cong (u [_]tm) ,∘ ⟩
  u [ (σ ∘ τ) , t [ τ ]t ]tm ∎
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
coh[η,] {A = U}    {σ} = refl
coh[η,] {A = El t} {σ = σ} = cong El $ begin
  t [ σ ]t                  ≡⟨ sym ([]tm≡[]t t σ) ⟩
  t [ σ ]tm                 ≡⟨ cong (t [_]tm) η, ⟩
  t [ π₁ σ , π₂ σ ]tm       ∎ 
  where open ≡-Reasoning

coh[η∅] : A [ σ ] ≡ A [ ∅ ]
coh[η∅] {A = U}            = refl
coh[η∅] {A = El t} {σ = σ} = cong El $ begin
  t [ σ ]t                  ≡⟨ sym ([]tm≡[]t t σ) ⟩
  t [ σ ]tm                 ≡⟨ cong (t [_]tm) η∅ ⟩
  t [ ∅ ]tm                 ∎
  where open ≡-Reasoning

π₂∘ : (σ : Sub Γ Δ) (τ : Sub Δ (Θ , A))
  → π₂ (τ ∘ σ) ≡ π₂ τ [ σ ]tm
π₂∘ {Γ} {Δ} {Θ} {A} σ τ = ≅-to-≡ $ begin
  π₂ (τ ∘ σ)                         ≅⟨ HEq.cong (λ ν → π₂ (ν ∘ σ)) (≡-to-≅ η,) ⟩
  -- cong {_} {Sub Δ (Γ , A)} {_} {Tm Θ (A [ π₁ σ ] [ τ ])}
  --   : (f : Sub Δ (Γ , A) → Tm Θ (A [ π₁ σ ] [ τ ])) {x y : Sub Δ (Γ , A)} → x Eq.≡ y → f x Eq.≡ f y
  π₂ (((π₁ τ) , (π₂ τ)) ∘ σ)         ≅⟨ HEq.cong π₂ (≡-to-≅ ,∘) ⟩
  π₂ (((π₁ τ ∘ σ) , (π₂ τ [ σ ]t)))  ≡⟨ cong (λ t → π₂ (_,_ {A = A} (π₁ τ ∘ σ) t)) (sym ([]tm≡[]t (π₂ τ) σ)) ⟩
  π₂ (((π₁ τ ∘ σ) , (π₂ τ [ σ ]tm))) ≡⟨ π₂, ⟩
  π₂ τ  [ σ ]tm ∎
  where open ≅-Reasoning
    
-- syntax abbreviations
-- wk : Sub (Δ , A) Δ
pattern wk = π₁ idS
-- vz : Tm (Γ , A) (A [ wk ])
pattern vz = π₂ idS
-- vs : Tm Γ A → Tm (Γ , B) (A [ wk ])   
pattern vs x = x [ wk ]tm
-- vs (vs ... (vs vz) ...) = π₂ idS [ π₁ idS ]tm .... [ π₁ idS ]tm

vz:= : Tm Γ A → Sub Γ (Γ , A)
vz:= t = idS , t
