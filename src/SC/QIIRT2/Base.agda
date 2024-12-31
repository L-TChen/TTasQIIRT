-- Formalizing Substitution Calculus as QIIRT
module SC.QIIRT2.Base where

open import Prelude
  hiding (_,_)

-- inductive-inductive-recursive definition of context, type, term, and type substitution

infixl 35 _[_] _[_]t _[_]tm
infixl 10 _,_

interleaved mutual
  data Ctx : Set
  data Ty  (Γ : Ctx) : Set
  data Sub (Γ : Ctx) : Ctx → Set
  data Tm  : (Γ : Ctx) → Ty Γ → Set

  postulate
    _[_]  : ∀{Δ Γ} → Ty Γ → Sub Δ Γ → Ty Δ

  variable
    Γ Δ Θ : Ctx
    A B C : Ty Γ
    t u   : Tm Γ A
    σ τ γ : Sub Δ Γ

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
      → (σ : Sub Δ Θ) (δ : Sub Γ Δ)
      → Sub Γ Θ
    π₁
      : (σ : Sub Γ (Δ , A))
      → Sub Γ Δ
    U
      : Ty Γ
    π₂
      : (σ : Sub Δ (Γ , A))
      → Tm Δ (A [ π₁ σ ])
    _[_]tm
      : Tm Γ A → (σ : Sub Δ Γ)
      → Tm Δ (A [ σ ])

  postulate
    U[]   : U [ σ ] ≡ U
    {-# REWRITE U[] #-}

    [id]  : A [ idS ]        ≡ A
    [∘]   : A [ τ ∘ σ ]      ≡ A [ τ ] [ σ ]
    [π₁,] : A [ π₁ (σ , t) ] ≡ A [ σ ]
    [π₁∘] : A [ π₁ (τ ∘ σ) ] ≡ A [ π₁ τ ] [ σ ]
    {-# REWRITE [id] [∘] [π₁,] [π₁∘] #-}

  _[_]t : Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ])
  t [ idS        ]t = t
  t [ τ ∘ σ      ]t = t [ τ ]t [ σ ]t
  t [ π₁ (σ , u) ]t = t [ σ ]t
  t [ π₁ (τ ∘ σ) ]t = t [ π₁ τ ]t [ σ ]t
  {-# CATCHALL #-}
  t [ σ       ]t = t [ σ ]tm

  postulate
    [id]tm : t [ idS   ]tm ≡ t
    [∘]tm  : t [ τ ∘ σ ]tm ≡ t [ τ ]tm [ σ ]tm
    -- equality constructors
    idS∘_ 
      : (σ : Sub Δ Γ)
      → idS ∘ σ ≡ σ
    _∘idS
      : (σ : Sub Δ Γ)
      → σ ∘ idS ≡ σ
    assocS
      : (σ ∘ τ) ∘ γ ≡ σ ∘ (τ ∘ γ)
    ,∘
      : (σ , t) ∘ τ ≡ σ ∘ τ , t [ τ ]t
    π₁,
      : π₁ (σ , t) ≡ σ
    π₂,
      : π₂ (σ , t) ≡ t
    η∅
      : {σ : Sub Δ ∅}
      → σ ≡ ∅
    η,
      : σ ≡ π₁ σ , π₂ σ

-- derived computation rules on composition
π₁∘ : (σ : Sub Γ Δ) (τ : Sub Δ (Θ , A)) → π₁ (τ ∘ σ) ≡ π₁ τ ∘ σ
π₁∘ σ τ = begin
    π₁ (τ ∘ σ)                    ≡⟨ cong (λ σ' → π₁ (σ' ∘ σ)) η, ⟩
    π₁ ((π₁ τ , π₂ τ) ∘ σ)        ≡⟨ cong π₁ ,∘ ⟩ 
    π₁ (π₁ τ ∘ σ , (π₂ τ) [ σ ]t) ≡⟨ π₁, ⟩
    π₁ τ ∘ σ                      ∎
  where open ≡-Reasoning

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

π₁idS∘ : {A : Ty Γ}(σ : Sub Δ (Γ , A)) → π₁ idS ∘ σ ≡ π₁ σ
π₁idS∘ σ = begin
  π₁ idS ∘ σ      ≡⟨ sym (π₁∘ σ idS) ⟩
  π₁ (idS ∘ σ)    ≡⟨ cong π₁ (idS∘ σ) ⟩
  π₁ σ            ∎
  where open ≡-Reasoning

π₂∘ : (σ : Sub Γ Δ) (τ : Sub Δ (Θ , A))
  → π₂ (τ ∘ σ) ≡ π₂ τ [ σ ]tm
π₂∘ {Γ} {Δ} {Θ} {A} σ τ = ≅-to-≡ $ begin
  π₂ (τ ∘ σ)                         ≅⟨ hcong (λ ν → π₂ (ν ∘ σ)) (≡-to-≅ η,) ⟩
  π₂ (((π₁ τ) , (π₂ τ)) ∘ σ)         ≅⟨ hcong π₂ (≡-to-≅ ,∘) ⟩
  π₂ (((π₁ τ ∘ σ) , (π₂ τ [ σ ]t)))  ≡⟨ cong (λ t → π₂ (_,_ {A = A} (π₁ τ ∘ σ) t)) ([]tm≡[]t (π₂ τ) σ) ⟨
  π₂ (((π₁ τ ∘ σ) , (π₂ τ [ σ ]tm))) ≡⟨ π₂, ⟩
  π₂ τ  [ σ ]tm                      ∎
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

coh[η∅] : A [ σ ] ≡ A [ ∅ ]
coh[η∅] {A = U} = refl
    
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
