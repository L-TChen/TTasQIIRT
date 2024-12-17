{-# OPTIONS -vtc.cover.splittree:10 #-}
-- Formalizing Substitution Calculus as QIIRT
module SC.QIIRT2.Base where

open import Prelude
  hiding (_,_)

-- inductive-inductive-recursive definition of context, type, term, and type substitution

infixl 35 _[_] _[_]t _[_]tm
infixl 10 _,_

data Ctx : Set
data Ty  : Ctx → Set
data Sub : Ctx → Ctx → Set
data Tm  : (Γ : Ctx) → Ty Γ → Set

postulate
  _[_]  : ∀{Δ Γ} → Ty Γ → Sub Δ Γ → Ty Δ
 
variable
  Γ Δ Θ     : Ctx
  A B A' B' : Ty Γ
  t u       : Tm Γ A
  σ τ γ υ σ' τ' : Sub Δ Γ

data Ctx where
  ∅
    : Ctx
  _,_
    : (Γ : Ctx) (A : Ty Γ)
    → Ctx

data Sub where
  ∅
    ---------
    : Sub Δ ∅
  _,_
    : (σ : Sub Δ Γ) (t : Tm Δ (A [ σ ]))
    ------------------------------------
    → Sub Δ (Γ , A)
  idS
    : Sub Δ Δ
  _∘_
    : {Γ Δ Θ : Ctx}
    → (σ : Sub Δ Γ) (δ : Sub Θ Δ)
    → Sub Θ Γ
  π₁
   : (σ : Sub Δ (Γ , A))
   → Sub Δ Γ

data Ty where
  U
    : Ty Γ

postulate
  U[]   : U [ σ ] ≡ U
  {-# REWRITE U[] #-}

data Tm where
  π₂
    : (σ : Sub Δ (Γ , A))
    → Tm Δ (A [ π₁ σ ])
  _[_]tm
    : Tm Γ A → (σ : Sub Δ Γ)
    → Tm Δ (A [ σ ])

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
  -- equality constructors
  idS∘_ 
    : (σ : Sub Δ Γ)
    → idS ∘ σ ≡ σ
  _∘idS
    : (σ : Sub Δ Γ)
    → σ ∘ idS ≡ σ
  assocS
    : (σ ∘ τ) ∘ υ ≡ σ ∘ (τ ∘ υ)
  ,∘
    : {A : Ty Γ}{σ : Sub Δ Γ}{t : Tm Δ (A [ σ ])}{τ : Sub Θ Δ}
    → (_,_ {A = A} σ t) ∘ τ ≡ σ ∘ τ , t [ τ ]t
  π₁,
    : {σ : Sub Δ Γ}{t : Tm Δ (A [ σ ])}
    → π₁ (_,_ {A = A} σ t) ≡ σ
  π₂,
    : {σ : Sub Δ Γ}{t : Tm Δ (A [ σ ])}
    → π₂ (_,_ {A = A} σ t) ≡ t
  η∅
    : {σ : Sub Δ ∅}
    → σ ≡ ∅
  η,
    : {σ : Sub Δ (Γ , A)}
    → σ ≡ π₁ σ , π₂ σ

-- derived computation rules on composition
π₁∘ : (σ : Sub Γ Δ) (τ : Sub Δ (Θ , A)) → π₁ (τ ∘ σ) ≡ π₁ τ ∘ σ
π₁∘ σ τ = begin
    π₁ (τ ∘ σ)                    ≡⟨ cong (λ σ' → π₁ (σ' ∘ σ)) η, ⟩
    π₁ ((π₁ τ , π₂ τ) ∘ σ)        ≡⟨ cong π₁ ,∘ ⟩ 
    π₁ (π₁ τ ∘ σ , (π₂ τ) [ σ ]t) ≡⟨ π₁, ⟩
    π₁ τ ∘ σ                      ∎
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

π₁idS∘ : {A : Ty Γ}(σ : Sub Δ (Γ , A)) → π₁ idS ∘ σ ≡ π₁ σ
π₁idS∘ σ = begin
  π₁ idS ∘ σ      ≡⟨ sym (π₁∘ σ idS) ⟩
  π₁ (idS ∘ σ)    ≡⟨ cong π₁ (idS∘ σ) ⟩
  π₁ σ            ∎
  where open ≡-Reasoning

π₂∘ : (σ : Sub Γ Δ) (τ : Sub Δ (Θ , A))
  → π₂ (τ ∘ σ) ≡ π₂ τ [ σ ]tm
π₂∘ {Γ} {Δ} {Θ} {A} σ τ = ≅-to-≡ $ begin
  π₂ (τ ∘ σ)                         ≅⟨ HEq.cong (λ ν → π₂ (ν ∘ σ)) (≡-to-≅ η,) ⟩
  π₂ (((π₁ τ) , (π₂ τ)) ∘ σ)         ≅⟨ HEq.cong π₂ (≡-to-≅ ,∘) ⟩
  π₂ (((π₁ τ ∘ σ) , (π₂ τ [ σ ]t)))  ≡⟨ cong (λ t → π₂ (_,_ {A = A} (π₁ τ ∘ σ) t)) (sym ([]tm≡[]t (π₂ τ) σ)) ⟩
  π₂ (((π₁ τ ∘ σ) , (π₂ τ [ σ ]tm))) ≡⟨ π₂, ⟩
  π₂ τ  [ σ ]tm ∎
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
coh[η∅] {A = U}            = refl
    
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