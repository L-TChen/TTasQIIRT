-- inductive-inductive-recursive definition of context, type, term, and type substitution
{-# OPTIONS --local-confluence-check #-}

module SC+El.QIIRT2.Base where
 
open import Prelude
  hiding (_,_)

open import Relation.Binary.HeterogeneousEquality as HEq
  using (_≅_; refl; module ≅-Reasoning)


infixl 35 _[_] _[_]t _[_]tm
infixl 4 _,_

interleaved mutual
  data Ctx : Set
  data Ty  : Ctx → Set
  data Sub : Ctx → Ctx → Set
  data Tm  : (Γ : Ctx) → Ty Γ → Set

  variable
      Γ Δ Θ : Ctx
      A B   : Ty Γ
      t u     : Tm Γ A
      σ τ γ υ : Sub Δ Γ

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
      : Sub Δ ∅
    _,_
      : (σ : Sub Γ Δ) (t : Tm Γ (A [ σ ]))
      ------------------------------------
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
      : (σ : Sub Γ Δ) (t : Tm Γ (A [ σ ]))
      → π₁ (σ , t) ≡ σ
    π₂,
      : {σ : Sub Δ Γ}{t : Tm Δ (A [ σ ])}
      →  π₂ (_,_ {A = A} σ t) ≡ t 
    ,∘
      -- {A : Ty Γ}{σ : Sub Δ Γ}{t : Tm Δ (A [ σ ])}{τ : Sub Θ Δ}
      : ((σ , t) ∘ τ) ≡ ((σ ∘ τ) , t [ τ ]t)
    η∅
      : {σ : Sub Γ ∅}
      → σ ≡ ∅
    η,
      : {σ : Sub Δ (Γ , A)}
      → σ ≡ (π₁ σ , π₂ σ)

  data _ where
    U
      : Ty Γ
    El
      : Tm Γ U → Ty Γ
      
  postulate
    U[]  : (σ : Sub Γ Δ) → _[_] {Δ} {Γ} U σ  ≡ U
    {-# REWRITE U[] #-}

    El[] : (σ : Sub Γ Δ) → (El t) [ σ ] ≡ El (t [ σ ]t)
    {-# REWRITE El[] #-}

  -- derived computation rules on composition
  π₁∘ : (σ : Sub Δ (Γ , A))(τ : Sub Θ Δ) → π₁ (σ ∘ τ) ≡ π₁ σ ∘ τ
  π₁∘ σ τ =
      π₁ (σ ∘ τ)
    ≡⟨ cong (λ σ' → π₁ (σ' ∘ τ)) η, ⟩
      π₁ ((π₁ σ , π₂ σ) ∘ τ)
    ≡⟨ cong π₁ ,∘ ⟩ 
      π₁ (π₁ σ ∘ τ , (π₂ σ) [ τ ]t)
    ≡⟨ π₁, _ _ ⟩
      π₁ σ ∘ τ
    ∎

  []t≡[]tm : {Γ Δ : Ctx} {A : Ty Δ} (t : Tm Δ A) (σ : Sub Γ Δ) → t [ σ ]tm ≡ t [ σ ]t 
  []t≡[]tm t ∅       = refl
  []t≡[]tm t (_ , _) = refl
  []t≡[]tm t idS     = [id]tm
  []t≡[]tm t (π₁ idS)     = refl
  []t≡[]tm t (π₁ (τ ∘ σ)) = begin
    t [ π₁ (τ ∘ σ) ]tm
      ≡⟨ {!!} ⟩
    t [ π₁ τ ∘ σ ]tm
      ≡⟨ [∘]tm ⟩
    t [ π₁ τ ]tm [ σ ]tm
      ≡⟨ cong (_[ σ ]tm) ([]t≡[]tm t (π₁ τ)) ⟩
    t [ π₁ τ ]t [ σ ]tm
      ≡⟨ []t≡[]tm (t [ π₁ τ ]t) σ ⟩
    t [ π₁ τ ]t [ σ ]t
      ∎
  []t≡[]tm t (π₁ (π₁ σ))  = refl
  []t≡[]tm t (τ ∘ σ) = begin
    t [ τ ∘ σ ]tm
      ≡⟨ [∘]tm ⟩
    t [ τ ]tm [ σ ]tm
      ≡⟨ cong (_[ σ ]tm) ([]t≡[]tm t τ)  ⟩
    t [ τ ]t [ σ ]tm
      ≡⟨ []t≡[]tm (t [ τ ]t) σ ⟩
    t [ τ ]t [ σ ]t
      ∎
  []t≡[]tm t (π₁ (σ , u)) = 
    t [ π₁ (σ , u) ]tm
      ≡⟨ {!!} ⟩
    t [ σ ]tm
      ≡⟨ []t≡[]tm t σ ⟩
    t [ σ ]t
      ∎
      
-- We will need to prove coherence for the following with another rewriting relation:
-- coherence of postulates
  
  coh[idS∘] : A [ idS ∘ σ ] ≡ A [ σ ]
  coh[idS∘] = refl

  coh[∘idS] : A [ σ ∘ idS ] ≡ A [ σ ]
  coh[∘idS] = refl

  coh[assocS] : A [ (σ ∘ τ) ∘ γ ] ≡ A [ σ ∘ (τ ∘ γ) ]
  coh[assocS] = refl

  coh[,∘] : A [ (σ , t) ∘ τ ] ≡ A [ σ ∘ τ , t [ τ ]t ]
  coh[,∘] {A = U} {σ = σ} {t = t} {τ = τ}    = refl
  coh[,∘] {A = El u} {σ = σ} {t = t} {τ = τ} = cong El (begin
   u [ σ , t ]tm [ τ ]t       ≡⟨ sym ([]t≡[]tm (u [ σ , t ]tm) τ) ⟩
   u [ σ , t ]tm [ τ ]tm      ≡⟨ sym ([∘]tm) ⟩
   u [ (σ , t) ∘ τ ]tm        ≡⟨ cong (u [_]tm) ,∘ ⟩
   u [ (σ ∘ τ) , t [ τ ]t ]tm ∎)
  
  coh[βπ₁] : A [ π₁ (σ , t) ] ≡ A [ σ ]
  coh[βπ₁] = refl

  coh[βπ₂] : π₂ (σ , t) [ τ ]t ≡ t [ τ ]t
  coh[βπ₂] {σ = σ} {t = t} {τ = τ} = begin
    π₂ (σ , t) [ τ ]t
      ≡⟨ sym ([]t≡[]tm _ _) ⟩
    π₂ (σ , t) [ τ ]tm
      ≡⟨ cong (_[ τ ]tm) π₂, ⟩
    t [ τ ]tm
      ≡⟨ []t≡[]tm _ _ ⟩
    t [ τ ]t
      ∎

  coh[η,] : A [ σ ] ≡ A [ π₁ σ , π₂ σ ]
  coh[η,] {A = U}    {σ} = refl
  coh[η,] {A = El t} {σ = σ} = cong El (begin
    t [ σ ]t              ≡⟨ sym ([]t≡[]tm t σ) ⟩
    t [ σ ]tm             ≡⟨ cong (t [_]tm) η, ⟩
    t [ π₁ σ , π₂ σ ]tm   ∎ 
    )

  coh[η∅] : A [ σ ] ≡ A [ ∅ ]
  coh[η∅] {A = U}            = refl
  coh[η∅] {A = El t} {σ = σ} = cong El (begin
    t [ σ ]t
      ≡⟨ sym ([]t≡[]tm t σ) ⟩
    t [ σ ]tm
      ≡⟨ cong (t [_]tm) η∅ ⟩
    t [ ∅ ]tm
      ∎)

π₂∘ : (σ : Sub Δ (Γ , A))(τ : Sub Θ Δ)
  → π₂ (σ ∘ τ) ≡ π₂ σ [ τ ]tm
π₂∘ {Δ} {Γ} {A} {Θ} σ τ =
    π₂ (σ ∘ τ)
  ≡⟨ {!!} ⟩
    π₂ {A = A} ((π₁ σ , π₂ σ) ∘ τ)
  ≡⟨ {!!} ⟩
    π₂ {A = A} ((π₁ σ ∘ τ) , π₂ σ [ τ ]tm)
  ≡⟨ π₂, {σ = π₁ σ ∘ τ} ⟩
    π₂ σ [ τ ]tm
  ∎
    
-- syntax abbreviations
wk : Sub (Δ , A) Δ
wk = π₁ idS

vz : Tm (Γ , A) (A [ wk ])
vz = π₂ idS

vs : Tm Γ A → Tm (Γ , B) (A [ wk ])   
vs x = x [ wk ]tm
-- vs (vs ... (vs vz) ...) = π₂ idS [ π₁ idS ]tm .... [ π₁ idS ]tm

vz:= : Tm Γ A → Sub Γ (Γ , A)
vz:= t = idS , t
