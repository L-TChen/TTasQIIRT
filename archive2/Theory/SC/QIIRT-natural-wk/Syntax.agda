{-# OPTIONS --cubical --exact-split #-}

-- Type theory as a quotient inductive-inductive-recursive type, inspired by the formualtion of natural models
-- whereas the recursion part is impredicative.


-- See https://github.com/agda/agda/issues/5362 for the current limitation of Agda
-- that affacts the definition of our encoding

module Theory.SC.QIIRT-natural-wk.Syntax where

open import Cubical.Foundations.Prelude
  hiding (Sub)
open import Cubical.Data.Sigma
  hiding (Sub)
  
infixl 20 _[_]
infixr 10 _∘_
infixl 4 _,_ _,_∶[_] _∋[_]_

interleaved mutual
  data Ctx : Set
  data Sub : Ctx → Ctx → Set
  data Wk  : Ctx → Ctx → Set
  data Ty  : Ctx → Set
  data Tm  : (Γ : Ctx) → Set
  data _∋[_]_ : (Γ {Δ} : Ctx) (w : Wk Γ Δ) (A : Ty Δ) → Set

  variable
      Γ Δ Θ Ξ : Ctx
      A B C : Ty Γ
      t u   : Tm Γ
      σ τ δ : Sub Γ Δ
      w v   : Wk Γ Δ
  
  data Ctx where
    ∅
      : Ctx
    _,_
      : (Γ : Ctx)(A : Ty Γ)
      → Ctx
      
  _[_]W'
    : (A : Ty Δ)(σ : Wk Γ Δ)
    → Ty Γ
--  π₁'
--    : Sub Γ (Δ , A)
--    → Sub Γ Δ
--  idS' : Sub Γ Γ
--  _∘'_
--    : Sub Δ Θ → Sub Γ Δ
--    → Sub Γ Θ
--  _,'_∶[_]
--    : (σ : Sub Γ Δ) (t : Tm Γ) → tyOf t ≡ (_ , (σ , A))
--    → Sub Γ (Δ , A)
--  βπ₁'
--    : (σ : Sub Γ Δ) (t : Tm Γ) (p : tyOf t ≡ (_ , (σ , A)))
--    → π₁' (σ ,' t ∶[ p ]) ≡ σ
  data Wk where
    idW  : Wk Γ Γ
    drop
      : Wk Γ Δ
      → Wk (Γ , A) Δ
    keep
      : (w : Wk Γ Δ)
      → Wk (Γ , A [ w ]W') (Δ , A)

  _∘wk_ : Wk Δ Θ → Wk Γ Δ → Wk Γ Θ
  w ∘wk v = {!!}
      
  data _∋[_]_ where
    here
      : (Γ , A) ∋[ drop idW ] A
    there
      : Γ       ∋[ w    ] A
      → (Γ , B) ∋[ w ∘wk drop idW ] A

  data Tm where
    _[_]
      : (t : Tm Δ) (σ : Sub Γ Δ)
      → Tm Γ
    var
      : Γ ∋[ w ] A
      → Tm Γ
--    π₂
--      : (σ : Sub Γ (Δ , A))
--      → Tm Γ
--    [idS]tm
--      : (t : Tm Γ)
--      → t [ idS' ] ≡ t
--    [∘]tm
--      : (t : Tm Γ)
--      → t [ σ ] [ τ ] ≡ t [ σ ∘' τ ]
--    βπ₂
--      : (t : Tm Γ) (p : tyOf t ≡ (Δ , (σ , A)))
--      → π₂ (σ ,' t ∶[ p ]) ≡ t
  π₁ : Sub Γ (Δ , A) → Sub Γ Δ
  π₂ : Sub Γ (Δ , A) → Tm Γ
  _∘_ : Sub Δ Θ → Sub Γ Δ → Sub Γ Θ

  idS : Sub Γ Γ

  ⇑ : Wk Γ Δ → Sub Γ Δ
  
  tyOf   : Tm Γ → Σ[ Δ ∈ Ctx ] (Sub Γ Δ × Ty Δ)
  tyOf (t [ σ ]) =
    let  (Θ , (τ , A)) = tyOf t in Θ , (τ ∘ σ , A)
  tyOf (var {Γ} {Δ} {w} {A} x)   = Δ , (⇑ w , A)
--  tyOf (π₂ {A = A} σ)  = {!!} , {!!} -- (π₁' σ , A)
--  tyOf ([idS]tm t i)   = {!!}
--  tyOf ([∘]tm   t i)   = {!!}
--  tyOf (βπ₂     t p i) = {!!}
      
  data Sub where
    ∅
      : Sub Γ ∅
    _,_∶[_]
      : (σ : Sub Γ Δ) (t : Tm Γ) → tyOf t ≡ (_ , (σ , A))
      → Sub Γ (Δ , A)
--    idS
--      : Sub Γ Γ
--    _∘_
--      : Sub Δ Θ → Sub Γ Δ
--      → Sub Γ Θ
--    π₁
--      : Sub Γ (Δ , A)
--      → Sub Γ Δ
--    idS∘_ 
--      : (σ : Sub Γ Δ)
--      → idS ∘ σ ≡ σ
--    _∘idS
--      : (σ : Sub Γ Δ)
--      → σ ∘ idS ≡ σ
--    assocS
--      : (δ ∘ τ) ∘ σ ≡ δ ∘ (τ ∘ σ)
--    ,∘
--      : (σ : Sub Δ Θ) (t : Tm Δ) (τ : Sub Γ Δ) (p : tyOf t ≡ (Θ , (σ , A)))
--      → (σ , t ∶[ p ]) ∘ τ ≡ (σ ∘' τ , t [ τ ] ∶[ (λ i → p i .fst , ((p i .snd .fst ∘' τ) , p i .snd .snd)) ])
--    βπ₁
--      : (σ : Sub Γ Δ) (t : Tm Γ) (p : tyOf t ≡ (_ , (σ , A)))
--      → π₁ (σ , t ∶[ p ]) ≡ σ
--    ηπ
--      : (σ : Sub Γ (Δ , A))
--      → σ ≡ (π₁' σ , π₂ σ ∶[ refl ])
--      -- Agda is a bit annoying -- QIIT support is not fully general as constructors cannot be interleaved.
--    η∅

--      : σ ≡ ∅

--  idS' = idS
--  _∘'_ = _∘_
--  _,'_∶[_] = _,_∶[_]
--  π₁' = π₁
--  βπ₁' = βπ₁

  π₁ (σ , _ ∶[ _ ]) = σ
  π₂ (_ , t ∶[ _ ]) = t

  idS {Γ = Γ} = {!!}

  ∅              ∘ σ = ∅
  (τ , t ∶[ p ]) ∘ σ = τ ∘ σ , t [ σ ] ∶[ {!!} ]

  _[_]S : (A : Ty Δ) (σ : Sub Γ Δ) → Ty Γ
    
  ↑_ : (σ : Sub Γ Δ) → Sub (Γ , (A [ σ ]S)) (Δ , A)
  ↑ σ = {!!}
  
  ⇑ idW      = idS
  ⇑ (drop w) = {!!} -- substitution weakening?
  ⇑ (keep w) = {!!} -- substitution lifting?

  data Ty where
--    _[_]
--      : (A : Ty Δ)(σ : Sub Γ Δ)
--      → Ty Γ
    _[_]
      : (A : Ty Δ)(σ : Wk Γ Δ)
      → Ty Γ
    U
      : Ty Γ
--    U[]
--      : U [ σ ] ≡ U
--    [∘]
--      : A [ τ ∘ σ ] ≡ A [ τ ] [ σ ]

  _[_]W' = _[_]

  A [ σ ]S = {!!}

η∅
  : (σ : Sub Γ ∅)
  → σ ≡ ∅
η∅ ∅ = refl

tyOfπ₂
  : (σ : Sub Γ (Δ , A))
  → tyOf (π₂ σ) ≡ (Δ , (π₁ σ , A))
tyOfπ₂ (σ , t ∶[ p ]) = p

ηπ
  : (σ : Sub Γ (Δ , A))
  → σ ≡ (π₁ σ , π₂ σ ∶[ tyOfπ₂ σ ])
ηπ (σ , t ∶[ x ]) = refl

π₁∘
  : (τ : Sub Δ (Θ , A)) (σ : Sub Γ Δ)
  → π₁ (τ ∘ σ) ≡ π₁ τ ∘ σ
π₁∘ (τ , _ ∶[ p ]) σ = refl

π₂∘
  : (τ : Sub Δ (Θ , A))(σ : Sub Γ Δ)
  → π₂ (τ ∘ σ) ≡ (π₂ τ) [ σ ]
π₂∘ (τ , t ∶[ x ]) σ = refl

-- -- syntax abbreviations
-- wk : Sub (Δ , A) Δ
-- wk = π₁ idS

-- vz : Tm (Γ , A)
-- vz = π₂ idS

-- vs : Tm Γ → Tm (Γ , B)
-- vs x = x [ wk ]
-- -- vs (vs ... (vs vz) ...) = π₂ idS [ π₁ idS ]tm .... [ π₁ idS ]tm

-- -- vz:= : (t : Tm Γ) → let (_ , (σ , A)) = tyOf t in Sub Γ (Γ , A [ σ ])
-- -- vz:= {Γ} t = idS , t ∶[ {!!} ]
