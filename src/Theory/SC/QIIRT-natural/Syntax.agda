-- Type theory as a quotient inductive-inductive-recursive type, inspired by the formualtion of natural models
-- whereas the recursion part is impredicative.


-- See https://github.com/agda/agda/issues/5362 for the current limitation of Agda
-- that affacts the definition of our encoding

open import Prelude

module Theory.SC.QIIRT-natural.Syntax where
  
infixl 20 _[_]
infixr 10 _∘_
infixl 4 _,_ _,_∶[_,_,_]

interleaved mutual
  data Ctx : Set
  data Sub : Ctx → Ctx → Set
  data Ty  : Ctx → Set
  data Tm  : (Γ : Ctx) → Set

  variable
      Γ Δ Θ Ξ : Ctx
      A B C : Ty Γ
      t u   : Tm Γ
      σ τ δ : Sub Γ Δ

  tyOf₀
    : Tm Γ → Ctx
  tyOf₁
    : (t : Tm Γ) → Sub Γ (tyOf₀ t)
  tyOf₂
    : (t : Tm Γ) → Ty (tyOf₀ t)


  data Ctx where
    ∅
      : Ctx
    _,_
      : (Γ : Ctx)(A : Ty Γ)
      → Ctx
      
  π₁'
    : Sub Γ (Δ , A)
    → Sub Γ Δ

  idS'
    : Sub Γ Γ

  _∘'_
    : Sub Δ Θ → Sub Γ Δ
    → Sub Γ Θ

  _,'_∶[_,_,_]
    : (σ : Sub Γ Δ) (t : Tm Γ) → (p : tyOf₀ t ≡ Δ) → PathP (λ i → Sub Γ (p i)) (tyOf₁ t) σ → PathP (λ i → Ty (p i)) (tyOf₂ t) A
    → Sub Γ (Δ , A)

  βπ₁'
    : (σ : Sub Γ Δ) (t : Tm Γ) → (p₀ : tyOf₀ t ≡ Δ) → (p₁ : PathP (λ i → Sub Γ (p₀ i)) (tyOf₁ t) σ) → (p₂ : PathP (λ i → Ty (p₀ i)) (tyOf₂ t) A)
    → π₁' (σ ,' t ∶[ p₀ , p₁ , p₂ ]) ≡ σ

  data Tm where
    _[_]
      : (t : Tm Δ) (σ : Sub Γ Δ)
      → Tm Γ
    π₂
      : (σ : Sub Γ (Δ , A))
      → Tm Γ
    [idS]tm
      : (t : Tm Γ)
      → t [ idS' ] ≡ t
    [∘]tm
      : (t : Tm Γ)
      → t [ τ ] [ σ ] ≡ t [ τ ∘' σ ]
    βπ₂
      : (t : Tm Γ) (p₀ : tyOf₀ t ≡ Δ) → (p₁ : PathP (λ i → Sub Γ (p₀ i)) (tyOf₁ t) σ) → (p₂ : PathP (λ i → Ty (p₀ i)) (tyOf₂ t) A)
      → PathP (λ i → Sub Γ (p₀ (~ i))) (π₁' (σ ,' t ∶[ p₀ , p₁ , p₂ ])) (tyOf₁ t)
      → π₂ (σ ,' t ∶[ p₀ , p₁ , p₂ ]) ≡ t

  _∘idS'
    : (σ : Sub Γ Δ)
    → σ ∘' idS' ≡ σ
  assocS'
    : (σ : Sub Γ Δ) (τ : Sub Δ Θ) (δ : Sub Θ Ξ)
    → (δ ∘' τ) ∘' σ ≡ δ ∘' (τ ∘' σ)

  tyOf₀ (t [ σ ]) = tyOf₀ t
  tyOf₀ (π₂ {Δ = Δ} {A = A} σ)  = Δ
  tyOf₀ ([idS]tm t i)   = tyOf₀ t
  tyOf₀ ([∘]tm {τ = τ} {σ = σ} t i) = tyOf₀ t
  tyOf₀ {Γ = Γ} (βπ₂ {Δ = Δ} {σ = σ} {A = A} t p₀ p₁ p₂ q i) = p₀ (~ i)


  tyOf₁ (t [ σ ]) = tyOf₁ t ∘' σ
  tyOf₁ (π₂ {A = A} σ)  = π₁' σ
  tyOf₁ ([idS]tm t i)   = (tyOf₁ t ∘idS') i
  tyOf₁ ([∘]tm {τ = τ} {σ = σ} t i) = assocS' σ τ (tyOf₁ t) i
  tyOf₁ {Γ = Γ} (βπ₂ {Δ = Δ} {σ = σ} {A = A} t p₀ p₁ p₂ q i) = q i

  tyOf₂ (t [ σ ]) = tyOf₂ t
  tyOf₂ (π₂ {A = A} σ)  = A
  tyOf₂ ([idS]tm t i)   = tyOf₂ t
  tyOf₂ ([∘]tm {τ = τ} {σ = σ} t i)   = tyOf₂ t
  tyOf₂ {Γ = Γ} (βπ₂ {Δ = Δ} {σ = σ} {A = A} t p₀ p₁ p₂ q i) = p₂ (~ i)

  data Sub where
    ∅
      : Sub Γ ∅
    _,_∶[_,_,_]
      : (σ : Sub Γ Δ) (t : Tm Γ) → (p₀ : tyOf₀ t ≡ Δ) → (p₁ : PathP (λ i → Sub Γ (p₀ i)) (tyOf₁ t) σ) → (p₂ : PathP (λ i → Ty (p₀ i)) (tyOf₂ t) A)
      → Sub Γ (Δ , A)
    idS
      : Sub Γ Γ
    _∘_
      : Sub Δ Θ → Sub Γ Δ
      → Sub Γ Θ
    π₁
      : Sub Γ (Δ , A)
      → Sub Γ Δ
    idS∘_ 
      : (σ : Sub Γ Δ)
      → idS ∘ σ ≡ σ
    _∘idS
      : (σ : Sub Γ Δ)
      → σ ∘ idS ≡ σ
    assocS
      : (σ : Sub Γ Δ) (τ : Sub Δ Θ) (δ : Sub Θ Ξ)
      → (δ ∘ τ) ∘ σ ≡ δ ∘ (τ ∘ σ)
    ,∘
      : (σ : Sub Δ Θ) (t : Tm Δ) (τ : Sub Γ Δ) (p₀ : tyOf₀ t ≡ Θ) → (p₁ : PathP (λ i → Sub Δ (p₀ i)) (tyOf₁ t) σ) → (p₂ : PathP (λ i → Ty (p₀ i)) (tyOf₂ t) A)
      → (σ , t ∶[ p₀ , p₁ , p₂ ]) ∘ τ ≡ ((σ ∘' τ) , t [ τ ] ∶[ p₀ , (λ i → p₁ i ∘' τ) , p₂ ])
    βπ₁
      : (σ : Sub Γ Δ) (t : Tm Γ) (p₀ : tyOf₀ t ≡ Δ) → (p₁ : PathP (λ i → Sub Γ (p₀ i)) (tyOf₁ t) σ) → (p₂ : PathP (λ i → Ty (p₀ i)) (tyOf₂ t) A)
      → π₁ (σ , t ∶[ p₀ , p₁ , p₂ ]) ≡ σ
    ηπ
      : (σ : Sub Γ (Δ , A))
      → σ ≡ (π₁' σ , π₂ σ ∶[ refl , refl , refl ])
      -- Agda is a bit annoying -- QIIT support is not fully general as constructors cannot be interleaved.
    η∅
      : σ ≡ ∅

  idS' = idS
  _∘'_ = _∘_
  _,'_∶[_,_,_] = _,_∶[_,_,_]
  π₁' = π₁
  βπ₁' = βπ₁
  _∘idS' = _∘idS
  assocS' = assocS

  data Ty where
    _[_]
      : (A : Ty Δ)(σ : Sub Γ Δ)
      → Ty Γ
    U
      : Ty Γ
    El : (t : Tm Γ) → tyOf₂ t ≡ U → Ty Γ
    U[]
      : U [ σ ] ≡ U
    [∘]
      : A [ τ ∘ σ ] ≡ A [ τ ] [ σ ]

⟨βπ₂⟩
      : (t : Tm Γ) (p₀ : tyOf₀ t ≡ Δ) → (p₁ : PathP (λ i → Sub Γ (p₀ i)) (tyOf₁ t) σ) → (p₂ : PathP (λ i → Ty (p₀ i)) (tyOf₂ t) A)
      → π₂ (σ ,' t ∶[ p₀ , p₁ , p₂ ]) ≡ t
⟨βπ₂⟩ {Γ = Γ} {σ = σ} t p₀ p₁ p₂ =
 βπ₂ t p₀ p₁ p₂ (subst (λ w → PathP (λ j → Sub Γ (p₀ (~ j))) w (tyOf₁ t)) (sym (βπ₁' σ t p₀ p₁ p₂)) (λ i → p₁ (~ i)))

tyOf : (t : Tm Γ) → Ty Γ
tyOf t = tyOf₂ t [ tyOf₁ t ]

π₁∘
  : (τ : Sub Δ (Θ , A)) (σ : Sub Γ Δ)
  → π₁ (τ ∘ σ) ≡ π₁ τ ∘ σ
π₁∘ τ σ =
  π₁ (τ ∘ σ)
    ≡⟨ cong π₁ (cong (_∘ σ) (ηπ τ)) ⟩
  π₁ ((π₁ τ , π₂ τ ∶[ refl , refl , refl ]) ∘ σ)
    ≡⟨ cong π₁ (,∘ (π₁ τ) (π₂ τ) σ refl refl refl) ⟩
  π₁ (π₁ τ ∘ σ , π₂ τ [ σ ] ∶[ refl , refl , refl ])
    ≡⟨ βπ₁ (π₁ τ ∘ σ) (π₂ τ [ σ ]) refl refl refl ⟩
  π₁ τ ∘ σ
    ∎

π₂∘
  : (τ : Sub Δ (Θ , A))(σ : Sub Γ Δ)
  → π₂ (τ ∘ σ) ≡ (π₂ τ) [ σ ]
π₂∘ τ σ =
  π₂ (τ ∘ σ)
    ≡⟨ cong π₂ (cong (_∘ σ) (ηπ τ)) ⟩
  π₂ ((π₁ τ , π₂ τ ∶[ refl , refl , refl ]) ∘ σ)
    ≡⟨ cong π₂ (,∘ (π₁ τ) (π₂ τ) σ refl refl refl) ⟩
  π₂ (π₁ τ ∘ σ , π₂ τ [ σ ] ∶[ refl , refl , refl ])
    ≡⟨ ⟨βπ₂⟩ (π₂ τ [ σ ]) refl refl refl ⟩
  π₂ τ [ σ ]
    ∎

-- syntax abbreviations
wk : Sub (Δ , A) Δ
wk = π₁ idS

vz : Tm (Γ , A)
vz = π₂ idS

vs : Tm Γ → Tm (Γ , B)
vs x = x [ wk ]
-- vs (vs ... (vs vz) ...) = π₂ idS [ π₁ idS ]tm .... [ π₁ idS ]tm

-- vz:= : (t : Tm Γ) → let (_ , (σ , A)) = tyOf t in Sub Γ (Γ , A [ σ ])
-- vz:= {Γ} t = idS , t ∶[ {!!} ]
