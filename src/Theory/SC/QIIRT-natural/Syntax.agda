-- Type theory as a quotient inductive-inductive-recursive type, inspired by the formualtion of natural models
-- whereas the recursion part is impredicative.


-- See https://github.com/agda/agda/issues/5362 for the current limitation of Agda
-- that affacts the definition of our encoding

open import Prelude

module Theory.SC.QIIRT-natural.Syntax where
  
infixl 20 _[_]
infixr 10 _∘_
infixl 4 _,_ _,_∶[_]

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

  tyOf
    : Tm Γ → Σ[ Δ ∈ Ctx ] (Sub Γ Δ × Ty Δ)

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

  _[_]T
    : (A : Ty Δ)(σ : Sub Γ Δ)
    → Ty Γ

  tyOf' : Tm Γ → Ty Γ

  _,'_∶[_]
    : (σ : Sub Γ Δ) (t : Tm Γ) → tyOf' t ≡ A [ σ ]T -- (_ , (σ , A))
    → Sub Γ (Δ , A)

  βπ₁'
    : (σ : Sub Γ Δ) (t : Tm Γ) (p : tyOf' t ≡ A [ σ ]T)
    → π₁' (σ ,' t ∶[ p ]) ≡ σ

  Π'
    : (A : Ty Γ) (B : Ty (Γ , A))
    → Ty Γ
      
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
      : (t : Tm Γ) (p : tyOf' t ≡ A [ σ ]T) (q : (Δ , (π₁' (σ ,' t ∶[ p ]) , A)) ≡ tyOf t)
      → π₂ (σ ,' t ∶[ p ]) ≡ t
    app
      : (t : Tm Γ) → tyOf' t ≡ Π' A B
      → Tm (Γ , A)
    abs
      : (t : Tm (Γ , A))
      → Tm Γ
    Πβ
      : (t : Tm (Γ , A)) (p : tyOf' (abs t) ≡ Π' A B)
      → app (abs t) p ≡ t

  _∘idS'
    : (σ : Sub Γ Δ)
    → σ ∘' idS' ≡ σ
  assocS'
    : (σ : Sub Γ Δ) (τ : Sub Δ Θ) (δ : Sub Θ Ξ)
    → (δ ∘' τ) ∘' σ ≡ δ ∘' (τ ∘' σ)
    
  [∘]'
    : A [ τ ∘' σ ]T ≡ A [ τ ]T [ σ ]T

  _↑_ : (σ : Sub Γ Δ) (A : Ty Δ) → Sub (Γ , (A [ σ ]T)) (Δ , A)
  σ ↑ A = {!!} -- (σ ∘' π₁' idS') ,' π₂ idS' ∶[ sym [∘]' ] 

  tyOf (t [ σ ]) =
    let  (Θ , (τ , A)) = tyOf t
    in Θ , (τ ∘' σ , A)
  tyOf (π₂ {A = A} σ)  = _ , (π₁' σ , A)
  tyOf ([idS]tm t i)   =
    let (Δ , (σ , A)) = tyOf t in
    Δ , ((σ ∘idS') i , A)
  tyOf ([∘]tm {τ = τ} {σ = σ} t i)   =
    let (Δ , (δ , A)) = tyOf t in
    Δ , (assocS' σ τ δ i , A)
  tyOf {Γ = Γ} (βπ₂ {Δ = Δ} {σ = σ} t p q i) = q i
  tyOf (app {Γ} {A} {B} t p) =
    let (Δ , (σ , C)) = tyOf t in
    (Γ , A) , (idS' , B)
  tyOf (abs {Γ} {A} t) =
    let (Δ , (σ , B)) = tyOf t in
    Γ , (idS' , Π' A (B [ σ ]T))
  tyOf (Πβ t p i) = ?

  tyOf₀ : Tm Γ → Ctx
  tyOf₀ t = tyOf t .fst

  tyOf₁ : (t : Tm Γ) → Sub Γ (tyOf₀ t)
  tyOf₁ t = tyOf t .snd .fst

  tyOf₂ : (t : Tm Γ) → Ty (tyOf₀ t)
  tyOf₂ t = tyOf t .snd .snd

  tyOf' t = tyOf₂ t [ tyOf₁ t ]T

  data Sub where
    ∅
      : Sub Γ ∅
    _,_∶[_]
      : (σ : Sub Γ Δ) (t : Tm Γ) → tyOf' t ≡ A [ σ ]T
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
    ,∘ -- [TODO] Define a smart constructor
      : (σ : Sub Δ Θ) (t : Tm Δ) (τ : Sub Γ Δ) (p : tyOf' t ≡ A [ σ ]T) (q : tyOf' (t [ τ ]) ≡ (A [ σ ∘ τ ]T)) -- (Θ , (σ , A)))
      → (σ , t ∶[ p ]) ∘ τ ≡ (σ ∘ τ , t [ τ ] ∶[ q ])
      -- (σ , t ∶[ p ]) ∘ τ ≡ (σ ∘' τ , t [ τ ] ∶[ (λ i → p i .fst , ((p i .snd .fst ∘' τ) , p i .snd .snd)) ])
    βπ₁
      : (σ : Sub Γ Δ) (t : Tm Γ) (p : tyOf' t ≡ A [ σ ]T)
      → π₁ (σ , t ∶[ p ]) ≡ σ
      -- π₁ (σ , t ∶[ p ]) ≡ σ
    ηπ
      : (σ : Sub Γ (Δ , A))
      → σ ≡ (π₁' σ , π₂ σ ∶[ refl ])
      -- Agda is a bit annoying -- QIIT support is not fully general as constructors cannot be interleaved.
    η∅
      : σ ≡ ∅

  idS' = idS
  _∘'_ = _∘_
  _,'_∶[_] = _,_∶[_]
  π₁' = π₁
  βπ₁' = βπ₁
  _∘idS' = _∘idS
  assocS' = assocS

  data Ty where
    _[_]
      : (A : Ty Δ)(σ : Sub Γ Δ)
      → Ty Γ
    [id]
      : A [ idS ] ≡ A
    [∘]
      : A [ τ ∘ σ ] ≡ A [ τ ] [ σ ]
    U
      : Ty Γ
    U[]
      : U [ σ ] ≡ U
    El
      : (t : Tm Γ) → tyOf' t ≡ U
      → Ty Γ
    El[] -- [TODO]: A smart constructor is needed
      : (p : tyOf' u ≡ U) (q : tyOf' (u [ τ ]) ≡ U) -- tyOf' u ≡ U
      → (El u p) [ τ ] ≡ El (u [ τ ]) q
    Π
      : (A : Ty Γ) (B : Ty (Γ , A))
      → Ty Γ
    Π[]
      : (Π A B) [ σ ] ≡ Π (A [ σ ]T) (B [ σ ↑ A ]) 

  _[_]T = _[_]
  
  [∘]' = [∘]
  Π' = Π
-- ⟨βπ₂⟩ : (t : Tm Γ) (p : tyOf t ≡ (Δ , (σ , A))) → π₂ (σ , t ∶[ {!!} ]) ≡ t
-- ⟨βπ₂⟩ {Δ = Δ} {σ} {A} t p = βπ₂ t p (((λ j → Δ , (βπ₁' σ t {!!} j , A)) ∙ sym p))

-- π₁∘
--   : (τ : Sub Δ (Θ , A)) (σ : Sub Γ Δ)
--   → π₁ (τ ∘ σ) ≡ π₁ τ ∘ σ
-- π₁∘ τ σ =
--   π₁ (τ ∘ σ)
--     ≡⟨ cong π₁ (cong (_∘ σ) (ηπ τ)) ⟩
--   π₁ ((π₁ τ , π₂ τ ∶[ refl ]) ∘ σ)
--     ≡⟨ cong π₁ (,∘ (π₁ τ) (π₂ τ) σ refl) ⟩
--   π₁ (π₁ τ ∘ σ , π₂ τ [ σ ] ∶[ refl ])
--     ≡⟨ βπ₁ (π₁ τ ∘ σ) (π₂ τ [ σ ]) refl ⟩
--   π₁ τ ∘ σ
--     ∎

-- π₂∘
--   : (τ : Sub Δ (Θ , A))(σ : Sub Γ Δ)
--   → π₂ (τ ∘ σ) ≡ (π₂ τ) [ σ ]
-- π₂∘ {Θ = Θ} {A} τ σ = 
--   π₂ (τ ∘ σ)
--     ≡⟨ cong π₂ (cong (_∘ σ) (ηπ τ)) ⟩
--   π₂ ((π₁ τ , π₂ τ ∶[ refl ]) ∘ σ)
--     ≡⟨ cong π₂ (,∘ (π₁ τ) (π₂ τ) σ refl) ⟩
--   π₂ (π₁ τ ∘ σ , π₂ τ [ σ ] ∶[ refl ])
--     ≡⟨ ⟨βπ₂⟩ (π₂ τ [ σ ]) refl ⟩
--   π₂ τ [ σ ]
--     ∎

-- -- -- syntax abbreviations
-- -- wk : Sub (Δ , A) Δ
-- -- wk = π₁ idS

-- -- vz : Tm (Γ , A)
-- -- vz = π₂ idS

-- -- vs : Tm Γ → Tm (Γ , B)
-- -- vs x = x [ wk ]
-- -- -- vs (vs ... (vs vz) ...) = π₂ idS [ π₁ idS ]tm .... [ π₁ idS ]tm

-- -- -- vz:= : (t : Tm Γ) → let (_ , (σ , A)) = tyOf t in Sub Γ (Γ , A [ σ ])
-- -- -- vz:= {Γ} t = idS , t ∶[ {!!} ]
