-- inductive-inductive-recursive definition of context, type, term, and type substitution

module SC+Pi.QIIRT-Lift.Base where
 
open import Prelude
  hiding (_,_)


infixr 20 [_]l_ [_⇈_]_ [_]_ [_⇈_]t_ [_]t_
infixl 10 _⨟_
infixl 10 _++_
infixl 6 _,_

interleaved mutual
  data Ctx  : Set
  data Lift : Ctx → Set
  data Ty  : Ctx → Set
  data Sub : Ctx → Ctx → Set
  data Tm  : (Γ : Ctx) → Ty Γ → Set
  
  variable
      Γ Δ Θ Φ : Ctx
      A B C   : Ty Γ
      t u     : Tm Γ A
      σ τ γ υ : Sub Γ Δ
      As Bs   : Lift Γ

  _++_ : (Γ : Ctx) → Lift Γ → Ctx

  postulate
    [_]l_  : Sub Γ Δ → Lift Δ → Lift Γ
    [_⇈_]_ : (As : Lift Δ) (σ : Sub Γ Δ) (A : Ty (Δ ++ As))
      → Ty (Γ ++ [ σ ]l As)

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
  Γ ++ (As , A) = Γ ++ As , A

  postulate
    ∅[]l : [ σ ]l ∅        ≡ ∅
    ,[]l : [ σ ]l (As , A) ≡ [ σ ]l As , [ As ⇈ σ ] A
    {-# REWRITE ∅[]l #-}

  [_]_ : (σ : Sub Γ Δ) (A : Ty Δ) → Ty Γ
  [ σ ] A = [ ∅ ⇈ σ ] A

  data _ where
    U
      : Ty Γ
    Π
      : (A : Ty Γ) → Ty (Γ , A) → Ty Γ
    ∅
      : Sub Γ ∅
    _,_
      : (σ : Sub Γ Δ) {A : Ty Δ} (t : Tm Γ ([ σ ] A))
      ----------------------------------------
      → Sub Γ (Δ , A) 
    idS
      : Sub Γ Γ
    _⨟_
      : (σ : Sub Γ Δ) (τ : Sub Δ Θ) 
      → Sub Γ Θ
    π₁
      : Sub Γ (Δ , A)
      → Sub Γ Δ
    π₂
      : (σ : Sub Γ (Δ , A))
      → Tm Γ ([ π₁ σ ] A)
    [_⇈_]t_
      : {Γ Δ : Ctx} (As : Lift Δ) (σ : Sub Γ Δ) {A : Ty (Δ ++ As)}
      → Tm (Δ ++ As)        A
      → Tm (Γ ++ [ σ ]l As) ([ As ⇈ σ ] A)
    abs
      : Tm (Γ , A) B → Tm Γ (Π A B)
    app
      : Tm Γ (Π A B) → Tm (Γ , A) B

  [_]t_
    : (σ : Sub Γ Δ) {A : Ty Δ}
    → Tm Δ A
    → Tm Γ ([ σ ] A)
  [ σ ]t t = [ ∅ ⇈ σ ]t t
  
  pattern wk   = π₁ idS
  pattern vz   = π₂ idS
  pattern vs x = [ ∅ ⇈ wk ]t x

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
    [idS]l : [ idS        ]l As ≡ As
    [∘]l   : [ σ ⨟ τ      ]l As ≡ [ σ ]l [ τ ]l As
    [π₁,]l : [ π₁ (σ , t) ]l As ≡ [ σ ]l As
    [π₁∘]l : [ π₁ (σ ⨟ τ) ]l As ≡ [ σ ]l [ π₁ τ ]l As
    {-# REWRITE [idS]l [∘]l [π₁,]l [π₁∘]l #-}

    [id]
      : [ As ⇈ idS ] A ≡ A
    [∘]
      : [ As ⇈ (σ ⨟ τ) ] A ≡  [ [ τ ]l As ⇈ σ ] [ As ⇈ τ ] A
    [π₁,]
      : [ As ⇈ π₁ (σ , t) ] A ≡ [ As ⇈ σ ] A
    [π₁⨟]
      : [ As ⇈ π₁ (σ ⨟ τ) ] A ≡ [ [ π₁ τ ]l As ⇈ σ ] [ As ⇈ π₁ τ ] A
    {-# REWRITE [id] [∘] [π₁,] [π₁⨟] ,[]l #-}

  postulate
  -- Equality constructors for terms
    [id]t : [ As ⇈ idS   ]t t ≡ t
    [∘]t  : [ As ⇈ σ ⨟ τ ]t t ≡ [ [ τ ]l As ⇈ σ ]t [ As ⇈ τ ]t t

  -- Equality constructors for substitutions
    idS∘_
      : (σ : Sub Γ Δ)
      → σ ⨟ idS ≡ σ
    _∘idS
      : (σ : Sub Γ Δ)
      → idS ⨟ σ ≡ σ
    assocS
      : (υ ⨟ τ) ⨟ σ ≡ υ ⨟ (τ ⨟ σ)
    π₁,
      : π₁ (σ , t) ≡ σ
    π₂,
      : {σ : Sub Γ Δ}{A : Ty Δ}{t : Tm Γ ([ σ ] A)}
      →  π₂ (σ , t) ≡ t 
    ,∘
      : (τ ⨟ (σ , t)) ≡ ((τ ⨟ σ) , [ τ ]t t)
    η∅
      : {σ : Sub Γ ∅}
      → σ ≡ ∅
    η,
      : {σ : Sub Γ (Δ , A)}
      → σ ≡ (π₁ σ , π₂ σ)

  postulate
    U[]
      : [ As ⇈ σ ] U ≡ U

    {-# REWRITE U[] #-}

  U[∅] : [ σ ] U ≡ U -- Why is this not an instance of U[∅]?
  U[∅] {Γ} {Δ} {σ} = U[] {Δ} {∅} {Γ} {σ}

  U[,] : [ As , A ⇈ σ ] U ≡ U
  U[,] {Γ} {As} {A} {Δ} {σ} = U[] {Γ} {As , A} {Δ} {σ}

  postulate
    Π[]
      : (σ : Sub Γ Δ) → [ As ⇈ σ ] Π A B ≡ Π ([ As ⇈ σ ] A) ([ (As , A) ⇈ σ ] B)
    {-# REWRITE Π[] #-}

  Π[∅] -- why is this not an instance of Π[]?
    : (σ : Sub Γ Δ) → [ σ ] Π A B ≡ Π ([ σ ] A) ([ ∅ , A ⇈ σ ] B)
  Π[∅] {Γ} {Δ} σ = Π[] {Γ} {Δ} {∅} σ

  Π[,] -- why is this not an instance of Π[]?
    : (σ : Sub Γ Δ) → [ As , A ⇈ σ ] Π B C ≡ Π ([ As , A ⇈ σ ] B) ([ As , A , B ⇈ σ ] C)
  Π[,] {Γ} {Δ} {As} {A} {B} {C} = Π[] {Γ} {Δ} {As , A} {B} {C}

--  {-# REWRITE U[∅] U[] Π[∅] Π[,] #-}

cong-U : Γ ≅ Δ → U {Γ} ≅ U {Δ}
cong-U {Γ} refl = refl

-- derived computation rules on composition
π₁∘ : (σ : Sub Γ Δ) (τ : Sub Δ (Θ , A)) → π₁ (σ ⨟ τ) ≡ σ ⨟ π₁ τ
π₁∘ {Γ} {Δ} {Θ} {A} σ τ = begin
  π₁ (σ ⨟ τ)                    ≡⟨ cong (λ τ → π₁ (σ ⨟ τ)) η, ⟩
  π₁ (σ ⨟ (π₁ τ , π₂ τ))        ≡⟨ cong π₁ ,∘ ⟩ 
  π₁ (σ ⨟ π₁ τ , [ σ ]t π₂ τ)   ≡⟨ π₁, ⟩
  σ ⨟ π₁ τ                      ∎
  where open ≡-Reasoning

-- {-
-- {-# TERMINATING #-} -- the size of σ is decreasing
-- []tm≡[]t : {Γ Δ : Ctx}(As : Lift Δ){A : Ty (Δ ++ As)}(t : Tm (Δ ++ As) A)(σ : Sub Γ Δ)
--   → t [ σ ⇈ As ]tm ≡ t [ σ ⇈ As ]t 
-- []tm≡[]t As t ∅       = refl
-- []tm≡[]t As t (_ , _) = refl
-- []tm≡[]t As t idS     = [id]tm
-- []tm≡[]t ∅ t wk = refl
-- []tm≡[]t (As , A) t wk = refl
-- []tm≡[]t ∅ t (π₁ (τ ∘ σ)) = ≅-to-≡ $ begin
--   t [ π₁ (τ ∘ σ) ⇈ ∅ ]tm       ≅⟨ HEq.cong (λ σ' → t [ σ' ⇈ ∅ ]tm) (≡-to-≅ (π₁∘ σ τ)) ⟩
--   t [ π₁ τ ∘ σ ⇈ ∅ ]tm         ≡⟨ [∘]tm ⟩
--   t [ π₁ τ ⇈ ∅ ]tm [ σ ⇈ ∅ ]tm ≡⟨ cong (λ t' → t' [ σ ⇈ ∅ ]tm) ([]tm≡[]t ∅ t (π₁ τ)) ⟩
--   t [ π₁ τ ⇈ ∅ ]t [ σ ⇈ ∅ ]tm  ≡⟨ []tm≡[]t ∅ (t [ π₁ τ ⇈ ∅ ]t) σ ⟩
--   t [ π₁ τ ⇈ ∅ ]t [ σ ⇈ ∅ ]t   ∎
--   where open ≅-Reasoning
-- []tm≡[]t As@(_ , _) t (π₁ (τ ∘ σ)) = ≅-to-≡ $ begin
--   t [ π₁ (τ ∘ σ) ⇈ As ]tm                  ≅⟨ HEq.cong (λ σ' → t [ σ' ⇈ As ]tm) (≡-to-≅ (π₁∘ σ τ)) ⟩
--   t [ π₁ τ ∘ σ ⇈ As ]tm                    ≡⟨ [∘]tm ⟩
--   t [ π₁ τ ⇈ As ]tm [ σ ⇈ As [ π₁ τ ]l ]tm ≡⟨ cong (λ t' → t' [ σ ⇈ As [ π₁ τ ]l ]tm) ([]tm≡[]t As t (π₁ τ)) ⟩
--   t [ π₁ τ ⇈ As ]t [ σ ⇈ As [ π₁ τ ]l ]tm  ≡⟨ []tm≡[]t (As [ π₁ τ ]l) (t [ π₁ τ ⇈ As ]t) σ ⟩
--   t [ π₁ τ ⇈ As ]t [ σ ⇈ As [ π₁ τ ]l ]t   ∎
--   where open ≅-Reasoning
-- []tm≡[]t ∅ t (π₁ (π₁ σ)) = refl
-- []tm≡[]t (As , A) t (π₁ (π₁ σ)) = refl
-- []tm≡[]t ∅ t (τ ∘ σ) = begin
--   t [ τ ∘ σ ⇈ ∅ ]tm                      ≡⟨ [∘]tm ⟩
--   t [ τ ⇈ ∅ ]tm [ σ ⇈ ∅ ]tm              ≡⟨ cong (λ t' → t' [ σ ⇈ ∅ ]tm) ([]tm≡[]t ∅ t τ)  ⟩
--   t [ τ ⇈ ∅ ]t [ σ ⇈ ∅ ]tm               ≡⟨ []tm≡[]t ∅ (t [ τ ⇈ ∅ ]t) σ ⟩
--   t [ τ ⇈ ∅ ]t [ σ ⇈ ∅ ]t                ∎
--   where open ≡-Reasoning
-- []tm≡[]t As@(_ , _) t (τ ∘ σ) = begin
--   t [ τ ∘ σ ⇈ As ]tm                     ≡⟨ [∘]tm ⟩
--   t [ τ ⇈ As ]tm [ σ ⇈ As [ τ ]l ]tm     ≡⟨ cong (λ t' → t' [ σ ⇈ As [ τ ]l ]tm) ([]tm≡[]t As t τ)  ⟩
--   t [ τ ⇈ As ]t [ σ ⇈ As [ τ ]l ]tm      ≡⟨ []tm≡[]t (As [ τ ]l) (t [ τ ⇈ As ]t) σ ⟩
--   t [ τ ⇈ As ]t [ σ ⇈ As [ τ ]l ]t                ∎
--   where open ≡-Reasoning
-- []tm≡[]t ∅ t (π₁ (σ , u)) = ≅-to-≡ $ begin
--   t [ π₁ (σ , u) ⇈ ∅ ]tm                 ≅⟨ HEq.cong (λ σ' → t [ σ' ⇈ ∅ ]tm) (≡-to-≅ π₁,) ⟩
--   t [ σ ⇈ ∅ ]tm                          ≡⟨ []tm≡[]t ∅ t σ ⟩
--   t [ σ ⇈ ∅ ]t                           ∎
--   where open ≅-Reasoning
-- []tm≡[]t As@(_ , _) t (π₁ (σ , u)) = refl
-- -}

coh[idS∘]
  : [ As ⇈ idS ⨟ σ ] A ≡ [ As ⇈ σ ] A
coh[idS∘] = refl

coh[∘idS]
  : [ As ⇈ σ ⨟ idS ] A ≡ [ As ⇈ σ ] A
coh[∘idS] = refl

coh[assocS]
  : [ As ⇈ (σ ⨟ τ) ⨟ γ ] A ≡ [ As ⇈ σ ⨟ (τ ⨟ γ) ] A
coh[assocS] = refl

module _ (σ : Sub Γ Δ) (τ : Sub Δ Θ) (A : Ty Θ) (t : Tm Δ ([ τ ] A)) where
  open ≡-Reasoning
  coh[⨟∘]l
    : (As : Lift (Θ , A))
    → [ σ ⨟ (τ , t) ]l As ≅ [ σ ⨟ τ , [ σ ]t t ]l As
  coh[⨟∘]'
    : (As : Lift (Θ , A))
    → [ σ ⨟ (τ , t) ]l As ≅ [ σ ⨟ τ , [ σ ]t t ]l As
    → (B : Ty ((Θ , A) ++ As))
    → [ As ⇈ σ ⨟ (τ , t) ] B ≅ [ As ⇈ (σ ⨟ τ) , [ σ ]t t ] B

  coh[⨟∘]l ∅        = refl
  coh[⨟∘]l (As , A) = hcong₂ _,_ (coh[⨟∘]l As) (coh[⨟∘]' As (coh[⨟∘]l As) A)

  coh[⨟∘]' As eq U       = cong-U (hcong (Γ ++_) eq)
  coh[⨟∘]' As eq (Π B C) = icong₂ Ty (cong (Γ ++_) (≅-to-≡ eq)) Π
    (coh[⨟∘]' As eq B)
    (coh[⨟∘]' (As , B) (hcong₂ _,_ eq (coh[⨟∘]' As eq B)) C)

coh[βπ₁] : [ As ⇈ π₁ (σ , t) ] A ≡ [ As ⇈ σ ] A
coh[βπ₁] = refl

-- {-
-- coh[βπ₂] : π₂ (σ , t) [ τ ⇈ As ]tm ≡ t [ τ ⇈ As ]tm
-- coh[βπ₂] {As = As} {σ = σ} {t = t} {τ = τ} = begin
--   π₂ (σ , t) [ τ ⇈ As ]tm        ≡⟨ cong (λ t' → t' [ τ ⇈ As ]tm) π₂, ⟩
--   t [ τ ⇈ As ]tm                 ∎
--   where open ≡-Reasoning
-- -}

module _ {Γ Δ : Ctx} where 
  open ≅-Reasoning
  coh[η,]l
    : (As : Lift (Δ , A)) (σ : Sub Γ (Δ , A)) → [ σ ]l As ≅ [ π₁ σ , π₂ σ ]l As
  coh[η,] 
    : {A' : Ty Δ} (As : Lift (Δ , A')) (σ : Sub Γ (Δ , A'))
    → [ σ ]l As ≅ [ π₁ σ , π₂ σ ]l As
    → (A : Ty ((Δ , A') ++ As))
    → [ As ⇈ σ ] A ≅ [ As ⇈ π₁ σ , π₂ σ ] A

  coh[η,]l ∅        σ = refl
  coh[η,]l (As , A) σ = hcong₂ _,_ (coh[η,]l As σ) (coh[η,] As σ (coh[η,]l As σ) A)

  coh[η,] As σ eq U       = cong-U (hcong (Γ ++_) eq)
  coh[η,] As σ eq (Π A B) = icong₂ Ty (cong (Γ ++_) (≅-to-≡ eq)) Π
    (coh[η,] As σ eq A)
    (coh[η,] (As , A) σ (hcong₂ _,_ eq (coh[η,] As σ eq A)) B)

module _ {Γ : Ctx} (σ : Sub Γ ∅) where
  open ≅-Reasoning

  coh[η∅]l : (As : Lift ∅)
    → [ σ ]l As ≅ [ ∅ {Γ} ]l As
  coh[η∅] : (As : Lift ∅) → [ σ ]l As ≅ [ ∅ {Γ} ]l As
    → (A : Ty (∅ ++ As))
    → [ As ⇈ σ ] A ≅ [ As ⇈ (∅ {Γ}) ] A 

  coh[η∅]l ∅        = refl
  coh[η∅]l (As , A) = hcong₂ _,_ (coh[η∅]l As) (coh[η∅] As (coh[η∅]l As) A)

  coh[η∅] As eq U       = cong-U (hcong (Γ ++_) eq)
  coh[η∅] As eq (Π A B) = icong₂ Ty (cong (Γ ++_) (≅-to-≡ eq)) Π
    (coh[η∅] As eq A)
    (coh[η∅] (As , A) ((hcong₂ _,_ eq (coh[η∅] As eq A))) B)

  coh[η∅]' : (As : Lift ∅) → (A : Ty (∅ ++ As))
    → [ As ⇈ σ ] A ≅ [ As ⇈ (∅ {Γ}) ] A 
  coh[η∅]' As A = coh[η∅] As (coh[η∅]l As) A

π₂∘ : (σ : Sub Γ Δ) (τ : Sub Δ (Θ , A))
  → π₂ (σ ⨟ τ) ≡ [ σ ]t (π₂ τ)
π₂∘ {Γ} {Δ} {Θ} {A} σ τ = ≅-to-≡ $ begin
  π₂ (σ ⨟ τ)                      ≅⟨ hcong (λ ν → π₂ (σ ⨟ ν)) (≡-to-≅ η,) ⟩
  π₂ (σ ⨟ (π₁ τ , π₂ τ))          ≅⟨ hcong π₂ (≡-to-≅ ,∘) ⟩
  π₂ ((σ ⨟ π₁ τ) , [ σ ]t (π₂ τ)) ≡⟨ π₂, ⟩
  [ σ ]t π₂ τ ∎
  where open ≅-Reasoning

-- vs (vs ... (vs vz) ...) = π₂ idS [ π₁ idS ]tm .... [ π₁ idS ]tm
vz:= : Tm Γ A → Sub Γ (Γ , A)
vz:= t = idS , t

