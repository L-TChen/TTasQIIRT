-- inductive-inductive-recursive definition of context, type, term, and type substitution

module SC+Pi.QIIRT-Lift2.Base where
 
open import Prelude
  hiding (_,_)

infixr 20 [_]l_ [_⇈_]_ [_]_ [_⇈_]t_ [_]t_
infixl 10 _⨟_
infixl 10 _++_
infixl 6 _,_

interleaved mutual
  data Ctx  : Set
  data Lift (Γ : Ctx) : Set
  data Ty   (Γ : Ctx) : Set
  data Sub  (Γ : Ctx) : Ctx → Set
  data Tm  : (Γ : Ctx) → Ty Γ → Set
  
  variable
      Γ Δ Θ Φ : Ctx
      Ξ       : Lift Γ
      A B C   : Ty Γ
      t u     : Tm Γ A
      σ τ γ υ : Sub Γ Δ

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
    ,[]l : [ σ ]l (Ξ , A) ≡ [ σ ]l Ξ , [ Ξ ⇈ σ ] A
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
      : {Γ Δ : Ctx} (Ξ : Lift Δ) (σ : Sub Γ Δ) {A : Ty (Δ ++ Ξ)}
      → Tm (Δ ++ Ξ)        A
      → Tm (Γ ++ [ σ ]l Ξ) ([ Ξ ⇈ σ ] A)
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

  [ idS        ] A = A
  [ σ ∘ τ      ] A = [ σ ] [ τ ] A
  [ π₁ (σ , t) ] A = [ σ ] A
  [ π₁ (τ ∘ σ) ] A = [ π₁ τ ] [ σ ] A
  [ σ ] U          = U
  [ σ ] (Π A B)    = Π (A [ σ ]) (B [ σ ↑ A ])

-}
  postulate
    [idS]l : [ idS        ]l Ξ ≡ Ξ
    [∘]l   : [ σ ⨟ τ      ]l Ξ ≡ [ σ ]l [ τ ]l Ξ
    [π₁,]l : [ π₁ (σ , t) ]l Ξ ≡ [ σ ]l Ξ
    [π₁∘]l : [ π₁ (σ ⨟ τ) ]l Ξ ≡ [ σ ]l [ π₁ τ ]l Ξ
    {-# REWRITE [idS]l [∘]l [π₁,]l [π₁∘]l #-}

    [id]  : [ Ξ ⇈ idS ]        A ≡ A
    [∘]   : [ Ξ ⇈ (σ ⨟ τ) ]    A ≡  [ [ τ ]l Ξ ⇈ σ ] [ Ξ ⇈ τ ] A
    [π₁,] : [ Ξ ⇈ π₁ (σ , t) ] A ≡ [ Ξ ⇈ σ ] A
    [π₁⨟] : [ Ξ ⇈ π₁ (σ ⨟ τ) ] A ≡ [ [ π₁ τ ]l Ξ ⇈ σ ] [ Ξ ⇈ π₁ τ ] A
    {-# REWRITE [id] [∘] [π₁,] [π₁⨟] ,[]l #-}

  postulate
  -- Equality constructors for terms
    [id]t : [ Ξ ⇈ idS   ]t t ≡ t
    [∘]t  : [ Ξ ⇈ σ ⨟ τ ]t t ≡ [ [ τ ]l Ξ ⇈ σ ]t [ Ξ ⇈ τ ]t t

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
      : [ Ξ ⇈ σ ] U ≡ U

    {-# REWRITE U[] #-}

  U[∅] : [ σ ] U ≡ U -- Why is this an instance of U[∅]?
  U[∅] = refl

  U[,] : [ Ξ , A ⇈ σ ] U ≡ U
  U[,] = refl

  postulate
    Π[]
      : [ Ξ ⇈ σ ] Π A B ≡ Π ([ Ξ ⇈ σ ] A) ([ (Ξ , A) ⇈ σ ] B)
    {-# REWRITE Π[] #-}

  Π[∅] -- [TODO] Why is this an instance of Π[]?
    : [ σ ] Π A B ≡ Π ([ σ ] A) ([ ∅ , A ⇈ σ ] B)
  Π[∅] = refl

  Π[,] -- [TODO] Why is this not an instance of Π[]?
    : [ Ξ , A ⇈ σ ] Π B C ≡ Π ([ Ξ , A ⇈ σ ] B) ([ Ξ , A , B ⇈ σ ] C)
  Π[,] = refl

cong-U : Γ ≅ Δ → U {Γ} ≅ U {Δ}
cong-U refl = refl

-- derived computation rules on composition
π₁∘ : (σ : Sub Γ Δ) (τ : Sub Δ (Θ , A)) → π₁ (σ ⨟ τ) ≡ σ ⨟ π₁ τ
π₁∘ σ τ = begin
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
  : [ Ξ ⇈ idS ⨟ σ ] A ≡ [ Ξ ⇈ σ ] A
coh[idS∘] = refl

coh[∘idS]
  : [ Ξ ⇈ σ ⨟ idS ] A ≡ [ Ξ ⇈ σ ] A
coh[∘idS] = refl

coh[assocS]
  : [ Ξ ⇈ (σ ⨟ τ) ⨟ γ ] A ≡ [ Ξ ⇈ σ ⨟ (τ ⨟ γ) ] A
coh[assocS] = refl

module _ (σ : Sub Γ Δ) (τ : Sub Δ Θ) (A : Ty Θ) (t : Tm Δ ([ τ ] A)) where
  open ≡-Reasoning
  coh[⨟∘]l
    : (Ξ : Lift (Θ , A))
    → [ σ ⨟ (τ , t) ]l Ξ ≅ [ σ ⨟ τ , [ σ ]t t ]l Ξ
  coh[⨟∘]'
    : (Ξ : Lift (Θ , A))
    → [ σ ⨟ (τ , t) ]l Ξ ≅ [ σ ⨟ τ , [ σ ]t t ]l Ξ
    → (B : Ty ((Θ , A) ++ Ξ))
    → [ Ξ ⇈ σ ⨟ (τ , t) ] B ≅ [ Ξ ⇈ (σ ⨟ τ) , [ σ ]t t ] B

  coh[⨟∘]l ∅        = refl
  coh[⨟∘]l (Ξ , A) = hcong₂ _,_ (coh[⨟∘]l Ξ) (coh[⨟∘]' Ξ (coh[⨟∘]l Ξ) A)

  coh[⨟∘]' Ξ eq U       = cong-U (hcong (Γ ++_) eq)
  coh[⨟∘]' Ξ eq (Π B C) = icong₂ Ty (cong (Γ ++_) (≅-to-≡ eq)) Π
    (coh[⨟∘]' Ξ eq B)
    (coh[⨟∘]' (Ξ , B) (hcong₂ _,_ eq (coh[⨟∘]' Ξ eq B)) C)

coh[βπ₁] : [ Ξ ⇈ π₁ (σ , t) ] A ≡ [ Ξ ⇈ σ ] A
coh[βπ₁] = refl

-- {-
-- coh[βπ₂] : π₂ (σ , t) [ τ ⇈ Ξ ]tm ≡ t [ τ ⇈ Ξ ]tm
-- coh[βπ₂] {Ξ = Ξ} {σ = σ} {t = t} {τ = τ} = begin
--   π₂ (σ , t) [ τ ⇈ Ξ ]tm        ≡⟨ cong (λ t' → t' [ τ ⇈ Ξ ]tm) π₂, ⟩
--   t [ τ ⇈ Ξ ]tm                 ∎
--   where open ≡-Reasoning
-- -}

module _ {Γ Δ : Ctx} {A : Ty Δ} (σ : Sub Γ (Δ , A)) where 
  open ≅-Reasoning
  coh[η,]l
    : (Ξ : Lift (Δ , A)) → [ σ ]l Ξ ≅ [ π₁ σ , π₂ σ ]l Ξ
  coh[η,] 
    : (Ξ : Lift (Δ , A))
    → [ σ ]l Ξ ≅ [ π₁ σ , π₂ σ ]l Ξ
    → (B : Ty ((Δ , A) ++ Ξ))
    → [ Ξ ⇈ σ ] B ≅ [ Ξ ⇈ π₁ σ , π₂ σ ] B

  coh[η,]l ∅       = refl
  coh[η,]l (Ξ , A) = hcong₂ _,_ (coh[η,]l Ξ) (coh[η,] Ξ (coh[η,]l Ξ) A)

  coh[η,] Ξ eq U       = cong-U (hcong (Γ ++_) eq)
  coh[η,] Ξ eq (Π A B) = icong₂ Ty (cong (Γ ++_) (≅-to-≡ eq)) Π
    (coh[η,] Ξ eq A)
    (coh[η,] (Ξ , A) (hcong₂ _,_ eq (coh[η,] Ξ eq A)) B)

module _ {Γ : Ctx} (σ : Sub Γ ∅) where
  open ≅-Reasoning

  coh[η∅]l : (Ξ : Lift ∅)
    → [ σ ]l Ξ ≅ [ ∅ {Γ} ]l Ξ
  coh[η∅] : (Ξ : Lift ∅) → [ σ ]l Ξ ≅ [ ∅ {Γ} ]l Ξ
    → (A : Ty (∅ ++ Ξ))
    → [ Ξ ⇈ σ ] A ≅ [ Ξ ⇈ (∅ {Γ}) ] A 

  coh[η∅]l ∅        = refl
  coh[η∅]l (Ξ , A) = hcong₂ _,_ (coh[η∅]l Ξ) (coh[η∅] Ξ (coh[η∅]l Ξ) A)

  coh[η∅] Ξ eq U       = cong-U (hcong (Γ ++_) eq)
  coh[η∅] Ξ eq (Π A B) = icong₂ Ty (cong (Γ ++_) (≅-to-≡ eq)) Π
    (coh[η∅] Ξ eq A)
    (coh[η∅] (Ξ , A) ((hcong₂ _,_ eq (coh[η∅] Ξ eq A))) B)

  coh[η∅]' : (Ξ : Lift ∅) → (A : Ty (∅ ++ Ξ))
    → [ Ξ ⇈ σ ] A ≅ [ Ξ ⇈ (∅ {Γ}) ] A 
  coh[η∅]' Ξ A = coh[η∅] Ξ (coh[η∅]l Ξ) A

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
