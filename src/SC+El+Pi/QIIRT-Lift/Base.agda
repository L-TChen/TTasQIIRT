module SC+El+Pi.QIIRT-Lift.Base where
 
open import Prelude
  hiding (_,_)

infixr 20 [_]l_ [_⇈_]_ [_]_ [_⇈_]t_ [_]t_ [_⇈_]tm_ [_]tm_
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
    ∅[]l : [ σ ]l ∅       ≡ ∅
    -- [TODO]: Making this a function cannot pass the local confluence check. Why?
    ,[]l : [ σ ]l (Ξ , A) ≡ [ σ ]l Ξ , [ Ξ ⇈ σ ] A
    {-# REWRITE ∅[]l #-}

  [_]_ : (σ : Sub Γ Δ) (A : Ty Δ) → Ty Γ
  [ σ ] A = [ ∅ ⇈ σ ] A

  data _ where
    U
      : Ty Γ
    Π
      : (A : Ty Γ) → Ty (Γ , A)
      → Ty Γ
    El
      : Tm Γ U
      → Ty Γ
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
    [_⇈_]tm_
      : {Γ Δ : Ctx} (Ξ : Lift Δ) (σ : Sub Γ Δ) {A : Ty (Δ ++ Ξ)}
      → Tm (Δ ++ Ξ)        A
      → Tm (Γ ++ [ σ ]l Ξ) ([ Ξ ⇈ σ ] A)
    abs
      : Tm (Γ , A) B → Tm Γ (Π A B)
    app
      : Tm Γ (Π A B) → Tm (Γ , A) B
  pattern wk   = π₁ idS
  pattern vz   = π₂ idS
  pattern vs x = [ ∅ ⇈ wk ]tm x

  [_]tm_
      : {Γ Δ : Ctx} (σ : Sub Γ Δ) {A : Ty Δ}
      → Tm Δ A
      → Tm Γ ([ σ ] A)
  [ σ ]tm u = [ ∅ ⇈ σ ]tm u

{-
  We'd like to define _[_] by overlapping patterns

  [ idS        ] A = A
  [ σ ⨟ τ      ] A = [ σ ] [ τ ] A
  [ π₁ (σ , t) ] A = [ σ ] A
  [ π₁ (τ ⨟ σ) ] A = [ π₁ τ ] [ σ ] A
  [ σ ] U          = U
  [ σ ] (Π A B)    = Π (A [ σ ]) (B [ σ ↑ A ])
  [ σ ] (El u)     = El ([ σ ]t u)
-}

  postulate
    [idS]l : [ idS        ]l Ξ ≡ Ξ
    [⨟]l   : [ σ ⨟ τ      ]l Ξ ≡ [ σ ]l [ τ ]l Ξ
    [π₁,]l : [ π₁ (σ , t) ]l Ξ ≡ [ σ ]l Ξ
    {-# REWRITE [idS]l [⨟]l [π₁,]l #-}
    [π₁idS⨟]l : [ π₁ (idS ⨟ τ) ]l Ξ ≡ [ π₁ τ ]l Ξ
    {-# REWRITE [π₁idS⨟]l #-}
--    [π₁⨟]l : [ π₁ (σ ⨟ τ) ]l Ξ ≡ [ σ ]l [ π₁ τ ]l Ξ
--    {-# REWRITE [π₁⨟]l #-}


    [id]  : [ Ξ ⇈ idS ]        A ≡ A
    [⨟]   : [ Ξ ⇈ (σ ⨟ τ) ]    A ≡  [ [ τ ]l Ξ ⇈ σ ] [ Ξ ⇈ τ ] A
    [π₁,] : [ Ξ ⇈ π₁ (σ , t) ] A ≡ [ Ξ ⇈ σ ] A
    {-# REWRITE [id] [⨟] [π₁,] #-}
    [π₁idS⨟] : [ Ξ ⇈ π₁ (idS ⨟ τ) ] A ≡ [ Ξ ⇈ π₁ τ ] A
    {-# REWRITE [π₁idS⨟] #-}
--    [π₁⨟] : [ Ξ ⇈ π₁ (σ ⨟ τ) ] A ≡ [ [ π₁ τ ]l Ξ ⇈ σ ] [ Ξ ⇈ π₁ τ ] A
--    {-# REWRITE [π₁⨟] #-}
    {-# REWRITE ,[]l #-}

  [_⇈_]t_ : {Γ Δ : Ctx} (Ξ : Lift Δ) (σ : Sub Γ Δ) {A : Ty (Δ ++ Ξ)}
    → Tm (Δ ++ Ξ)        A
    → Tm (Γ ++ [ σ ]l Ξ) ([ Ξ ⇈ σ ] A)
  [ Ξ ⇈ idS        ]t u = u
  [ Ξ ⇈ σ ⨟ τ      ]t u = [ [ τ ]l Ξ ⇈ σ ]t [ Ξ ⇈ τ ]t u
  [ Ξ ⇈ π₁ (σ , t) ]t u = [ Ξ ⇈ σ ]t u
  [ Ξ ⇈ π₁ (idS ⨟ τ) ]t u = [ Ξ ⇈ π₁ τ ]t u
  {-# CATCHALL #-}
  [ Ξ ⇈ σ          ]t u = [ Ξ ⇈ σ ]tm u

  [_]t_
    : (σ : Sub Γ Δ) {A : Ty Δ}
    → Tm Δ A
    → Tm Γ ([ σ ] A)
  [ σ ]t t = [ ∅ ⇈ σ ]t t
  
  postulate
  -- Equality constructors for terms
    [id]t : [ Ξ ⇈ idS   ]tm t ≡ t
    [⨟]t  : [ Ξ ⇈ σ ⨟ τ ]tm t ≡ [ [ τ ]l Ξ ⇈ σ ]tm [ Ξ ⇈ τ ]tm t

  -- Equality constructors for substitutions
    _⨟idS
      : (σ : Sub Γ Δ)
      → σ ⨟ idS ≡ σ
    idS⨟_
      : (σ : Sub Γ Δ)
      → idS ⨟ σ ≡ σ
    assocS
      : (υ ⨟ τ) ⨟ σ ≡ υ ⨟ (τ ⨟ σ)
    π₁,
      : π₁ (σ , t) ≡ σ
    π₂,
      : {σ : Sub Γ Δ}{A : Ty Δ}{t : Tm Γ ([ σ ] A)}
      →  π₂ (σ , t) ≡ t 
    ,⨟
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

    Π[]
      : [ Ξ ⇈ σ ] Π A B ≡ Π ([ Ξ ⇈ σ ] A) ([ (Ξ , A) ⇈ σ ] B)
    {-# REWRITE Π[] #-}

    El[]
      : {Ξ : Lift Δ} (σ : Sub Γ Δ) (u : Tm (Δ ++ Ξ) U)
      → [ Ξ ⇈ σ ] (El u) ≡ El ([ Ξ ⇈ σ ]t u)
    {-# REWRITE El[] #-}

cong-U : Γ ≅ Δ → U {Γ} ≅ U {Δ}
cong-U refl = refl

-- derived computation rules on composition
π₁⨟ : (σ : Sub Γ Δ) (τ : Sub Δ (Θ , A)) → π₁ (σ ⨟ τ) ≡ σ ⨟ π₁ τ
π₁⨟ σ τ = begin
  π₁ (σ ⨟ τ)                    ≡⟨ cong (λ τ → π₁ (σ ⨟ τ)) η, ⟩
  π₁ (σ ⨟ (π₁ τ , π₂ τ))        ≡⟨ cong π₁ ,⨟ ⟩ 
  π₁ (σ ⨟ π₁ τ , [ σ ]t π₂ τ)   ≡⟨ π₁, ⟩
  σ ⨟ π₁ τ                      ∎
  where open ≡-Reasoning

π₁idS⨟ : (τ : Sub Δ (Θ , A)) → π₁ (idS ⨟ τ) ≡ π₁ τ
π₁idS⨟ τ = begin
  π₁ (idS ⨟ τ) ≡⟨ π₁⨟ idS τ ⟩
  idS ⨟ π₁ τ   ≡⟨ (idS⨟ π₁ τ) ⟩
  π₁ τ         ∎
  where open ≡-Reasoning

[]tm≡[]t : (Ξ : Lift Δ){A : Ty (Δ ++ Ξ)}(u : Tm (Δ ++ Ξ) A)(σ : Sub Γ Δ)
  → [ Ξ ⇈ σ ]tm u ≡ [ Ξ ⇈ σ ]t u
[]tm≡[]t Ξ u ∅            = refl
[]tm≡[]t Ξ u (σ , t)      = refl
[]tm≡[]t Ξ u wk           = refl
[]tm≡[]t Ξ u (π₁ (π₁ σ))  = refl
[]tm≡[]t Ξ u (π₁ (∅ ⨟ τ))       = refl
[]tm≡[]t Ξ u (π₁ ((σ , t) ⨟ τ)) = refl
[]tm≡[]t Ξ u (π₁ (σ ⨟ σ₁ ⨟ τ))  = refl
[]tm≡[]t Ξ u (π₁ (π₁ σ ⨟ τ))    = refl
[]tm≡[]t Ξ u idS          = [id]t
[]tm≡[]t Ξ u (_⨟_ {Δ = Θ} σ τ) = begin
  [ Ξ ⇈ σ ⨟ τ ]tm u                ≡⟨ [⨟]t ⟩
  [ [ τ ]l Ξ ⇈ σ ]tm [ Ξ ⇈ τ ]tm u ≡⟨ cong ([ [ τ ]l Ξ ⇈ σ ]tm_) ([]tm≡[]t Ξ u τ) ⟩
  [ [ τ ]l Ξ ⇈ σ ]tm [ Ξ ⇈ τ ]t  u ≡⟨ []tm≡[]t ([ τ ]l Ξ) ([ Ξ ⇈ τ ]t u) σ ⟩
  [ [ τ ]l Ξ ⇈ σ ]t  [ Ξ ⇈ τ ]t  u ∎
  where open ≡-Reasoning
[]tm≡[]t {Γ} {Δ} Ξ u (π₁ (σ , t)) = ≅-to-≡ $ begin
  [ Ξ ⇈ π₁ (σ , t) ]tm u ≅⟨ hcong (λ σ → [ Ξ ⇈ σ ]tm u) (≡-to-≅ π₁,) ⟩
  [ Ξ ⇈ σ ]tm u          ≡⟨ []tm≡[]t Ξ u σ ⟩
  [ Ξ ⇈ σ ]t  u          ∎
  where open ≅-Reasoning
[]tm≡[]t Ξ u (π₁ (idS ⨟ τ)) = ≅-to-≡ $ begin
  [ Ξ ⇈ π₁ (idS ⨟ τ) ]tm u  ≅⟨ hcong (λ σ → [ Ξ ⇈ σ ]tm u) (≡-to-≅ (π₁idS⨟ τ)) ⟩
  [ Ξ ⇈ π₁ τ ]tm u          ≡⟨ []tm≡[]t Ξ u (π₁ τ) ⟩
  [ Ξ ⇈ π₁ τ ]t  u          ∎
  where open ≅-Reasoning

coh[idS⨟]
  : [ Ξ ⇈ idS ⨟ σ ] A ≡ [ Ξ ⇈ σ ] A
coh[idS⨟] = refl

coh[⨟idS]
  : [ Ξ ⇈ σ ⨟ idS ] A ≡ [ Ξ ⇈ σ ] A
coh[⨟idS] = refl

coh[assocS]
  : [ Ξ ⇈ (σ ⨟ τ) ⨟ γ ] A ≡ [ Ξ ⇈ σ ⨟ (τ ⨟ γ) ] A
coh[assocS] = refl

module _ (σ : Sub Γ Δ) (τ : Sub Δ Θ) (A : Ty Θ) (t : Tm Δ ([ τ ] A)) where
  open ≅-Reasoning
  coh[⨟,]l
    : (Ξ : Lift (Θ , A))
    → [ σ ⨟ (τ , t) ]l Ξ ≅ [ σ ⨟ τ , [ σ ]t t ]l Ξ
  coh[⨟,]'
    : (Ξ : Lift (Θ , A))
    → [ σ ⨟ (τ , t) ]l Ξ ≅ [ σ ⨟ τ , [ σ ]t t ]l Ξ
    → (B : Ty ((Θ , A) ++ Ξ))
    → [ Ξ ⇈ σ ⨟ (τ , t) ] B ≅ [ Ξ ⇈ (σ ⨟ τ) , [ σ ]t t ] B

  coh[⨟,]l ∅        = refl
  coh[⨟,]l (Ξ , A) = hcong₂ _,_ (coh[⨟,]l Ξ) (coh[⨟,]' Ξ (coh[⨟,]l Ξ) A)

  coh[⨟,]' Ξ eq U       = cong-U (hcong (Γ ++_) eq)
  coh[⨟,]' Ξ eq (Π B C) = icong₂ Ty (cong (Γ ++_) (≅-to-≡ eq)) Π
    (coh[⨟,]' Ξ eq B)
    (coh[⨟,]' (Ξ , B) (hcong₂ _,_ eq (coh[⨟,]' Ξ eq B)) C)
  coh[⨟,]' Ξ eq (El u)  = {!!}


coh[βπ₁] : [ Ξ ⇈ π₁ (σ , t) ] A ≡ [ Ξ ⇈ σ ] A
coh[βπ₁] = refl

coh[βπ₂] : [ Ξ ⇈ τ ]t π₂ (σ , t) ≡ [ Ξ ⇈ τ ]t t
coh[βπ₂] = {! !}
  where open ≡-Reasoning

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
  coh[η,] Ξ eq (El u)  = {!!}

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
  coh[η∅] Ξ eq (El u)  = {!!}

π₂⨟ : (σ : Sub Γ Δ) (τ : Sub Δ (Θ , A))
  → π₂ (σ ⨟ τ) ≡ {![ σ ]t (π₂ τ)!} -- yep, we need transport here.
π₂⨟ = {!!}
--π₂⨟ {Γ} {Δ} {Θ} {A} σ τ = ≅-to-≡ $ begin
--  π₂ (σ ⨟ τ)                      ≅⟨ hcong (λ ν → π₂ (σ ⨟ ν)) (≡-to-≅ η,) ⟩
--  π₂ (σ ⨟ (π₁ τ , π₂ τ))          ≅⟨ hcong π₂ (≡-to-≅ ,⨟) ⟩
--  π₂ ((σ ⨟ π₁ τ) , [ σ ]t (π₂ τ)) ≡⟨ π₂, ⟩
--  [ σ ]t π₂ τ ∎
--  where open ≅-Reasoning

-- vs (vs ... (vs vz) ...) = π₂ idS [ π₁ idS ]tm .... [ π₁ idS ]tm
vz:= : Tm Γ A → Sub Γ (Γ , A)
vz:= t = idS , t
