-- Type theory as a quotient inductive-inductive-recursive type, inspired by the formualtion of natural models
-- whereas the recursion part is impredicative.


-- See https://github.com/agda/agda/issues/5362 for the current limitation of Agda
-- that affacts the definition of our encoding

open import Prelude
  hiding (tt)

module Theory.SC.QIIRT-natural2.Syntax where
  
module Foo where
  infixl 8 _[_] _[_]T _[_]t
  infixr 10 _∘_
  infixl 4 _,_ _,_∶[_]

  data Ctx : Set
  data Sub : (Γ Δ : Ctx) → Set
  data Ty  : Ctx → Set
  data Tm  : (Γ : Ctx) → Set

  variable
      Γ Δ Θ Ξ : Ctx
      A B C : Ty Γ
      t u   : Tm Γ
      σ τ δ : Sub Γ Δ

  tyOf
    : Tm Γ → Ty Γ

  -- Substitution calculus part
  data Ctx where
    ∅
      : Ctx
    _,_
      : (Γ : Ctx)(A : Ty Γ)
      → Ctx
  _[_]T
    : (A : Ty Δ)(σ : Sub Γ Δ)
    → Ty Γ
  _[_]t
    : (A : Tm Δ)(σ : Sub Γ Δ)
    → Tm Γ
  ∅S
    : Sub Γ ∅
  _,_∶[_]
    : (σ : Sub Γ Δ) (t : Tm Γ) → tyOf t ≡ A [ σ ]T
    → Sub Γ (Δ , A)
  idS
    : Sub Γ Γ
  _∘_
    : Sub Δ Θ → Sub Γ Δ
    → Sub Γ Θ
  π₁
    : Sub Γ (Δ , A)
    → Sub Γ Δ
  π₂
    : Sub Γ (Δ , A)
    → Tm Γ

  tyOfπ₂ -- should be definitional after the datatype declaration
    : (σ : Sub Γ (Δ , A))
    → tyOf (π₂ σ) ≡ A [ π₁ σ ]T
  tyOfπ₂idS
    : tyOf (π₂ idS) ≡ A [ σ ∘ π₁ idS ]T

  _↑_
    : (σ : Sub Γ Δ) (A : Ty Δ)
    → Sub (Γ , A [ σ ]T) (Δ , A)
  σ ↑ A = σ ∘ π₁ idS , π₂ idS ∶[ tyOfπ₂idS ]

  idS∘_
    : (σ : Sub Γ Δ)
    → idS ∘ σ ≡ σ
  _∘idS
    : (σ : Sub Γ Δ)
    → σ ∘ idS ≡ σ
  assocS
    : (σ : Sub Γ Δ) (τ : Sub Δ Θ) (γ : Sub Θ Ξ)
    → (γ ∘ τ) ∘ σ ≡ γ ∘ (τ ∘ σ)
  ,∘
    : (σ : Sub Δ Θ) (t : Tm Δ) (τ : Sub Γ Δ) (p : tyOf t ≡ A [ σ ]T)
      (q : tyOf (t [ τ ]t) ≡ A [ σ ∘ τ ]T)
    → (σ , t ∶[ p ]) ∘ τ ≡ (σ ∘ τ , t [ τ ]t ∶[ q ])

  ηπ
    : (σ : Sub Γ (Δ , A))
    → σ ≡ (π₁ σ , π₂ σ ∶[ tyOfπ₂ σ ])
  η∅
    : (σ : Sub Γ ∅)
    → σ ≡ ∅S
  βπ₁
    : (σ : Sub Γ Δ) (t : Tm Γ) (p : tyOf t ≡ A [ σ ]T)
    → π₁ (σ , t ∶[ p ]) ≡ σ
  βπ₂
    : (σ : Sub Γ Δ) (t : Tm Γ) (p : tyOf t ≡ A [ σ ]T)
    → (q : A [ π₁ (σ , t ∶[ p ]) ]T ≡  tyOf t)
    → π₂ (σ , t ∶[ p ]) ≡ t
  [idS]T
    : A ≡ A [ idS ]T
  [∘]T
    : (A : Ty Θ) (σ : Sub Γ Δ) (τ : Sub Δ Θ)
    → A [ τ ]T [ σ ]T ≡ A [ τ ∘ σ ]T
  [idS]t
    : (t : Tm Γ)
    → t ≡ t [ idS ]t
  [∘]t
    : (t : Tm Θ) (σ : Sub Γ Δ) (τ : Sub Δ Θ)
    → t [ τ ]t [ σ ]t ≡ t [ τ ∘ σ ]t

  -- Empty universe
  U
    : Ty Γ
  U[]
    : U [ σ ]T ≡ U
  El
    : (u : Tm Γ) (p : tyOf u ≡ U)
    → Ty Γ
  El[]
    : (τ : Sub Γ Δ) (u : Tm Δ) (p : tyOf u ≡ U) (q : tyOf (u [ τ ]t) ≡ U)
    → (El u p) [ τ ]T ≡ El (u [ τ ]t) q

  -- Π-types
  Π
    : (A : Ty Γ) (B : Ty (Γ , A))
    → Ty Γ
  app
    : (t : Tm Γ) → tyOf t ≡ Π A B
    → Tm (Γ , A)
  abs
    : (t : Tm (Γ , A))
    → Tm Γ
  tyOfabs
    : tyOf (abs t) ≡ Π A (tyOf t)
  Π[]
    : (Π A B) [ σ ]T ≡ Π (A [ σ ]T) (B [ σ ↑ A ]T)
  abs[]
    : (t : Tm (Γ , A))
    → abs t [ σ ]t ≡ abs (t [ σ ↑ A ]t)
  Πβ
    : (t : Tm (Γ , A)) 
    → app (abs t) tyOfabs ≡ t
  Πη
    : (t : Tm Γ) (p : tyOf t ≡ Π A B)
    → abs (app t p) ≡ t

  -- The type of Booleans
  𝔹
    : Ty Γ
  𝔹[]
    : 𝔹 [ σ ]T ≡ 𝔹
  𝔹[]₂
    : tyOf (π₂ idS) ≡ 𝔹 [ τ ]T


  tt ff
    : Tm Γ
  tyOftt : tyOf {Γ} tt ≡ 𝔹 [ idS ]T -- definitional or not
  tyOfff : tyOf {Γ} ff ≡ 𝔹 [ idS ]T -- definitional or not

  _↑𝔹
    : (σ : Sub Γ Δ)
    → Sub (Γ , 𝔹) (Δ , 𝔹)
  σ ↑𝔹 = (σ ∘ π₁ idS) , π₂ idS ∶[ 𝔹[]₂ {τ = σ ∘ π₁ idS} ]


  elim𝔹
    : (P : Ty (Γ , 𝔹)) (t u : Tm Γ)
    → tyOf t ≡ (P [ idS , tt ∶[ tyOftt ] ]T)
    → tyOf u ≡ (P [ idS , ff ∶[ tyOfff ] ]T)
    → (b : Tm Γ) → tyOf b ≡ 𝔹 [ idS ]T
    → Tm Γ
  elim𝔹[]
    : (P : Ty (Γ , 𝔹)) (t u : Tm Γ) (pt : tyOf t ≡ _) (pu : tyOf u ≡ _) → (b : Tm Γ) (pb : tyOf b ≡ 𝔹 [ idS ]T)
    → (pt₂ : tyOf (t [ σ ]t) ≡ P [ σ ↑𝔹 ]T [ idS , tt ∶[ tyOftt ] ]T)
    → (pu₂ : tyOf (u [ σ ]t) ≡ P [ σ ↑𝔹 ]T [ idS , ff ∶[ tyOfff ] ]T)
    → (pb₂ : tyOf (b [ σ ]t) ≡ 𝔹 [ idS ]T)
    → (P [ idS , b ∶[ pb ] ]T [ σ ]T) ≡ (P [ (σ ∘ π₁ idS) , π₂ idS ∶[ 𝔹[]₂ ] ]T [ idS , b [ σ ]t ∶[ pb₂ ] ]T)
    → (elim𝔹 P t u pt pu b pb) [ σ ]t
    ≡ elim𝔹 (P [ σ ↑𝔹 ]T) (t [ σ ]t) (u [ σ ]t) pt₂ pu₂ (b [ σ ]t) pb₂

  -- the following is the actual constructors in Agda
  data Ty where
    _[_] : (A : Ty Δ)(σ : Sub Γ Δ)
      → Ty Γ
    [idS]T'
      : A ≡ A [ idS ]
    [∘]T'
      : (A : Ty Θ) (σ : Sub Γ Δ) (τ : Sub Δ Θ)
      → A [ τ ]T [ σ ]T ≡ A [ τ ∘ σ ]T
    U'
      : Ty Γ
    U[]'
      : U [ σ ]T ≡ U
    El'
      : (u : Tm Γ) (p : tyOf u ≡ U)
      → Ty Γ
    El[]'
      : (τ : Sub Γ Δ) (u : Tm Δ) (p : tyOf u ≡ U) (q : tyOf (u [ τ ]t) ≡ U)
      → (El u p) [ τ ]T ≡ El (u [ τ ]t) q
    Π'
      : (A : Ty Γ) (B : Ty (Γ , A))
      → Ty Γ
    Π[]'
      : (Π A B) [ σ ]T ≡ Π (A [ σ ]T) (B [ σ ↑ A ]T)
    𝔹'
      : Ty Γ
    𝔹[]'
      : 𝔹 [ σ ]T ≡ 𝔹
    𝔹[]₂'
      : tyOf (π₂ idS) ≡ 𝔹 [ τ ]

  data Sub where
    ∅
      : Sub Γ ∅
    _,_∶[_]'
      : (σ : Sub Γ Δ) (t : Tm Γ) → tyOf t ≡ A [ σ ]T
      → Sub Γ (Δ , A)
    idS' : Sub Γ Γ
    _∘'_
      : Sub Δ Θ → Sub Γ Δ
      → Sub Γ Θ
    π₁'
      : Sub Γ (Δ , A)
      → Sub Γ Δ
    βπ₁'
      : (σ : Sub Γ Δ) (t : Tm Γ) (p : tyOf t ≡ A [ σ ]T)
      → π₁ (σ , t ∶[ p ]) ≡ σ
    idS∘'_
      : (σ : Sub Γ Δ)
      → idS ∘ σ ≡ σ
    _∘idS'
      : (σ : Sub Γ Δ)
      → σ ∘ idS ≡ σ
    assocS'
      : (σ : Sub Γ Δ) (τ : Sub Δ Θ) (γ : Sub Θ Ξ)
      → (γ ∘ τ) ∘ σ ≡ γ ∘ (τ ∘ σ)
    ,∘'
      : (σ : Sub Δ Θ) (t : Tm Δ) (τ : Sub Γ Δ) (p : tyOf t ≡ A [ σ ]T)
        (q : tyOf (t [ τ ]t) ≡ A [ σ ∘ τ ]T)
      → (σ , t ∶[ p ]) ∘ τ ≡ (σ ∘ τ , t [ τ ]t ∶[ q ])
    η∅'
      : (σ : Sub Γ ∅)
      → σ ≡ ∅
    ηπ'
      : (σ : Sub Γ (Δ , A))
      → σ ≡ (π₁ σ , π₂ σ ∶[ tyOfπ₂ σ ])
  data Tm where
    _[_] : (A : Tm Δ)(σ : Sub Γ Δ)
      → Tm Γ
    π₂'
      : Sub Γ (Δ , A)
      → Tm Γ
    βπ₂'
      : (σ : Sub Γ Δ) (t : Tm Γ) (p : tyOf t ≡ A [ σ ]T)
      → (q : A [ π₁ (σ , t ∶[ p ]) ]T ≡ tyOf t)
      → π₂ (σ , t ∶[ p ]) ≡ t
    [idS]t'
      : (t : Tm Γ)
      → t ≡ t [ idS ]t
    [∘]t'
      : (t : Tm Θ) (σ : Sub Γ Δ) (τ : Sub Δ Θ)
      → t [ τ ]t [ σ ]t ≡ t [ τ ∘ σ ]t
    app'
      : (t : Tm Γ) → tyOf t ≡ Π A B
      → Tm (Γ , A)
    abs'
      : (t : Tm (Γ , A))
      → Tm Γ
    abs[]'
      : (t : Tm (Γ , A)) 
      → abs t [ σ ]t ≡ abs (t [ σ ↑ A ]t)
    Πβ'
      : (t : Tm (Γ , A))
      → app (abs t) tyOfabs ≡ t
    Πη'
      : (t : Tm Γ) (p : tyOf t ≡ Π A B)
      → abs (app t p) ≡ t
    tt' ff'
      : Tm Γ
    elim𝔹'
      : (P : Ty (Γ , 𝔹)) (t u : Tm Γ)
      → tyOf t ≡ (P [ idS , tt ∶[ tyOftt ] ]T)
      → tyOf u ≡ (P [ idS , ff ∶[ tyOfff ] ]T)
      → (b : Tm Γ) → tyOf b ≡ 𝔹 [ idS ]T
      → Tm Γ
    elim𝔹[]'
      : (P : Ty (Γ , 𝔹)) (t u : Tm Γ) (pt : tyOf t ≡ _) (pu : tyOf u ≡ _) → (b : Tm Γ) (pb : tyOf b ≡ 𝔹 [ idS ]T)
      → (pt₂ : tyOf (t [ σ ]t) ≡ P [ σ ↑𝔹 ]T [ idS , tt ∶[ tyOftt ] ]T)
      → (pu₂ : tyOf (u [ σ ]t) ≡ P [ σ ↑𝔹 ]T [ idS , ff ∶[ tyOfff ] ]T)
      → (pb₂ : tyOf (b [ σ ]t) ≡ 𝔹 [ idS ]T)
      → P [ idS , b ∶[ pb ] ] [ σ ] ≡ P [ (σ ∘ π₁ idS) , π₂ idS ∶[ 𝔹[]₂ ] ] [ idS , b [ σ ] ∶[ pb₂ ] ]
      → (elim𝔹 P t u pt pu b pb) [ σ ]t
      ≡ elim𝔹 (P [ σ ↑𝔹 ]T) (t [ σ ]t) (u [ σ ]t) pt₂ pu₂ (b [ σ ]t) pb₂

  _[_]T = _[_]
  _[_]t = _[_]
  U = U'
  U[] = U[]'
  El = El'
  El[] = El[]'
  Π = Π'
  Π[] = Π[]'
  𝔹 = 𝔹'
  𝔹[] = 𝔹[]'
  𝔹[]₂ = 𝔹[]₂'
  ∅S = ∅
  _,_∶[_] = _,_∶[_]'
  idS = idS'
  _∘_ = _∘'_
  π₁  = π₁'
  π₂  = π₂'
  [idS]T = [idS]T'
  [∘]T = [∘]T'
  βπ₁ = βπ₁'
  βπ₂ = βπ₂'
  idS∘_ = idS∘'_
  _∘idS = _∘idS'
  assocS = assocS'
  ,∘ = ,∘'
  η∅ = η∅'
  ηπ = ηπ'
  [idS]t = [idS]t'
  [∘]t  = [∘]t'
  abs = abs'
  app = app'
  abs[] = abs[]'
  Πβ = Πβ'
  Πη = Πη'
  tt = tt'
  ff = ff'
  elim𝔹 = elim𝔹'
  elim𝔹[] = elim𝔹[]'

  tyOf (t [ σ ]) = tyOf t [ σ ]T
  tyOf (π₂' {Γ} {Δ} {A} σ) = A [ π₁ σ ]T
  tyOf (βπ₂' σ t p q i)   = q i
  tyOf ([idS]t' t i)      = [idS]T {A = tyOf t} i
  tyOf ([∘]t' t σ τ i)    = [∘]T (tyOf t) σ τ i
  tyOf (app' {B = B} t p) = B
  tyOf (abs' {A = A} t)   = Π A (tyOf t)
  tyOf (abs[]' {A = A} {σ = σ} t i) =
    Π[] {A = A} {B = tyOf t} {σ = σ} i
  tyOf (Πβ' t i) = tyOf t
  tyOf (Πη' t p i) = p (~ i)
  tyOf tt' = 𝔹
  tyOf ff' = 𝔹
  tyOf (elim𝔹' P u t pu pt b pb) = P [ idS , b ∶[ pb ] ]T
  tyOf (elim𝔹[]' P u t pu pt b pb pt₂ pu₂ pb₂ q i) = q i

  tyOfπ₂ {Γ} {Δ} {A} σ = refl
  tyOfπ₂idS {A = A} {σ = σ} = [∘]T A (π₁ idS) σ
  tyOfabs = refl
  tyOftt = [idS]T
  tyOfff = [idS]T

  ⟨,∘⟩
    : (σ : Sub Δ Θ) (t : Tm Δ) (τ : Sub Γ Δ) (p : tyOf t ≡ A [ σ ]T)
    → (σ , t ∶[ p ]) ∘ τ ≡ (σ ∘ τ , t [ τ ]t ∶[ cong _[ τ ] p ∙ [∘]T A τ σ ])
  ⟨,∘⟩ σ t τ p = ,∘ σ t τ p (cong (_[ τ ]) p ∙ [∘]T _ τ σ)

  ⟨βπ₂⟩
    : (σ : Sub Γ Δ) (t : Tm Γ) (p : tyOf t ≡ A [ σ ]T)
    → π₂ (σ , t ∶[ p ]) ≡ t
  ⟨βπ₂⟩ {A = A} σ t p = βπ₂ σ t p (cong (A [_]) (βπ₁ σ t p) ∙ sym p)

  ⟨elim𝔹[]⟩
    : (P : Ty (Γ , 𝔹)) (t u : Tm Γ) (pt : tyOf t ≡ _) (pu : tyOf u ≡ _) → (b : Tm Γ) (pb : tyOf b ≡ 𝔹 [ idS ]T)
    → (elim𝔹 P t u pt pu b pb) [ σ ]t
    ≡ elim𝔹 (P [ σ ↑𝔹 ]T) (t [ σ ]t) (u [ σ ]t) {!!} {!!} (b [ σ ]t) (cong _[ σ ]T pb ∙ ([∘]T 𝔹 σ idS ∙ 𝔹[]) ∙ sym 𝔹[])
  ⟨elim𝔹[]⟩ P t u pt pu b pb = elim𝔹[] P t u pt pu b pb _ _ _ {!!}

open Foo public
  hiding (_∘_; π₁; π₂; ,∘; βπ₂; ηπ; _[_]T; _[_]t)
  renaming
  ( _∘'_ to _∘_
  ; π₁' to π₁
  ; π₂' to π₂
  ; ⟨,∘⟩ to ,∘
  ; ⟨βπ₂⟩ to βπ₂
  ; ηπ' to ηπ
  )


π₁∘
  : (τ : Sub Δ (Θ , A)) (σ : Sub Γ Δ)
  → π₁ (τ ∘ σ) ≡ π₁ τ ∘ σ
π₁∘ τ σ =
  π₁ (τ ∘ σ)
    ≡⟨ cong π₁ (cong (_∘ σ) (ηπ τ)) ⟩
  π₁ ((π₁ τ , π₂ τ ∶[ refl ]) ∘ σ)
    ≡⟨ cong π₁ (,∘ (π₁ τ) (π₂ τ) σ refl) ⟩
  π₁ (π₁ τ ∘ σ , π₂ τ [ σ ] ∶[ cong (_[ σ ]) (λ _ → tyOf (π₂ τ)) ∙ [∘]T _ σ (π₁ τ) ])
    ≡⟨ βπ₁ (π₁ τ ∘ σ) (π₂ τ [ σ ]) (cong (_[ σ ]) (λ _ → tyOf (π₂ τ)) ∙ [∘]T _ σ (π₁ τ)) ⟩
  π₁ τ ∘ σ
    ∎

π₂∘
  : (τ : Sub Δ (Θ , A))(σ : Sub Γ Δ)
  → π₂ (τ ∘ σ) ≡ (π₂ τ) [ σ ]
π₂∘ {Θ = Θ} {A} τ σ = 
  π₂ (τ ∘ σ)
    ≡⟨ cong π₂ (cong (_∘ σ) (ηπ τ)) ⟩
  π₂ ((π₁ τ , π₂ τ ∶[ refl ]) ∘ σ)
    ≡⟨ cong π₂ (,∘ (π₁ τ) (π₂ τ) σ refl) ⟩
  π₂ (π₁ τ ∘ σ , π₂ τ [ σ ] ∶[ cong (_[ σ ]) (λ _ → tyOf (π₂ τ)) ∙ [∘]T _ σ (π₁ τ) ])
    ≡⟨ βπ₂ (π₁ τ ∘ σ) (π₂ τ [ σ ]) (cong (_[ σ ]) (λ _ → tyOf (π₂ τ)) ∙ [∘]T A σ (π₁ τ)) ⟩
  π₂ τ [ σ ]
    ∎
  -- interleaved mutual
  --   data Ctx : Set
  --   data Sub : Ctx → Ctx → Set
  --   data Ty  : Ctx → Set
  --   data Tm  : (Γ : Ctx) → Set

  --   variable
  --       Γ Δ Θ Ξ : Ctx
  --       A B C : Ty Γ
  --       t u   : Tm Γ
  --       σ τ δ : Sub Γ Δ

  --   tyOf
  --     : Tm Γ → Ty Γ


  -- --   data Ctx where
  -- --     ∅
  -- --       : Ctx
  -- --     _,_
  -- --       : (Γ : Ctx)(A : Ty Γ)
  -- --       → Ctx

  -- -- -- Agda is a bit annoying: QIIT support is not fully general as constructors cannot be interleaved.
  -- --   _[_]T
  -- --     : (A : Ty Δ)(σ : Sub Γ Δ)
  -- --     → Ty Γ
  -- --   _[_]t
  -- --     : (A : Tm Δ)(σ : Sub Γ Δ)
  -- --     → Tm Γ
  -- --   _,'_∶[_]
  -- --     : (σ : Sub Γ Δ) (t : Tm Γ) → tyOf t ≡ A [ σ ]T
  -- --     → Sub Γ (Δ , A)
  -- --   idS'
  -- --     : Sub Γ Γ
  -- --   _∘'_
  -- --     : Sub Δ Θ → Sub Γ Δ
  -- --     → Sub Γ Θ
  -- --   π₁'
  -- --     : Sub Γ (Δ , A)
  -- --     → Sub Γ Δ
  -- --   π₂'
  -- --     : Sub Γ (Δ , A)
  -- --     → Tm Γ
  -- --   [idS]'
  -- --     : A ≡ A [ idS' ]T
  -- --   [∘]'
  -- --     : A [ τ ]T [ σ ]T ≡ A [ τ ∘' σ ]T

  -- --   ⟨_∶_∶_⟩
  -- --     : (t : Tm Γ) (A : Ty Γ) (p : tyOf t ≡ A) → Sub Γ (Γ , A)

  -- --   βπ₁'
  -- --     : (σ : Sub Γ Δ) (t : Tm Γ) (p : tyOf t ≡ A [ σ ]T)
  -- --     → π₁' (σ ,' t ∶[ p ]) ≡ σ

  -- --   tyOfπ₂ : tyOf (π₂' idS') ≡ A [ σ ∘' π₁' idS' ]T

  -- --   _↑_ : (σ : Sub Γ Δ) (A : Ty Δ) → Sub (Γ , (A [ σ ]T)) (Δ , A)
  -- --   σ ↑ A = (σ ∘' π₁' idS') ,' π₂' idS' ∶[ tyOfπ₂ ]

  -- --   data Ty where
  -- --     _[_]
  -- --       : (A : Ty Δ)(σ : Sub Γ Δ)
  -- --       → Ty Γ
  -- --     [idS]
  -- --       : A ≡ A [ idS' ]
  -- --     [∘]
  -- --       : A [ τ ] [ σ ] ≡ A [ τ ∘' σ ]
  -- --     U
  -- --       : Ty Γ
  -- --     U[]
  -- --       : U [ σ ] ≡ U
  -- --     El
  -- --       : (u : Tm Γ) → tyOf u ≡ U
  -- --       → Ty Γ
  -- --     El[]
  -- --       : (τ : Sub Γ Δ) (u : Tm Δ) (p : tyOf u ≡ U) (q : tyOf (u [ τ ]t) ≡ U)
  -- --       → (El u p) [ τ ] ≡ El (u [ τ ]t) q
  -- --     Π
  -- --       : (A : Ty Γ) (B : Ty (Γ , A))
  -- --       → Ty Γ
  -- --     Π[]
  -- --       : (Π A B) [ σ ] ≡ Π (A [ σ ]T) (B [ σ ↑ A ]) 
  -- --     𝔹
  -- --       : Ty Γ

  -- --   tt' ff' : Tm Γ
  -- --   tyOftt : tyOf {Γ} tt' ≡ 𝔹 [ idS' ]T
  -- --   tyOfff : tyOf {Γ} ff' ≡ 𝔹 [ idS' ]T
  -- --   tyOftt' : tyOf {Γ} tt' ≡ 𝔹
  -- --   tyOfff' : tyOf {Γ} ff' ≡ 𝔹

  -- --   data Tm where
  -- --     _[_]
  -- --       : (t : Tm Δ) (σ : Sub Γ Δ)
  -- --       → Tm Γ
  -- --     π₂
  -- --       : (σ : Sub Γ (Δ , A))
  -- --       → Tm Γ
  -- --     [idS]tm
  -- --       : (t : Tm Γ)
  -- --       → t ≡ t [ idS' ]
  -- --     [∘]tm
  -- --       : (t : Tm Γ)
  -- --       → t [ τ ] [ σ ] ≡ t [ τ ∘' σ ]
  -- --     βπ₂
  -- --       : (t : Tm Γ) (p : tyOf t ≡ A [ σ ]T) (q : A [ π₁' (σ ,' t ∶[ p ]) ]T ≡ tyOf t)
  -- --       → π₂ (σ ,' t ∶[ p ]) ≡ t
  -- --     app
  -- --       : (t : Tm Γ) → tyOf t ≡ Π A B
  -- --       → Tm (Γ , A)
  -- --     abs
  -- --       : (t : Tm (Γ , A))
  -- --       → Tm Γ
  -- --     abs[]
  -- --       : (t : Tm (Δ , A)) (σ : Sub Γ Δ) (p : tyOf (abs t) [ σ ] ≡ Π (A [ σ ]T) (tyOf (t [ σ ↑ A ])))
  -- --       → (abs t) [ σ ] ≡ abs (t [ σ ↑ _ ])
  -- --     Πβ
  -- --       : (t : Tm (Γ , A)) (p : tyOf (abs t) ≡ Π A B) (q : B ≡ tyOf t)
  -- --       → app (abs t) p ≡ t
  -- --     Πη
  -- --       : (p : tyOf t ≡ Π A B)
  -- --       → abs (app t p) ≡ t
  -- --     tt ff
  -- --       : Tm Γ
  -- --     elim𝔹
  -- --       : (P : Ty (Γ , 𝔹)) → (t u : Tm Γ) → tyOf t ≡ P [ idS' ,' tt' ∶[ tyOftt ]  ]T → tyOf u ≡ P [ idS' ,' ff' ∶[ tyOfff ] ]T
  -- --       → (b : Tm Γ) → tyOf b ≡ 𝔹 → tyOf b ≡ 𝔹 [ idS' ]T
  -- --       → Tm Γ
  -- --     elim𝔹[] 
  -- --       : (P : Ty (Γ , 𝔹)) → (t u : Tm Γ) (pt : tyOf t ≡ P [ idS' ,' tt' ∶[ tyOftt ]  ]T) (pu : tyOf u ≡ P [ idS' ,' ff' ∶[ tyOfff ] ]T)
  -- --       → (b : Tm Γ) (pb : tyOf b ≡ 𝔹) (q : tyOf b ≡ 𝔹 [ idS' ]T)
  -- --       → (elim𝔹 P t u pt pu b pb q) [ σ ] ≡ {!!} -- elim𝔹 {!P [ σ ↑ ? ]T!} {!!} {!!} {!!} {!!} {!!} {!!} {!!}
  -- --     𝔹βₜ
  -- --       : (P : Ty (Γ , 𝔹)) → (t u : Tm Γ) (pt : tyOf t ≡ P [ idS' ,' tt' ∶[ tyOftt ]  ]T) (pu : tyOf u ≡ P [ idS' ,' ff' ∶[ tyOfff ] ]T)
  -- --       → elim𝔹 P t u pt pu tt' tyOftt' tyOftt ≡ t 

  -- --   π₂' = π₂
  -- --   tt' = tt
  -- --   ff' = ff

  -- --   _[_]t = _[_]

  -- --   tyOf (t [ σ ])      = tyOf t [ σ ]T
  -- --   tyOf (π₂ {A = A} σ) = A [ π₁' σ ]T
  -- --   tyOf ([idS]tm t i)  = [idS]' {A = tyOf t} i
  -- --   tyOf ([∘]tm {τ = τ} {σ = σ} t i) = [∘]' {A = tyOf t} {τ = τ} {σ = σ} i
  -- --   tyOf (βπ₂ t p q i)     = q i
  -- --   tyOf (app {B = B} t x) = B
  -- --   tyOf (abs {A = A} t)   = Π A (tyOf t)
  -- --   tyOf (abs[] t σ p i)   = {!!}
  -- --   tyOf (Πβ t p q i)      = q i
  -- --   tyOf (Πη p i)          = p (~ i)
  -- --   tyOf tt = 𝔹
  -- --   tyOf ff = 𝔹
  -- --   tyOf (elim𝔹 P t u pt pu b pb q) = P [ idS' ,' b ∶[ q ] ]T
  -- --   tyOf (elim𝔹[] P t t₁ pt pu t₂ pb q i) = {!!}
  -- --   tyOf (𝔹βₜ P t t₁ pt pu i) = {!!}

  -- --   A [ τ ] [ σ ]T = A [ τ ∘' σ ]
  -- --   [idS] i [ σ ]T = {!!}
  -- --   [∘] i [ σ ]T   = {!!}
  -- --   U [ σ ]T       = U
  -- --   U[] {σ = τ} i [ σ ]T = U[] {σ = τ ∘' σ} i -- U[] i
  -- --   El u p [ σ ]T = El (u [ σ ]) {!U[]!}
  -- --   El[] τ u p q i [ σ ]T = {!!}
  -- --   Π A A₁ [ σ ]T = {!!}
  -- --   Π[] i [ σ ]T = {!!}
  -- --   𝔹 [ σ ]T = 𝔹

  -- --   tyOftt = [idS]'
  -- --   tyOfff = [idS]'

  -- --   tyOftt' = refl
  -- --   tyOfff' = refl

  -- --   tyOfπ₂ = {!!} -- [∘]

  -- --   data Sub where
  -- --     ∅
  -- --       : Sub Γ ∅
  -- --     _,_∶[_]
  -- --       : (σ : Sub Γ Δ) (t : Tm Γ) → tyOf t ≡ A [ σ ]T
  -- --       → Sub Γ (Δ , A)
  -- --     idS
  -- --       : Sub Γ Γ
  -- --     _∘_
  -- --       : Sub Δ Θ → Sub Γ Δ
  -- --       → Sub Γ Θ
  -- --     π₁
  -- --       : Sub Γ (Δ , A)
  -- --       → Sub Γ Δ
  -- --     idS∘_ 
  -- --       : (σ : Sub Γ Δ)
  -- --       → idS ∘ σ ≡ σ
  -- --     _∘idS
  -- --       : (σ : Sub Γ Δ)
  -- --       → σ ∘ idS ≡ σ
  -- --     assocS
  -- --       : (σ : Sub Γ Δ) (τ : Sub Δ Θ) (δ : Sub Θ Ξ)
  -- --       → (δ ∘ τ) ∘ σ ≡ δ ∘ (τ ∘ σ)
  -- --     ,∘
  -- --       : (σ : Sub Δ Θ) (t : Tm Δ) (τ : Sub Γ Δ) (p : tyOf t ≡ A [ σ ]T) (q : tyOf (t [ τ ]) ≡ A [ σ ∘ τ ]T)
  -- --       → (σ , t ∶[ p ]) ∘ τ ≡ (σ ∘ τ , t [ τ ] ∶[ q ])
  -- --     βπ₁
  -- --       : (σ : Sub Γ Δ) (t : Tm Γ) (p : tyOf t ≡ A [ σ ]T)
  -- --       → π₁ (σ , t ∶[ p ]) ≡ σ
  -- --     ηπ
  -- --       : (σ : Sub Γ (Δ , A))
  -- --       → σ ≡ (π₁' σ , π₂ σ ∶[ refl ])
  -- --     η∅
  -- --       : σ ≡ ∅

  -- --   idS' = idS
  -- --   _∘'_ = _∘_
  -- --   _,'_∶[_] = _,_∶[_]
  -- --   π₁'    = π₁
  -- --   βπ₁'   = βπ₁
  -- --   _∘idS' = _∘idS
  -- --   assocS' = assocS


  -- --   [idS]' = {!!} -- [idS]
  -- --   [∘]'   = {!!} -- [∘]
  -- --   ⟨ t ∶ A ∶ p ⟩ = {!!} -- idS , t ∶[ p ∙ [idS] ]

  -- -- -- ⟨βπ₂⟩ : (t : Tm Γ) (p : tyOf t ≡ A [ σ ]) → π₂ (σ , t ∶[ p ]) ≡ t
  -- -- -- ⟨βπ₂⟩ {Γ} {Δ} {A} {σ} t p = βπ₂ t p
  -- -- --   (A [ π₁ (σ , t ∶[ p ]) ]
  -- -- --     ≡⟨ cong (A [_]) (βπ₁ σ t p) ⟩
  -- -- --   A [ σ ]
  -- -- --     ≡⟨ sym p ⟩
  -- -- --   tyOf t
  -- -- --     ∎)

  -- -- -- ⟨,∘⟩
  -- -- --   : (σ : Sub Δ Θ) (t : Tm Δ) (τ : Sub Γ Δ) (p : tyOf t ≡ A [ σ ]T)
  -- -- --   → (σ , t ∶[ p ]) ∘ τ ≡ (σ ∘ τ , t [ τ ] ∶[ cong (_[ τ ]) p ∙ [∘] ])
  -- -- -- ⟨,∘⟩ σ t τ p = ,∘ σ t τ p (cong (_[ τ ]) p ∙ [∘])

  -- -- -- ⟨El[]⟩
  -- -- --   : (τ : Sub Γ Δ) (u : Tm Δ) (p : tyOf u ≡ U)
  -- -- --   → (El u p) [ τ ] ≡ El (u [ τ ]) (cong _[ τ ] p ∙ U[])
  -- -- -- ⟨El[]⟩ τ u p = El[] τ u p (cong (_[ τ ]) p ∙ U[])

  -- -- -- ⟨elim𝔹⟩
  -- -- --   : (P : Ty (Γ , 𝔹)) → (t u : Tm Γ) → tyOf t ≡ P [ idS' ,' tt' ∶[ tyOftt ]  ]T → tyOf u ≡ P [ idS' ,' ff' ∶[ tyOfff ] ]T
  -- -- --   → (b : Tm Γ) → tyOf b ≡ 𝔹
  -- -- --   → Tm Γ
  -- -- -- ⟨elim𝔹⟩ P t u pt pu b pb = elim𝔹 P t u pt pu b pb (pb ∙ [idS])

  -- -- -- π₁∘
  -- -- --   : (τ : Sub Δ (Θ , A)) (σ : Sub Γ Δ)
  -- -- --   → π₁ (τ ∘ σ) ≡ π₁ τ ∘ σ
  -- -- -- π₁∘ τ σ =
  -- -- --   π₁ (τ ∘ σ)
  -- -- --     ≡⟨ cong π₁ (cong (_∘ σ) (ηπ τ)) ⟩
  -- -- --   π₁ ((π₁ τ , π₂ τ ∶[ refl ]) ∘ σ)
  -- -- --     ≡⟨ cong π₁ (⟨,∘⟩ (π₁ τ) (π₂ τ) σ refl) ⟩
  -- -- --   π₁ (π₁ τ ∘ σ , π₂ τ [ σ ] ∶[ cong (_[ σ ]) (refl {x = tyOf (π₂ τ)}) ∙ [∘] ]) -- Cubical Agda does not compute cong f refl to refl
  -- -- --     ≡⟨ βπ₁ (π₁ τ ∘ σ) (π₂ τ [ σ ]) (cong (_[ σ ]) (refl {x = tyOf (π₂ τ)}) ∙ [∘]) ⟩
  -- -- --   π₁ τ ∘ σ
  -- -- --     ∎

  -- -- -- π₂∘
  -- -- --   : (τ : Sub Δ (Θ , A))(σ : Sub Γ Δ)
  -- -- --   → π₂ (τ ∘ σ) ≡ (π₂ τ) [ σ ]
  -- -- -- π₂∘ {Θ = Θ} {A} τ σ = 
  -- -- --   π₂ (τ ∘ σ)
  -- -- --     ≡⟨ cong π₂ (cong (_∘ σ) (ηπ τ)) ⟩
  -- -- --   π₂ ((π₁ τ , π₂ τ ∶[ refl ]) ∘ σ)
  -- -- --     ≡⟨ cong π₂ (⟨,∘⟩ (π₁ τ) (π₂ τ) σ refl) ⟩
  -- -- --   π₂ (π₁ τ ∘ σ , π₂ τ [ σ ] ∶[ cong (_[ σ ]) (λ _ → tyOf (π₂ τ)) ∙ [∘] ])
  -- -- --     ≡⟨ ⟨βπ₂⟩ (π₂ τ [ σ ]) (cong (_[ σ ]) (λ _ → tyOf (π₂ τ)) ∙ [∘]) ⟩
  -- -- --   π₂ τ [ σ ]
  -- -- --     ∎

  -- -- -- -- syntax abbreviations
  -- -- -- wk : Sub (Δ , A) Δ
  -- -- -- wk = π₁ idS

  -- -- -- vz : Tm (Γ , A)
  -- -- -- vz = π₂ idS

  -- -- -- vs : Tm Γ → Tm (Γ , B)
  -- -- -- vs x = x [ wk ]
  -- -- -- -- vs (vs ... (vs vz) ...) = π₂ idS [ π₁ idS ]tm .... [ π₁ idS ]tm

  -- -- -- -- vz:= : (t : Tm Γ) → let (_ , (σ , A)) = tyOf t in Sub Γ (Γ , A [ σ ])
  -- -- -- -- vz:= {Γ} t = idS , t ∶[ {!!} ]
