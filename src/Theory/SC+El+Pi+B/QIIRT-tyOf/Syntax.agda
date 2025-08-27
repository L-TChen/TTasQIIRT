open import Prelude
  hiding (_,_)

module Theory.SC+El+Pi+B.QIIRT-tyOf.Syntax where
  
module Foo where
  module _ where -- delimit the scope of forward declarations
    infixl 8  _[_] _[_]T _[_]t
    infixr 10 _∘_
    infixl 4  _,_ _,_∶[_]

    data Ctx : Set
    data Sub : (Γ Δ : Ctx) → Set
    data Ty  : Ctx → Set
    data Tm  : (Γ : Ctx) → Set
    tyOf
      : ∀ {Γ} → Tm Γ → Ty Γ

    module Var where
      variable
          Γ Δ Θ Ξ : Ctx
          A B C D : Ty Γ
          t u   : Tm Γ
          σ τ γ δ : Sub Γ Δ
    open Var

    -- Substitution calculus
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

    tyOfπ₂ -- definitional after the datatype declaration
      : (σ : Sub Γ (Δ , A))
      → tyOf (π₂ σ) ≡ A [ π₁ σ ]T
    tyOfπ₂idS
      : tyOf (π₂ {A = A [ σ ]T} idS) ≡ A [ σ ∘ π₁ idS ]T

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

    -- Universe
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
      : (t : Tm Γ) (B : Ty (Γ , A)) (pt : tyOf t ≡ Π A B)
      → Tm (Γ , A)
    abs
      : (t : Tm (Γ , A))
      → Tm Γ
    tyOfabs
      : tyOf (abs t) ≡ Π A (tyOf t)
    Π[]
      : (σ : Sub Γ Δ) (B : Ty (Δ , A))
      → (Π A B) [ σ ]T ≡ Π (A [ σ ]T) (B [ σ ↑ A ]T)
    abs[]
      : (σ : Sub Γ Δ) (t : Tm (Δ , A))
      → abs t [ σ ]t ≡ abs (t [ σ ↑ A ]t)
    Πβ
      : (t : Tm (Γ , A)) (p : tyOf (abs t) ≡ Π A (tyOf t))
      → app (abs t) (tyOf t) p ≡ t
    Πη
      : (t : Tm Γ) (p : tyOf t ≡ Π A B)
      → abs (app t B p) ≡ t

    -- The type of Booleans
    𝔹
      : Ty Γ
    𝔹[]
      : (σ : Sub Γ Δ)
      → 𝔹 [ σ ]T ≡ 𝔹
    𝔹[]₂
      : tyOf (π₂ {Γ , 𝔹} idS) ≡ 𝔹 [ τ ]T
    tt ff
      : Tm Γ
    tt[]
      : (σ : Sub Γ Δ)
      → tt [ σ ]t ≡ tt
    ff[]
      : (σ : Sub Γ Δ)
      → ff [ σ ]t ≡ ff
    tyOftt : tyOf {Γ} tt ≡ 𝔹 [ idS ]T -- definitional later
    tyOfff : tyOf {Γ} ff ≡ 𝔹 [ idS ]T -- definitional later

    _↑𝔹
      : (σ : Sub Γ Δ)
      → Sub (Γ , 𝔹) (Δ , 𝔹)
    σ ↑𝔹 = σ ∘ π₁ idS , π₂ idS ∶[ 𝔹[]₂ {τ = σ ∘ π₁ idS} ]

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

    -- Code for the universe
    𝕓 : Tm Γ
    𝕓[]
      : (σ : Sub Γ Δ)
      → 𝕓 [ σ ]t ≡ 𝕓
    tyOf𝕓
      : tyOf {Γ} 𝕓 ≡ U
    El𝕓
      : (Γ : Ctx)
      → El {Γ} (𝕓) tyOf𝕓 ≡ 𝔹

    El[]₂
      : (u : Tm Δ) (pu : tyOf u ≡ U)(pu' : tyOf (u [ σ ]t) ≡ U)
      → tyOf (π₂ {Γ , El (u [ σ ]t) pu'} idS) ≡ El u pu [ σ ∘ π₁ idS ]T

    _↑El
      : (σ : Sub Γ Δ) {u : Tm Δ} {pu : tyOf u ≡ U} {pu' : tyOf (u [ σ ]t) ≡ U}
      → Sub (Γ , El (u [ σ ]t) pu') (Δ , El u pu)
    (σ ↑El) {u} {pu} {pu'} = σ ∘ π₁ idS , π₂ idS ∶[ El[]₂ u pu pu' ]

    π
      : (a : Tm Γ) (pa : tyOf a ≡ U)
      → (b : Tm (Γ , El a pa)) (pb : tyOf b ≡ U)
      → Tm Γ
    π[]
      : (a : Tm Γ) (pa : tyOf a ≡ U)
      → (b : Tm (Γ , El a pa)) (pb : tyOf b ≡ U)
      → (pa' : tyOf (a [ σ ]t) ≡ U)
      → (pb' : tyOf (b [ σ ↑El ]t) ≡ U)
      → (π a pa b pb) [ σ ]t ≡ π (a [ σ ]t) pa' (b [ σ ↑El ]t) pb'
    tyOfπ
      : (a : Tm Γ) (pa : tyOf a ≡ U) (b : Tm (Γ , El a pa)) (pb : tyOf b ≡ U)
      → tyOf (π a pa b pb) ≡ U
    Elπ
      : (a : Tm Γ) (pa : tyOf a ≡ U)
      → (b : Tm (Γ , El a pa)) (pb : tyOf b ≡ U)
      → El (π a pa b pb) (tyOfπ a pa b pb) ≡ Π (El a pa) (El b pb)

    -- the following are the actual constructors in Agda
    data Ctx where
      ∅' : Ctx 
      _,'_ : (Γ : Ctx) (A : Ty Γ) → Ctx
    data Sub where
      ∅'
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
        → σ ≡ ∅S
      ηπ'
        : (σ : Sub Γ (Δ , A))
        → σ ≡ (π₁ σ , π₂ σ ∶[ tyOfπ₂ σ ])
    data Ty where
      _[_] : (A : Ty Δ) (σ : Sub Γ Δ)
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
      El[]₂'
        : {σ : Sub Γ Δ}
        → (u : Tm Δ) (pu : tyOf u ≡ U)(pu' : tyOf (u [ σ ]t) ≡ U)
        → tyOf (π₂ {Γ , El (u [ σ ]t) pu'} {A = El (u [ σ ]t) pu'} idS)
        ≡ El u pu [ σ ∘ π₁ idS ]T
      Π'
        : (A : Ty Γ) (B : Ty (Γ , A))
        → Ty Γ
      Π[]'
        : (σ : Sub Γ Δ) (B : Ty (Δ , A))
        → (Π A B) [ σ ]T ≡ Π (A [ σ ]T) (B [ σ ↑ A ]T)
      𝔹'
        : Ty Γ
      𝔹[]'
        : (σ : Sub Γ Δ)
        → 𝔹 [ σ ]T ≡ 𝔹
      𝔹[]₂'
        : tyOf (π₂ {Γ , 𝔹} {A = 𝔹} idS) ≡ 𝔹 [ τ ]T
      El𝕓'
        : (Γ : Ctx)
        → El {Γ} 𝕓 tyOf𝕓 ≡ 𝔹
      tyOfπ'
        : (a : Tm Γ) (pa : tyOf a ≡ U) (b : Tm (Γ , El a pa)) (pb : tyOf b ≡ U)
        → tyOf (π a pa b pb) ≡ U
      Elπ'
        : (a : Tm Γ) (pa : tyOf a ≡ U)
        → (b : Tm (Γ , El a pa)) (pb : tyOf b ≡ U)
        → El (π a pa b pb) (tyOfπ a pa b pb) ≡ Π (El a pa) (El b pb)
      -- Ty-is-set : isSet (Ty Γ)

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
        : (t : Tm Γ) (B : Ty (Γ , A)) (pt : tyOf t ≡ Π A B)
        → Tm (Γ , A)
      abs'
        : (t : Tm (Γ , A))
        → Tm Γ
      abs[]'
        : (σ : Sub Γ Δ) (t : Tm (Δ , A)) 
        → abs t [ σ ]t ≡ abs (t [ σ ↑ A ]t)
      Πβ'
        : (t : Tm (Γ , A)) (p : tyOf (abs t) ≡ Π A (tyOf t))
        → app (abs t) (tyOf t) p ≡ t
      Πη'
        : (t : Tm Γ) (p : tyOf t ≡ Π A B)
        → abs (app t B p) ≡ t
      tt' ff'
        : Tm Γ
      tt[]'
        : (σ : Sub Γ Δ)
        → tt [ σ ]t ≡ tt
      ff[]'
        : (σ : Sub Γ Δ)
        → ff [ σ ]t ≡ ff
      elim𝔹'
        : (P : Ty (Γ , 𝔹)) (t u : Tm Γ)
        → (pt : tyOf t ≡ P [ idS , tt ∶[ tyOftt ] ]T)
        → (pu : tyOf u ≡ P [ idS , ff ∶[ tyOfff ] ]T)
        → (b : Tm Γ) → tyOf b ≡ 𝔹 [ idS ]T
        → Tm Γ
      elim𝔹[]'
        : (P : Ty (Γ , 𝔹)) (t u : Tm Γ) (pt : tyOf t ≡ _) (pu : tyOf u ≡ _) → (b : Tm Γ) (pb : tyOf b ≡ 𝔹 [ idS ]T)
        → (pt₂ : tyOf (t [ σ ]t) ≡ P [ σ ↑𝔹 ]T [ idS , tt ∶[ tyOftt ] ]T)
        → (pu₂ : tyOf (u [ σ ]t) ≡ P [ σ ↑𝔹 ]T [ idS , ff ∶[ tyOfff ] ]T)
        → (pb₂ : tyOf (b [ σ ]t) ≡ 𝔹 [ idS ]T)
        → (p : P [ idS , b ∶[ pb ] ] [ σ ] ≡ P [ (σ ∘ π₁ idS) , π₂ idS ∶[ 𝔹[]₂ ] ] [ idS , b [ σ ] ∶[ pb₂ ] ])
        → (elim𝔹 P t u pt pu b pb) [ σ ]t
        ≡ elim𝔹 (P [ σ ↑𝔹 ]T) (t [ σ ]t) (u [ σ ]t) pt₂ pu₂ (b [ σ ]t) pb₂
      𝕓'
        : Tm Γ
      𝕓[]'
        : (σ : Sub Γ Δ)
        → 𝕓 [ σ ]t ≡ 𝕓
      π'
        : (a : Tm Γ) (pa : tyOf a ≡ U)
        → (b : Tm (Γ , El a pa)) (pb : tyOf b ≡ U)
        → Tm Γ
      π[]'
        : (a : Tm Γ) (pa : tyOf a ≡ U)
        → (b : Tm (Γ , El a pa)) (pb : tyOf b ≡ U)
        → (pa' : tyOf (a [ σ ]t) ≡ U)
        → (pb' : tyOf (b [ σ ↑El ]t) ≡ U)
        → (π a pa b pb) [ σ ]t ≡ π (a [ σ ]t) pa' (b [ σ ↑El ]t) pb'

    ∅       = ∅'
    _,_     = _,'_
    _[_]T   = _[_]
    _[_]t   = _[_]
    U       = U'
    U[]     = U[]'
    El      = El'
    El[]    = El[]'
    El[]₂   = El[]₂'
    Π       = Π'
    Π[]     = Π[]'
    𝔹       = 𝔹'
    𝔹[]     = 𝔹[]'
    𝔹[]₂    = 𝔹[]₂'
    ∅S      = ∅'
    _,_∶[_] = _,_∶[_]'
    idS     = idS'
    _∘_     = _∘'_
    π₁      = π₁'
    π₂      = π₂'
    [idS]T  = [idS]T'
    [∘]T    = [∘]T'
    βπ₁     = βπ₁'
    βπ₂     = βπ₂'
    idS∘_   = idS∘'_
    _∘idS   = _∘idS'
    assocS  = assocS'
    ,∘      = ,∘'
    η∅      = η∅'
    ηπ      = ηπ'
    [idS]t  = [idS]t'
    [∘]t    = [∘]t'
    abs     = abs'
    app     = app'
    abs[]   = abs[]'
    Πβ      = Πβ'
    Πη      = Πη'
    tt      = tt'
    ff      = ff'
    tt[]    = tt[]'
    ff[]    = ff[]'
    elim𝔹   = elim𝔹'
    elim𝔹[] = elim𝔹[]'
    𝕓       = 𝕓'
    𝕓[]     = 𝕓[]'
    El𝕓     = El𝕓'
    tyOfπ   = tyOfπ'
    π       = π'
    Elπ     = Elπ'
    π[]     = π[]'

    tyOf (t [ σ ]) = tyOf t [ σ ]T
    tyOf (π₂' {Γ} {Δ} {A} σ) = A [ π₁ {A = A} σ ]T
    tyOf (βπ₂' σ t p q i)   = q i
    tyOf ([idS]t' t i)      = [idS]T {A = tyOf t} i
    tyOf ([∘]t' t σ τ i)    = [∘]T (tyOf t) σ τ i
    tyOf (app' t B p) = B
    tyOf (abs' {A = A} t)   = Π A (tyOf t)
    tyOf (abs[]' σ t i) =
      Π[] σ (tyOf t) i
    tyOf (Πβ' t p i) = tyOf t
    tyOf (Πη' t p i) = p (~ i)
    tyOf tt' = 𝔹
    tyOf ff' = 𝔹
    tyOf (tt[]' σ i) = 𝔹[] σ i
    tyOf (ff[]' σ i) = 𝔹[] σ i
    tyOf (elim𝔹' P u t pu pt b pb) = P [ idS , b ∶[ pb ] ]T
    tyOf (elim𝔹[]' P u t pu pt b pb pt₂ pu₂ pb₂ q i) = q i
    tyOf 𝕓' = U
    tyOf (𝕓[]' σ i) = U[] {σ = σ} i
    tyOf (π' a pa b pb) = U
    tyOf (π[]' {σ = σ} a pa b pb pa' pb' i) = U[] {σ = σ} i

    -- equaitons derivable from the computational behaviour of `tyOf
    tyOfπ₂ σ = refl
    tyOfπ₂idS {A = A} {σ = σ} = [∘]T A (π₁ idS) σ
    tyOfabs = refl
    tyOftt  = [idS]T
    tyOfff  = [idS]T
    tyOf𝕓   = refl
 
  open Var
  wk : Sub (Γ , A) Γ
  wk = π₁ idS
  
  ⟨,∘⟩
    : (σ : Sub Δ Θ) (t : Tm Δ) (τ : Sub Γ Δ) (p : tyOf t ≡ A [ σ ]T)
    → (σ , t ∶[ p ]) ∘ τ ≡ (σ ∘ τ , t [ τ ]t ∶[ cong _[ τ ] p ∙ [∘]T A τ σ ])
  ⟨,∘⟩ σ t τ p = ,∘ σ t τ p _

  ⟨βπ₂⟩
    : (σ : Sub Γ Δ) (t : Tm Γ) (p : tyOf t ≡ A [ σ ]T)
    → π₂ (σ , t ∶[ p ]) ≡ t
  ⟨βπ₂⟩ {A = A} σ t p = βπ₂ σ t _ (cong (A [_]) (βπ₁ σ t p) ∙ sym p)

  π₁∘
    : (τ : Sub Δ (Θ , A)) (σ : Sub Γ Δ)
    → π₁ (τ ∘ σ) ≡ π₁ τ ∘ σ
  π₁∘ τ σ =
    π₁ (τ ∘ σ)
      ≡⟨ cong π₁ (cong (_∘ σ) (ηπ τ)) ⟩
    π₁ ((π₁ τ , π₂ τ ∶[ refl ]) ∘ σ)
      ≡⟨ cong π₁ (⟨,∘⟩ (π₁ τ) (π₂ τ) σ refl) ⟩
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
      ≡⟨ cong π₂ (⟨,∘⟩ (π₁ τ) (π₂ τ) σ refl) ⟩
    π₂ (π₁ τ ∘ σ , π₂ τ [ σ ] ∶[ _ ])
      ≡⟨ ⟨βπ₂⟩ (π₁ τ ∘ σ) (π₂ τ [ σ ]) _ ⟩
    π₂ τ [ σ ]
      ∎

  π₁idS
    : (σ : Sub Γ (Δ , A))
    → π₁ σ ≡ π₁ idS ∘ σ
  π₁idS σ = 
    π₁ σ
      ≡⟨ cong π₁ (sym (idS∘ σ)) ⟩
    π₁ (idS ∘ σ)
      ≡⟨ π₁∘ _ σ ⟩
    π₁ idS ∘ σ
      ∎

  π₂idS
    : (σ : Sub Γ (Δ , A))
    → π₂ σ ≡ π₂ idS [ σ ]t
  π₂idS σ = 
    π₂ σ
      ≡⟨ cong π₂ (sym (idS∘ σ)) ⟩
    π₂ (idS ∘ σ)
      ≡⟨ π₂∘ _ _ ⟩
    π₂ idS [ σ ]t
      ∎

  wk∘
    : (σ : Sub Γ (Δ , A))
    → π₁ σ ≡ wk ∘ σ
  wk∘ σ = 
    π₁ σ
      ≡⟨ cong π₁ (sym (idS∘ σ)) ⟩
    π₁ (idS ∘ σ)
      ≡⟨ π₁∘ idS σ ⟩
    wk ∘ σ
      ∎

  -- Proofs regarding Boolean
  -- Sanity check
  𝔹[σ]≡𝔹[τ] : 𝔹 [ σ ]T ≡ 𝔹 [ τ ]T
  𝔹[σ]≡𝔹[τ] {σ = σ} {τ = τ} = 𝔹[] σ ∙ sym (𝔹[] τ)

  wk∘↑𝔹
    : (σ : Sub Γ Δ)
    → wk ∘ (σ ↑𝔹) ≡ σ ∘ wk
  wk∘↑𝔹 σ =
    wk ∘ (σ ↑𝔹)
      ≡⟨ sym (wk∘ (σ ↑𝔹))  ⟩
    π₁ (σ ↑𝔹)
      ≡⟨ refl ⟩
    π₁ ((σ ∘ wk) , π₂ idS ∶[ 𝔹[]₂ ])
      ≡⟨ βπ₁ _ _ _ ⟩
    σ ∘ wk
      ∎
  ⟨_∶[_]⟩𝔹 : (b : Tm Γ) (pb : tyOf b ≡ 𝔹 [ idS ]T)
    → Sub Γ (Γ , 𝔹)
  ⟨ b ∶[ pb ]⟩𝔹 = idS , b ∶[ pb ]

  wk∘⟨⟩
    : (b : Tm Γ) (pb : tyOf b ≡ (𝔹 [ idS ]T))
    → wk ∘ ⟨ b ∶[ pb ]⟩𝔹 ≡ idS
  wk∘⟨⟩ b pb =
    wk ∘ ⟨ b ∶[ pb ]⟩𝔹
      ≡⟨ sym (π₁idS _)  ⟩
    π₁ (idS , b ∶[ pb ])
      ≡⟨ βπ₁ _ _ _ ⟩
    idS
      ∎

  vz[⟨b⟩]
    : (b : Tm Γ) (pb : tyOf b ≡ 𝔹 [ idS ]T)
    → π₂ idS [ ⟨ b ∶[ pb ]⟩𝔹 ]t ≡ b
  vz[⟨b⟩] b pb =
    π₂ idS [ ⟨ b ∶[ pb ]⟩𝔹 ]t
      ≡⟨ refl ⟩
    π₂ idS [ idS , b ∶[ pb ] ]t
      ≡⟨ sym (π₂idS ⟨ b ∶[ pb ]⟩𝔹) ⟩
    π₂ ⟨ b ∶[ _ ]⟩𝔹
      ≡⟨ βπ₂ _ _ _ (cong (𝔹 [_]) (βπ₁ _ _ _) ∙ sym pb) ⟩
    b
      ∎

{-
  ⟨⟩∘=↑∘[]
    : (b : Tm Γ) (pb : tyOf b ≡ 𝔹 [ idS ]T) (pb' : tyOf (b [ σ ]t) ≡ 𝔹 [ idS ]T)
    → ⟨ b ∶[ pb ]⟩𝔹 ∘ σ ≡ (σ ↑𝔹) ∘ ⟨ b [ σ ]t ∶[ pb' ]⟩𝔹
  ⟨⟩∘=↑∘[] {Δ} {Γ} {σ} b pb pb' =
    ⟨ b ∶[ pb ]⟩𝔹 ∘ σ 
      ≡⟨ ,∘ idS b σ pb _ ⟩
    idS ∘ σ , b [ σ ]t ∶[ _ ]
      ≡[ i ]⟨ (idS∘ σ) i , b [ σ ]t ∶[ pb' ∙ 𝔹[σ]≡𝔹[τ] ] ⟩
    σ , b [ σ ]t ∶[ _ ]
      ≡[ i ]⟨ (σ ∘idS) (~ i) , b [ σ ]t ∶[ pb' ∙ 𝔹[σ]≡𝔹[τ] ] ⟩
    σ ∘ idS , b [ σ ]t ∶[ pb' ∙ 𝔹[σ]≡𝔹[τ] ] 
      ≡[ i ]⟨ σ ∘ wk∘⟨⟩ (b [ σ ]) pb' (~ i) , vz[⟨b⟩] (b [ σ ]) pb' (~ i) ∶[ {!!} ] ⟩
            -- [TODO]: derivable from K?
    σ ∘ (π₁ idS ∘ ⟨ b [ σ ]t ∶[ pb' ]⟩𝔹) , π₂ idS [ ⟨ b [ σ ]t ∶[ pb' ]⟩𝔹 ]t ∶[ _ ]
      ≡[ i ]⟨ assocS ⟨ b [ σ ]t ∶[ pb' ]⟩𝔹 (π₁ idS) σ (~ i) , π₂ idS [ ⟨ b [ σ ]t ∶[ pb' ]⟩𝔹 ] ∶[ {!!} ] ⟩
            -- [TODO]: derivable from K?
    (σ ∘ π₁ idS) ∘ ⟨ b [ σ ]t ∶[ pb' ]⟩𝔹 , π₂ idS [ ⟨ b [ σ ]t ∶[ pb' ]⟩𝔹 ]t ∶[ [∘]T _ _ _ ∙ 𝔹[σ]≡𝔹[τ] ]
      ≡⟨ sym (,∘ _ _ _ _ _) ⟩
    (σ ↑𝔹) ∘ ⟨ b [ σ ]t ∶[ pb' ]⟩𝔹
      ∎

  [⟨⟩∘]=[↑∘[]]
    : (b : Tm Γ) (pb : tyOf b ≡ 𝔹 [ idS ]T) (pb' : tyOf (b [ σ ]t) ≡ 𝔹 [ idS ]T)
    → A [ ⟨ b ∶[ pb ]⟩𝔹 ]T [ σ ]T
    ≡ A [ σ ↑𝔹 ]T [ ⟨ b [ σ ]t ∶[ pb' ]⟩𝔹 ]T
  [⟨⟩∘]=[↑∘[]] {Δ} {Γ} {σ} {A} b pb pb' = 
    A [ ⟨ b ∶[ pb ]⟩𝔹 ]T [ σ ]T
      ≡⟨ [∘]T _ _ _ ⟩
    A [ ⟨ b ∶[ pb ]⟩𝔹 ∘ σ ]T
      ≡⟨ cong (A [_]) (⟨⟩∘=↑∘[] b pb pb') ⟩
    A [ σ ↑𝔹 ∘ ⟨ b [ σ ]t ∶[ pb' ]⟩𝔹 ]T
      ≡⟨ sym ([∘]T _ _ _) ⟩
    A [ σ ↑𝔹 ]T [ ⟨ b [ σ ]t ∶[ pb' ]⟩𝔹 ]T
      ∎

  ⟨elim𝔹[]⟩
    : (P : Ty (Γ , 𝔹)) (t u : Tm Γ) (pt : tyOf t ≡ _) (pu : tyOf u ≡ _) → (b : Tm Γ) (pb : tyOf b ≡ 𝔹 [ idS ]T)
    → (elim𝔹 P t u pt pu b pb) [ σ ]t
    ≡ elim𝔹 (P [ σ ↑𝔹 ]T) (t [ σ ]t) (u [ σ ]t) _ _ (b [ σ ]t) _
  ⟨elim𝔹[]⟩ {σ = σ} P t u pt pu b pb = elim𝔹[] P t u pt pu b pb
    (tyOf t [ σ ]T
      ≡⟨ cong (_[ σ ]T) pt ⟩
    P [ ⟨ tt ∶[ tyOftt ]⟩𝔹 ]T [ σ ]T
      ≡⟨ [⟨⟩∘]=[↑∘[]] {σ = σ} {A = P} tt tyOftt 𝔹[σ]≡𝔹[τ] ⟩
    P [ σ ↑𝔹 ]T [ ⟨ tt [ σ ]t ∶[ _ ]⟩𝔹 ]T
      ≡⟨ cong (P [ σ ↑𝔹 ]T [_]T) {!!} ⟩
            -- [TODO]: derivable from K?
    P [ σ ↑𝔹 ]T [ ⟨ tt ∶[ tyOfff ]⟩𝔹 ]T
      ∎)
    (tyOf u [ σ ]T
      ≡⟨ cong (_[ σ ]T) pu ⟩
    P [ ⟨ ff ∶[ tyOfff ]⟩𝔹 ]T [ σ ]T
      ≡⟨ [⟨⟩∘]=[↑∘[]] {σ = σ} {P} ff tyOfff 𝔹[σ]≡𝔹[τ] ⟩
    P [ σ ↑𝔹 ]T [ ⟨ ff [ σ ]t ∶[ _ ]⟩𝔹 ]T
      ≡⟨ cong (P [ σ ↑𝔹 ]T [_]T) {!!} ⟩
            -- [TODO]: derivable from K?
    P [ σ ↑𝔹 ]T [ ⟨ ff ∶[ tyOfff ]⟩𝔹 ]T
      ∎)
    _ ([⟨⟩∘]=[↑∘[]] b pb
        (tyOf b [ σ ]T
          ≡⟨ cong (_[ σ ]T) pb ⟩
        𝔹 [ idS ]T [ σ ]T
          ≡⟨ cong (_[ σ ]T) (sym [idS]T) ⟩
        𝔹 [ σ ]T
          ≡⟨ 𝔹[σ]≡𝔹[τ] ⟩
        𝔹 [ idS ]T ∎))

  𝔹[]₂′=𝔹[]₂ : 𝔹[]₂ {τ = τ} ≡ 𝔹[]₂′
  𝔹[]₂′=𝔹[]₂ = {!!} -- derivable from K
-}

  El[]₂-sanity-check
    : {σ : Sub Γ Δ}(u : Tm Δ) (pu : tyOf u ≡ U)(pu' : tyOf (u [ σ ]t) ≡ U)
    → tyOf (π₂ {Γ , El (u [ σ ]t) pu'} idS) ≡ El u pu [ σ ∘ π₁ idS ]T
  El[]₂-sanity-check {Δ = Δ} {σ = σ} u pu pu' =
    El (u [ σ ]t) pu' [ π₁ idS ]T
      ≡⟨ El[] (π₁ idS) (u [ σ ]t) pu' (cong _[ π₁ {A = El (u [ σ ]t) pu'} idS ] pu' ∙ U[])  ⟩
    El (u [ σ ]t [ π₁ idS ]t) _
      ≡⟨ cong₂ El ([∘]t u (π₁ idS) σ) (isProp→PathP (λ _ → UIP) _ _) ⟩
    El (u [ σ ∘ π₁ idS ]t) _
      ≡⟨ sym (El[] (σ ∘ π₁ idS) u pu (cong _[ σ ∘ π₁ {A = El (u [ σ ]t) pu'} idS ]T pu ∙ U[])) ⟩
    El u pu [ σ ∘ π₁ idS ]T
      ∎

open Foo public
  hiding
  ( ∅
  ; _,_
  ; _[_]T
  ; _[_]t
  ; U
  ; U[]
  ; El
  ; El[]
  ; El[]₂
  ; Π
  ; Π[]
  ; 𝔹
  ; 𝔹[]
  ; 𝔹[]₂
  ; ∅S
  ; _,_∶[_]
  ; idS
  ; _∘_
  ; π₁
  ; π₂
  ; [idS]T
  ; [∘]T
  ; βπ₁
  ; βπ₂
  ; idS∘_
  ; _∘idS
  ; assocS
  ; ,∘
  ; η∅
  ; ηπ
  ; [idS]t
  ; [∘]t
  ; abs
  ; app
  ; abs[]
  ; Πβ
  ; Πη
  ; tt
  ; ff
  ; tt[]
  ; ff[]
  ; elim𝔹
  ; elim𝔹[]
  ; 𝕓
  ; 𝕓[]
  ; El𝕓
  ; tyOfπ
  ; π
  ; Elπ
  ; π[]
  )
  renaming
  ( ∅' to ∅
  ; _,'_ to _,_
  ; U' to U
  ; U[]' to U[]
  ; El' to El
  ; El[]' to El[]
  ; El[]₂' to El[]₂
  ; Π' to Π
  ; Π[]' to Π[]
  ; 𝔹' to 𝔹
  ; 𝔹[]' to 𝔹[]
  ; 𝔹[]₂' to 𝔹[]₂
  ; _,_∶[_]' to _,_∶[_]
  ; idS' to idS
  ; _∘'_ to _∘_
  ; π₁'  to π₁
  ; π₂'  to π₂ 
  ; [idS]T' to [idS]T
  ; [∘]T' to [∘]T
  ; βπ₁' to βπ₁
  ; βπ₂' to βπ₂
  ; idS∘'_ to idS∘_
  ; _∘idS' to _∘idS
  ; assocS' to assocS
  ; ,∘' to ,∘
  ; η∅' to η∅
  ; ηπ' to ηπ
  ; [idS]t' to [idS]t
  ; [∘]t'  to [∘]t
  ; abs' to abs
  ; app' to app
  ; abs[]' to abs[]
  ; Πβ' to Πβ
  ; Πη' to Πη
  ; tt' to tt
  ; ff' to ff
  ; tt[]' to tt[]
  ; ff[]' to ff[]
  ; elim𝔹' to elim𝔹
  ; elim𝔹[]' to elim𝔹[]
  ; 𝕓' to 𝕓
  ; 𝕓[]' to 𝕓[]
  ; El𝕓' to El𝕓
  ; tyOfπ' to tyOfπ
  ; π' to π
  ; Elπ' to Elπ
  ; π[]' to π[]
  )


open Var
-- syntax abbreviations
vz : Tm (Γ , A)
vz = π₂ idS

vs : Tm Γ → Tm (Γ , B)
vs x = x [ wk ]
-- vs (vs ... (vs vz) ...) = π₂ idS [ π₁ idS ]tm .... [ π₁ idS ]tm

-- -- vz:= : (t : Tm Γ) → let (_ , (σ , A)) = tyOf t in Sub Γ (Γ , A [ σ ])
-- -- vz:= {Γ} t = idS , t ∶[ {!!} ]
