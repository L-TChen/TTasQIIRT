-- Type theory as a quotient inductive-inductive-recursive type, inspired by the formualtion of natural models
-- whereas the recursion part is impredicative.


-- See https://github.com/agda/agda/issues/5362 for the current limitation of Agda
-- that affacts the definition of our encoding

open import Prelude
  hiding (_,_)

module Theory.SC.QIIRT-tyOf.Syntax where
  
module Foo where
  module _ where -- delimit the scope of forward declarations
    infixl 8  _[_] _[_]T _[_]t
    infixr 10 _∘_
    infixl 4  _,_ _,_∶[_] _,_∶[_]'

    data Ctx : Set
    data Sub : (Γ Δ : Ctx) → Set
    data Ty  : Ctx → Set
    data Tm  : (Γ : Ctx) → Set
    tyOf
      : ∀ {Γ} → Tm Γ → Ty Γ

    variable
        Γ Δ Θ Ξ : Ctx
        A B C : Ty Γ
        t u   : Tm Γ
        σ τ δ : Sub Γ Δ

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

    -- the following are the actual constructors in Agda
    data Ctx where
      ∅' : Ctx 
      _,'_ : (Γ : Ctx) (A : Ty Γ) → Ctx
      
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
      Ty-is-set : isSet (Ty Γ)

    data Sub where
      ∅S'
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

    ∅       = ∅'
    _,_     = _,'_
    _[_]T   = _[_]
    _[_]t   = _[_]
    U       = U'
    U[]     = U[]'
    ∅S      = ∅S'
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

    tyOf (t [ σ ]) = tyOf t [ σ ]T
    tyOf (π₂' {Γ} {Δ} {A} σ) = A [ π₁ σ ]T
    tyOf (βπ₂' σ t p q i)   = q i
    tyOf ([idS]t' t i)      = [idS]T {A = tyOf t} i
    tyOf ([∘]t' t σ τ i)    = [∘]T (tyOf t) σ τ i

    -- equaitons derivable from the computational behaviour of `tyOf
    tyOfπ₂ σ = refl
    tyOfπ₂idS {A = A} {σ = σ} = [∘]T A (π₁ idS) σ
    tyOfabs = refl
    tyOftt  = [idS]T
    tyOfff  = [idS]T
    tyOf𝕓   = refl
 
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

open Foo public
  hiding
  ( ∅
  ; _,_
  ; _[_]T
  ; _[_]t
  ; U
  ; U[]
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
  )
  renaming
  ( ∅' to ∅
  ; _,'_ to _,_
  ; U' to U
  ; U[]' to U[]
  ; ∅S' to ∅S
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
  )

π₁∘
  : (τ : Sub Δ (Θ , A)) (σ : Sub Γ Δ)
  → π₁ (τ ∘ σ) ≡ π₁ τ ∘ σ
π₁∘ τ σ =
  π₁ (τ ∘ σ)
    ≡⟨ cong π₁ (cong (_∘ σ) (ηπ τ)) ⟩
  π₁ ((π₁ τ , π₂ τ ∶[ refl ]) ∘ σ)
    ≡⟨ cong π₁ (,∘ (π₁ τ) (π₂ τ) σ refl ([∘]T _ _ _)) ⟩
  π₁ (π₁ τ ∘ σ , π₂ τ [ σ ] ∶[ [∘]T _ σ (π₁ τ) ])
    ≡⟨ βπ₁ (π₁ τ ∘ σ) (π₂ τ [ σ ]) ([∘]T _ _ _) ⟩
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
  → π₂ σ ≡ π₂ idS [ σ ]
π₂idS σ =
  π₂ σ
    ≡⟨ cong π₂ (sym (idS∘ σ)) ⟩
  π₂ (idS ∘ σ)
    ≡⟨ π₂∘ _ _ ⟩
  π₂ idS [ σ ]
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

-- syntax abbreviations
vz : Tm (Γ , A)
vz = π₂ idS

vs : Tm Γ → Tm (Γ , B)
vs x = x [ wk ]
-- vs (vs ... (vs vz) ...) = π₂ idS [ π₁ idS ]tm .... [ π₁ idS ]tm

-- -- vz:= : (t : Tm Γ) → let (_ , (σ , A)) = tyOf t in Sub Γ (Γ , A [ σ ])
-- -- vz:= {Γ} t = idS , t ∶[ {!!} ]
