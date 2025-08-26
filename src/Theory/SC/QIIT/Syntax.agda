-- Doesn't pass the positivity checker

open import Prelude
  renaming (_,_ to _,,_)

module Theory.SC.QIIT.Syntax where

module Foo where
  module _ where -- delimit the scope of forward declarations
    data Ctx : Set
    data Sub : (Γ Δ : Ctx) → Set
    data Ty  : (Γ : Ctx) → Set
    data Tm  : (Γ : Ctx) (A : Ty Γ) → Set

    module Var where
      variable
          Γ Δ Θ Ξ : Ctx
          A B C D : Ty  Γ
          t u     : Tm  Γ A
          σ τ δ γ : Sub Γ Δ
    open Var

    infixl 8  _[_] _[_]T _[_]t
    infixr 10 _∘_
    infixl 4  _,_  _,S_ _≡Tm[_]_
      
    _≡Tm[_]_ : Tm Γ A → A ≡ B → Tm Γ B → Set
    t ≡Tm[ p ] u = PathP (λ i → Tm _ (p i)) t u
    {-# INLINE _≡Tm[_]_ #-}

    -- Substitution calculus
    ∅
      : Ctx
    _,_
      : (Γ : Ctx) (A : Ty Γ)
      → Ctx
    _[_]T
      : (A : Ty Δ) (σ : Sub Γ Δ)
      → Ty Γ
    _[_]t
      : (t : Tm Δ A) (σ : Sub Γ Δ)
      → Tm Γ (A [ σ ]T)
    ∅S
      : Sub Γ ∅
    _,S_
      : (σ : Sub Γ Δ) (t : Tm Γ (A [ σ ]T))
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
      : (σ : Sub Γ (Δ , A))
      → Tm Γ (A [ π₁ σ ]T)
    [idS]T
      : A ≡ A [ idS ]T
    [∘]T
      : (A : Ty Θ) (σ : Sub Γ Δ) (τ : Sub Δ Θ)
      → A [ τ ]T [ σ ]T ≡ A [ τ ∘ σ ]T
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
      : (σ : Sub Δ Θ) (t : Tm Δ (A [ σ ]T)) (τ : Sub Γ Δ)
      → (σ ,S t) ∘ τ
      ≡ (σ ∘ τ ,S tr (Tm Γ) ([∘]T A τ σ) (t [ τ ]t))
    ηπ
      : (σ : Sub Γ (Δ , A))
      → σ ≡ (π₁ σ ,S π₂ σ)
    η∅
      : (σ : Sub Γ ∅)
      → σ ≡ ∅S
    βπ₁
      : (σ : Sub Γ Δ) (t : Tm Γ (A [ σ ]T))
      → π₁ (σ ,S t) ≡ σ
    _↑_
      : (σ : Sub Γ Δ) (A : Ty Δ)
      → Sub (Γ , A [ σ ]T) (Δ , A)
    _↑_ {Γ} σ A =
      σ ∘ π₁ idS ,S tr (Tm (Γ , (A [ σ ]T))) ([∘]T _ _ _) (π₂ idS)
    βπ₂
      : (σ : Sub Γ Δ) (t : Tm Γ (A [ σ ]T))
      → π₂ (σ ,S t)
      ≡Tm[ cong (A [_]T) (βπ₁ _ _) ] t
    [idS]t
      : (t : Tm Γ A)
      → t ≡Tm[ [idS]T ] t [ idS ]t
    [∘]t
      : (t : Tm Θ A) (σ : Sub Γ Δ) (τ : Sub Δ Θ)
      → t [ τ ]t [ σ ]t ≡Tm[ [∘]T A σ τ ]
        t [ τ ∘ σ ]t

    -- Universe
    U
      : Ty Γ
    U[]
      : U [ σ ]T ≡ U

    -- the following are the actual constructors in Agda
    data Ctx where
      ∅'
        : Ctx 
      _,'_
        : (Γ : Ctx) (A : Ty Γ) → Ctx
      
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
--      Ty-is-set : isSet (Ty Γ)

    data Sub where
      ∅'
        : Sub Γ ∅
      _,'_
        : (σ : Sub Γ Δ) (t : Tm Γ (A [ σ ]T))
        → Sub Γ (Δ , A)
      idS'
        : Sub Γ Γ
      _∘'_
        : Sub Δ Θ → Sub Γ Δ
        → Sub Γ Θ
      π₁'
        : Sub Γ (Δ , A)
        → Sub Γ Δ
      βπ₁'
        : (σ : Sub Γ Δ) (t : Tm Γ (A [ σ ]T))
        → π₁ (σ ,S t) ≡ σ
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
        : (σ : Sub Δ Θ) (t : Tm Δ (A [ σ ]T)) (τ : Sub Γ Δ)
        → (σ ,S t) ∘ τ ≡
          (σ ∘ τ ,S tr (Tm Γ) ([∘]T _ τ σ) (t [ τ ]t))
      η∅'
        : (σ : Sub Γ ∅)
        → σ ≡ ∅S
      ηπ'
        : (σ : Sub Γ (Δ , A))
        → σ ≡ (π₁ σ ,S π₂ σ)
--      Sub-is-set
--        : isSet (Sub Γ Δ) -- Added for NbE

    data Tm where
      _[_] : (t : Tm Δ A)(σ : Sub Γ Δ)
        → Tm Γ (A [ σ ]T)
      π₂'
        : (σ : Sub Γ (Δ , A))
        → Tm Γ (A [ π₁ σ ]T)
      βπ₂'
        : (σ : Sub Γ Δ) (t : Tm Γ (A [ σ ]T)) 
        → π₂ (σ ,S t)
        ≡Tm[ cong (A [_]T) (βπ₁ σ t) ]
          t
      [idS]t'
        : (t : Tm Γ A)
        → t ≡Tm[ [idS]T ] t [ idS ]t
      [∘]t'
        : (t : Tm Θ A) (σ : Sub Γ Δ) (τ : Sub Δ Θ)
        → t [ τ ]t [ σ ]t
        ≡Tm[ [∘]T A σ τ ] t [ τ ∘ σ ]t
--      Tm-is-set
--        : isSet (Tm Γ) -- Added for NbE

    ∅       = ∅'
    _,_     = _,'_
    _[_]T   = _[_]
    _[_]t   = _[_]
    U       = U'
    U[]     = U[]'
    ∅S      = ∅'
    _,S_    = _,'_
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

open Foo public
  hiding
  ( ∅
  ; _,_
  ; _[_]T
  ; _[_]t
  ; U
  ; U[]
  ; ∅S
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

open Var

π₁∘
  : π₁ (τ ∘ σ) ≡ π₁ τ ∘ σ
π₁∘ {τ = τ} {σ = σ} = 
  π₁ (τ ∘ σ)
    ≡⟨ cong π₁ (cong (_∘ σ) (ηπ τ)) ⟩
  π₁ ((π₁ τ , π₂ τ) ∘ σ)
    ≡⟨ cong π₁ (,∘ (π₁ τ) (π₂ τ) σ) ⟩
  π₁ ((π₁ τ ∘ σ) , _)
    ≡⟨ βπ₁ _ _ ⟩
  π₁ τ ∘ σ
    ∎
π∘
  : Path ([ B ∶ Ty Γ ] × Tm Γ B)
    (A [ π₁ (τ ∘ σ)] ,, π₂ (τ ∘ σ)) (A [ π₁ τ ] [ σ ] ,, π₂ τ [ σ ])
π∘ {Γ} {Δ} {A} {Ξ} {τ} {σ} = 
 A [ π₁ (τ ∘ σ) ] ,, π₂ (τ ∘ σ)
   ≡⟨ {!!} ⟩
 A [ π₁ ((π₁ τ , π₂ τ) ∘ σ) ] ,, π₂ ((π₁ τ , π₂ τ) ∘ σ)
   ≡⟨ {!!} ⟩
 A [ π₁ ((π₁ τ ∘ σ) , tr (Tm Γ) ([∘]T _ _ _) (π₂ τ [ σ ])) ] ,,
   π₂ ((π₁ τ ∘ σ) , tr (Tm Γ) ([∘]T _ _ _) (π₂ τ [ σ ]))
   ≡⟨ {!!} ⟩
 A [ π₁ τ ∘ σ ] ,, tr (Tm Γ) ([∘]T _ _ _) (π₂ τ [ σ ])
   ≡⟨ {!!} ⟩
 A [ π₁ τ ] [ σ ] ,, π₂ τ [ σ ]
   ∎
