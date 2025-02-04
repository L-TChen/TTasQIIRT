open import Prelude
  hiding (⊤; tt)

module SC+U+Pi+Id.QIIT.Metacircular where

open import Level
open import Data.Unit.Polymorphic

open import SC+U+Pi+Id.QIIT.Syntax
open import SC+U+Pi+Id.QIIT.Elimination
open import SC+U+Pi+Id.QIIT.Elimination.Motive
open import SC+U+Pi+Id.QIIT.Elimination.Method
open Eliminator
open Motive

module _ (fext : ∀{ℓ ℓ'}{A : Set ℓ}{B : A → Set ℓ'}{f g : (a : A) → B a}
               → (∀ x → f x ≡ g x)
               → f ≡ g) where
  intp : Eliminator
  intp .mot = record
    { Ctxᴹ = λ _ → Set 
    ; Tyᴹ  = λ Γᴹ _ _ → Γᴹ → Set
    ; Subᴹ = λ Γᴹ Δᴹ _ → Γᴹ → Δᴹ
    ; Tmᴹ  = λ Γᴹ Aᴹ t → (γ : Γᴹ) → Aᴹ γ
    }
  intp .met = record
    { 𝒞 = record
      { C₁ = record
        { [_]ᴹ_ = λ σᴹ Aᴹ γ → Aᴹ (σᴹ γ)
        ; ∅ᶜᴹ = ⊤
        ; _,ᶜᴹ_ = Σ
        ; ∅ˢᴹ = λ _ → tt
        ; _,ˢᴹ_ = λ σᴹ tᴹ γ → σᴹ γ , tᴹ γ
        ; idSᴹ = id
        ; _⨟ᴹ_ = λ σᴹ τᴹ → τᴹ ∘ σᴹ
        ; π₁ᴹ = λ σᴹ γ → σᴹ γ .proj₁
        ; [idSᴹ] = tr-const [idS]
        ; [⨟ᴹ]ᴹ = tr-const [⨟]
        ; π₂ᴹ = λ σᴹ γ → σᴹ γ .proj₂
        ; [_]tmᴹ_ = λ σᴹ tᴹ γ → tᴹ (σᴹ γ)
        }
      ; C₂ = record
        { _⨟ᴹidSᴹ = λ {_} {_} {_} {_} {σ} _ → tr-const (σ ⨟idS)
        ; idSᴹ⨟ᴹ_ = λ {_} {_} {_} {_} {σ} _ → tr-const (idS⨟ σ)
        ; ⨟ᴹ-assoc = tr-const ⨟-assoc
        ; π₁ᴹ,ˢᴹ = tr-const π₁,
        ; ⨟ᴹ,ˢᴹ = λ {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_}
                    {σᴹ} {τᴹ} {tᴹ}
                → tr-const ⨟, ∙ fext λ γ → cong (τᴹ (σᴹ γ) ,_) {!   !}
        ; η∅ˢᴹ = λ {Γ} {_} {σ} {_} → tr-const (η∅ {Γ} {σ})
        ; η,ˢᴹ = tr-const η,
        ; [idSᴹ]tmᴹ = λ {Γ} {Γᴹ} {i} {A} {Aᴹ} {t} {tᴹ} 
                    → tr-const [idS]tm ∙ 
                      let I = Σ (Ty Γ i) λ A → Motive.Tyᴹ (intp .mot) Γᴹ i A × Tm Γ A
                      in {!   !}
                      -- cong (λ p → tr (λ ((A , (Aᴹ , t))) → Tmᴹ Γᴹ Aᴹ t) p tᴹ) refl 
        ; [⨟ᴹ]tmᴹ = λ {Γ} {Γᴹ} {Δ} {Δᴹ} {σ} {σᴹ} {Θ} {Θᴹ} {τ} {τᴹ} {_} {_} {_} {_} {tᴹ}
                  → tr-const [⨟]tm ∙ {! [⨟]  !}
        ; π₂ᴹ,ˢᴹ = tr-const π₂, ∙ {!   !}
      }
      }
    ; univ = record
      { Uᴹ = {!   !}
      ; Elᴹ = {!   !}
      ; Liftᴹ = {!   !}
      ; cᴹ = {!   !}
      ; mkᴹ = {!   !}
      ; unᴹ = {!   !}
      ; []ᴹUᴹ = {!   !}
      ; []ᴹElᴹ = {!   !}
      ; []ᴹLiftᴹ = {!   !}
      ; []tᴹcᴹ = {!   !}
      ; []mkᴹ = {!   !}
      ; []unᴹ = {!   !}
      ; Uᴹβ = {!   !}
      ; Uᴹη = {!   !}
      ; Liftᴹβ = {!   !}
      ; Liftᴹη = {!   !}
      }
    ; piTy = record
      { Πᴹ    = λ Aᴹ Bᴹ γ → (x : Aᴹ γ) → Bᴹ (γ , x)
      ; ƛᴹ_   = λ tᴹ γ x → tᴹ (γ , x)
      ; appᴹ  = λ tᴹ (γ , x) → tᴹ γ x
      ; []ᴹΠᴹ = tr-const []Π ∙ {! refl  !} -- refl
      ; []ƛᴹ  = λ σ σᴹ → tr-const ([]ƛ σ _) ∙ {!   !}
      ; Πβᴹ   = tr-const Πβ
      ; Πηᴹ   = tr-const Πη
      }
    ; idTy = {!   !}
    }

  {-
  intp .met = record
    { 𝒞 = record
      { [_]ᴹ_       = λ σᴹ tᴹ γ → tᴹ (σᴹ γ)
      ; ∅ᶜᴹ         = ⊤
      ; _,ᶜᴹ_       = Σ
      ; ∅ˢᴹ         = λ _ → tt
      ; _,ˢᴹ_       = λ σᴹ tᴹ γ → σᴹ γ , tᴹ γ
      ; idSᴹ        = λ γ → γ
      ; _⨟ᴹ_        = λ σᴹ τᴹ → τᴹ ∘ σᴹ
      ; π₁ᴹ         = λ σᴹ γ → σᴹ γ .proj₁
      ; [idSᴹ]      = refl
      ; [⨟ᴹ]ᴹ       = refl
      ; [π₁ᴹ,ˢᴹ]ᴹ   = refl
      ; [π₁ᴹ⨟ᴹ]ᴹ    = refl
      ; π₂ᴹ         = λ σᴹ γ → σᴹ γ .proj₂
      ; [_]tmᴹ_     = λ σᴹ tᴹ γ → tᴹ (σᴹ γ)
      ; _↑ᴹ_        = λ σᴹ Aᴹ (γ , tᴹ) → σᴹ γ , tᴹ
      ; idSᴹ↑ᴹ      = refl
      ; ⨟ᴹ↑ᴹ        = refl
      ; π₁ᴹ,ˢᴹ↑ᴹ    = refl
      ; π₁ᴹ⨟ᴹ↑ᴹ     = refl
      ; ∅ˢᴹ↑ᴹ       = refl
      ; ,ˢᴹ↑ᴹ       = refl
      ; π₁ᴹidSᴹ↑ᴹ   = refl
      ; π₁ᴹπ₁ᴹ↑ᴹ    = refl
      ; [_]tᴹ_      = λ σᴹ tᴹ γ → tᴹ (σᴹ γ)
      ; [idSᴹ]tᴹ    = refl
      ; [⨟ᴹ]tᴹ      = refl
      ; [π₁ᴹ,ˢᴹ]tᴹ  = refl
      ; [π₁ᴹ⨟ᴹ]tᴹ   = refl
      ; [∅ˢᴹ]tᴹ     = refl
      ; [,ˢᴹ]tᴹ     = refl
      ; [π₁ᴹidSᴹ]tᴹ = refl
      ; [π₁ᴹπ₁ᴹ]tᴹ  = refl
      ; _⨟ᴹidSᴹ     = λ σᴹ → tr-const (_ ⨟idS)
      ; idSᴹ⨟ᴹ_     = λ σᴹ → tr-const (idS⨟ _)
      ; ⨟ᴹ-assoc    = tr-const ⨟-assoc
      ; π₁ᴹ,ˢᴹ      = tr-const π₁,
      ; ⨟ᴹ,ˢᴹ       = tr-const ⨟,
      ; η∅ˢᴹ        = refl
      ; η,ˢᴹ        = tr-const η,
      ; [idSᴹ]tmᴹ   = tr-const [idS]tm
      ; [⨟ᴹ]tmᴹ     = tr-const [⨟]tm
      ; π₂ᴹ,ˢᴹ      = tr-const π₂,
      }
    ; univ = {!!} -- requires a proper treatment for Coquand universes
    ; piTy = record
      { Πᴹ    = λ Aᴹ Bᴹ γ → (x : Aᴹ γ) → Bᴹ (γ , x)
      ; ƛᴹ_   = λ tᴹ γ x → tᴹ (γ , x)
      ; appᴹ  = λ tᴹ (γ , x) → tᴹ γ x
      ; []ᴹΠᴹ = refl
      ; []ƛᴹ  = λ σ σᴹ → tr-const ([]ƛ σ _) 
      }
    ; idTy = {!!} -- requires a proper treatment for Coquand universes and function extensionality
    }
  -}