-- For simplicity in dealing with the universe levels in the object
-- theory, we turn on type in type in this module
-- This is needed as `intp` would otherwise need to live in Setω
{-# OPTIONS --type-in-type #-}
open import Prelude

module Theory.SC+U+Pi+Id.QIIRT.Metacircular where

open import Level
open import Axiom.Extensionality.Propositional

open import Theory.SC+U+Pi+Id.QIIRT.Syntax
open import Theory.SC+U+Pi+Id.QIIRT.Recursion
open Recursor

postulate
  funext : Extensionality _ _

intp : Recursor
intp .mot = record
  { Ctxᴹ = Set
  ; Tyᴹ  = λ Γᴹ i → Γᴹ → Set (natlevel i)
  ; Subᴹ = λ Γᴹ Δᴹ → Γᴹ → Δᴹ
  ; Tmᴹ  = λ Γᴹ Aᴹ → (γ : Γᴹ) → Aᴹ γ
  }
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
    ; [idS]ᴹ      = refl
    ; [⨟]ᴹ        = refl
    ; [π₁,]ᴹ     = refl
    ; [π₁⨟]ᴹ      = refl
    ; π₂ᴹ         = λ σᴹ γ → σᴹ γ .proj₂
    ; [_]tmᴹ_     = λ σᴹ tᴹ γ → tᴹ (σᴹ γ)
    ; _↑ᴹ_        = λ σᴹ Aᴹ (γ , tᴹ) → σᴹ γ , tᴹ
    ; idS↑ᴹ       = refl
    ; ⨟↑ᴹ         = refl
    ; π₁,↑ᴹ       = refl
    ; π₁⨟↑ᴹ       = refl
    ; ∅↑ᴹ         = refl
    ; ,↑ᴹ         = refl
    ; π₁idS↑ᴹ     = refl
    ; π₁π₁↑ᴹ      = refl
    ; [_]tᴹ_      = λ σᴹ tᴹ γ → tᴹ (σᴹ γ)
    ; [idS]tᴹ     = refl
    ; [⨟]tᴹ       = refl
    ; [π₁,]tᴹ     = refl
    ; [π₁⨟]tᴹ     = refl
    ; [∅]tᴹ       = refl
    ; [,]tᴹ       = refl
    ; [π₁idS]tᴹ   = refl
    ; [π₁π₁]tᴹ    = refl
    ; _⨟idSᴹ      = λ σᴹ → refl
    ; idS⨟ᴹ_      = λ σᴹ → refl
    ; ⨟-assocᴹ    = refl
    ; π₁,ᴹ        = refl
    ; ⨟,ᴹ         = refl
    ; η∅ᴹ         = refl
    ; η,ᴹ         = refl
    ; [idS]tmᴹ    = refl
    ; [⨟]tmᴹ      = refl
    ; π₂,ᴹ        = refl
    }
  ; univ = record
            { Uᴹ = λ i _ → Set (natlevel i)
            ; Elᴹ = λ a γ → a γ
            ; Liftᴹ = λ A γ → Level.Lift _ (A γ)
            ; cᴹ = λ A γ → A γ
            ; mkᴹ = λ a γ → Level.lift (a γ)
            ; unᴹ = λ a γ → Level.lower (a γ)
            ; []Uᴹ = refl
            ; []Elᴹ = λ σᴹ uᴹ → refl
            ; []Liftᴹ = refl
            ; []tcᴹ = λ σᴹ Aᴹ → refl
            ; []mkᴹ = λ σᴹ tᴹ → refl
            ; []unᴹ = λ σᴹ Aᴹ tᴹ → refl
            ; Uβᴹ = refl
            ; Uηᴹ = refl
            ; Liftβᴹ = refl
            ; Liftηᴹ = refl
            }
  ; piTy = record
    { Πᴹ    = λ Aᴹ Bᴹ γ → (x : Aᴹ γ) → Bᴹ (γ , x)
    ; ƛᴹ_   = λ tᴹ γ x → tᴹ (γ , x)
    ; appᴹ  = λ tᴹ (γ , x) → tᴹ γ x
    ; []Πᴹ  = refl
    ; []ƛᴹ  = λ σ σᴹ → refl
    ; Πβᴹ   = refl
    ; Πηᴹ   = refl
    }
  ; idTy = record
    { Idᴹ      = λ aᴹ tᴹ uᴹ γ → tᴹ γ ≡ uᴹ γ
    ; []Idᴹ    = refl
    ; reflᴹ    = λ t γ → refl
    ; []reflᴹ  = λ σᴹ tᴹ → refl
    ; reflectᴹ = funext
    }
  }
