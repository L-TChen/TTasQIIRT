open import Prelude

module Theory.SC+U+Pi+Id.QIIRT.Metacircular where

open import Level

open import Theory.SC+U+Pi+Id.QIIRT.Syntax
open import Theory.SC+U+Pi+Id.QIIRT.Elimination
open import Theory.SC+U+Pi+Id.QIIRT.Elimination.Motive
open import Theory.SC+U+Pi+Id.QIIRT.Elimination.Method
open Eliminator
open Motive

intp : Eliminator
intp .mot = record
  { Ctxᴹ = λ _ → Set 
  ; Tyᴹ  = λ Γᴹ _ _ → Γᴹ → Set
  ; Subᴹ = λ Γᴹ Δᴹ _ → Γᴹ → Δᴹ
  ; Tmᴹ  = λ Γᴹ Aᴹ t → (γ : Γᴹ) → Aᴹ γ
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
  ; idTy = {!!} -- requires a proper treatment for Coquand universes
  }
