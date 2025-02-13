open import Prelude

module SC+U+Pi+Id.QIIRT.Metacircular where

open import Level

open import SC+U+Pi+Id.QIIRT.Syntax
open import SC+U+Pi+Id.QIIRT.Recursion
open Recursor

intp : Recursor
intp .Mot = record
  { Ctxᴹ = Set 
  ; Tyᴹ  = λ Γᴹ _ → Γᴹ → Set
  ; Subᴹ = λ Γᴹ Δᴹ → Γᴹ → Δᴹ
  ; Tmᴹ  = λ Γᴹ Aᴹ → (γ : Γᴹ) → Aᴹ γ
  }
intp .Met = record
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
    ; _⨟ᴹidSᴹ     = λ σᴹ → refl
    ; idSᴹ⨟ᴹ_     = λ σᴹ → refl
    ; ⨟ᴹ-assoc    = refl
    ; π₁ᴹ,ˢᴹ      = refl
    ; ⨟ᴹ,ˢᴹ       = refl 
    ; η∅ˢᴹ        = refl
    ; η,ˢᴹ        = refl
    ; [idSᴹ]tmᴹ   = refl
    ; [⨟ᴹ]tmᴹ     = refl
    ; π₂ᴹ,ˢᴹ      = refl
    }
  ; univ = {!!} -- requires a proper treatment for Coquand universes
  ; piTy = record
    { Πᴹ    = λ Aᴹ Bᴹ γ → (x : Aᴹ γ) → Bᴹ (γ , x)
    ; ƛᴹ_   = λ tᴹ γ x → tᴹ (γ , x)
    ; appᴹ  = λ tᴹ (γ , x) → tᴹ γ x
    ; []ᴹΠᴹ = refl
    ; []ƛᴹ  = λ σ σᴹ → refl
    ; Πβᴹ   = refl 
    ; Πηᴹ   = refl
    }
  ; idTy = record
    { Idᴹ      = λ aᴹ tᴹ uᴹ γ → tᴹ γ ≡ uᴹ γ
    ; []ᴹIdᴹ   = {!!} -- refl
    ; reflᴹ    = λ t γ → refl
    ; []reflᴹ  = {!!}
    ; reflectᴹ = {!!} -- requires function extensionality
    }
  }
