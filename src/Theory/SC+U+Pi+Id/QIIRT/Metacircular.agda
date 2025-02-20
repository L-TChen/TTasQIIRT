open import Prelude

module SC+U+Pi+Id.QIIRT.Metacircular where

open import Level

open import SC+U+Pi+Id.QIIRT.Syntax
open import SC+U+Pi+Id.QIIRT.Recursion
open Recursor

intp : Recursor
intp .mot = record
  { Ctxᴹ = Set 
  ; Tyᴹ  = λ Γᴹ _ → Γᴹ → Set
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
    ; [π₁,ᴹ]ᴹ     = refl
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
  ; univ = {! !} -- requires a proper treatment for Coquand universes
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
    ; []Idᴹ    = {! !} -- refl
    ; reflᴹ    = λ t γ → refl
    ; []reflᴹ  = {! !}
    ; reflectᴹ = {! !} -- requires function extensionality
    }
  }
