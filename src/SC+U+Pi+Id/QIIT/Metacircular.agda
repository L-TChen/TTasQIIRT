open import Prelude
  hiding (⊤; tt)

module SC+U+Pi+Id.QIIT.Metacircular where

open import Level
open import Data.Unit.Polymorphic

open import SC+U+Pi+Id.QIIT.Syntax
open import SC+U+Pi+Id.QIIT.Recursion
open Recursor

module _ (fext : ∀{ℓ ℓ'}{A : Set ℓ}{B : A → Set ℓ'}{f g : (a : A) → B a}
               → (∀ x → f x ≡ g x)
               → f ≡ g) where
  intp : Recursor
  intp .mot = record
    { Ctxᴹ = Set 
    ; Tyᴹ  = λ Γᴹ _ → Γᴹ → Set
    ; Subᴹ = λ Γᴹ Δᴹ → Γᴹ → Δᴹ
    ; Tmᴹ  = λ Γᴹ Aᴹ → (γ : Γᴹ) → Aᴹ γ
    }
  intp .met = record
    { 𝒞    = record
      { C₁ = record
        { [_]ᴹ_ = λ σᴹ tᴹ γ → tᴹ (σᴹ γ)
        ; ∅ᶜᴹ   = ⊤
        ; _,ᶜᴹ_ = Σ
        ; ∅ˢᴹ   = λ _ → tt
        ; _,ˢᴹ_ = λ σᴹ tᴹ γ → σᴹ γ , tᴹ γ
        ; idSᴹ = λ γ → γ
        ; _⨟ᴹ_ = λ σᴹ τᴹ → τᴹ ∘ σᴹ
        ; π₁ᴹ  = λ σᴹ γ → σᴹ γ .proj₁
        ; [idSᴹ]  = refl
        ; [⨟ᴹ]ᴹ   = refl
        ; π₂ᴹ     = λ σᴹ γ → σᴹ γ .proj₂
        ; [_]tmᴹ_ = λ σᴹ tᴹ γ → tᴹ (σᴹ γ)
        }
      ; C₂ = record
        { _⨟ᴹidSᴹ   = λ σᴹ → refl
        ; idSᴹ⨟ᴹ_   = λ σᴹ → refl
        ; ⨟ᴹ-assoc  = refl
        ; π₁ᴹ,ˢᴹ    = refl
        ; ⨟ᴹ,ˢᴹ     = refl
        ; η∅ˢᴹ      = refl
        ; η,ˢᴹ      = refl
        ; [idSᴹ]tmᴹ = refl
        ; [⨟ᴹ]tmᴹ   = refl
        ; π₂ᴹ,ˢᴹ    = refl
        }
      }
    ; univ = {!!}
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
      ; []reflᴹ  = λ σᴹ tᴹ → ? -- refl
      ; reflectᴹ = {!!}-- requires function extensionality
      }
    }
