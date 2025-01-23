open import Prelude
-- copy and modify from Theory
module SC+U+Pi+Id.Translation.Model.toQIIT where

open import SC+U+Pi+Id.QIIT.Syntax     as QIIT
open import SC+U+Pi+Id.QIIT.Properties as QIIT
open import SC+U+Pi+Id.QIIT.Elimination as QE

import SC+U+Pi+Id.QIIRT.Base as R
  hiding (i) 

import SC+U+Pi+Id.QIIRT.Model as RM

open ≡-Reasoning
module _ {ℓ ℓ′}(QM : Eliminator {ℓ} {ℓ′}) where
  open Eliminator QM
  open import SC+U+Pi+Id.Translation.Syntax.Translate
    using (From_To_; QIIRT→QIIT)
  open From_To_ QIIRT→QIIT
  
  toQIIT : RM.Model {ℓ} {ℓ′}
  toQIIT .RM.Model.Mot = record
    { Ctxᴹ = λ Γ → Ctxᴹ (Γ >c)
    ; Tyᴹ  = λ Γᴹ i A → Tyᴹ Γᴹ i (A >ty)
    ; Subᴹ = λ Γᴹ Δᴹ σ → Subᴹ Γᴹ Δᴹ (σ >s)
    ; Tmᴹ  = λ Γᴹ Aᴹ t → Tmᴹ Γᴹ Aᴹ (t >tm)
    }
  toQIIT .RM.Model.Met = record
    { 𝒞    = record
      { [_]ᴹ_       = λ {Γ} {Γᴹ} {Δ} {Δᴹ} {σ} {i} {A} σᴹ Aᴹ → tr TyᴹFam ([]>ty σ A) ([ σᴹ ]ᴹ Aᴹ)
      ; ∅ᶜᴹ         = ∅ᶜᴹ
      ; _,ᶜᴹ_       = _,ᶜᴹ_
      ; ∅ˢᴹ         = ∅ˢᴹ
      ; _,ˢᴹ_       = λ {Γ} {Γᴹ} {Δ} {Δᴹ} {σ} {_} {A} {Aᴹ} {t} σᴹ tᴹ
                    → σᴹ ,ˢᴹ trTmᴹₜ (sym $ []>ty σ A)
                                    (tr² ([]>ty σ A) ∙ cong (λ p → tr TyᴹFam p ([ σᴹ ]ᴹ Aᴹ)) (trans-symʳ ([]>ty σ A)))
                                     tᴹ
      ; idSᴹ        = idSᴹ
      ; _⨟ᴹ_        = λ {Γ} {Γᴹ} {Δ} {Δᴹ} {τ} {Θ} {Θᴹ} {σ} τᴹ σᴹ → τᴹ ⨟ᴹ σᴹ
      ; π₁ᴹ         = λ {Γ} {Γᴹ} {Δ} {Δᴹ} {i} {A} {Aᴹ} {σ} σᴹ → π₁ᴹ σᴹ
      ; [idSᴹ]      = {!   !}
      ; [⨟ᴹ]ᴹ       = {!   !}
      ; [π₁ᴹ,ˢᴹ]ᴹ   = {!   !}
      ; [π₁ᴹ⨟ᴹ]ᴹ    = {!   !}
      ; π₂ᴹ         = {!   !}
      ; [_]tmᴹ_     = {!   !}
      ; _↑ᴹ_        = {!   !}
      ; idSᴹ↑ᴹ      = {!   !}
      ; ⨟ᴹ↑ᴹ        = {!   !}
      ; π₁ᴹ,ˢᴹ↑ᴹ    = {!   !}
      ; π₁ᴹ⨟ᴹ↑ᴹ     = {!   !}
      ; ∅ˢᴹ↑ᴹ       = {!   !}
      ; ,ˢᴹ↑ᴹ       = {!   !}
      ; π₁ᴹidSᴹ↑ᴹ   = {!   !}
      ; π₁ᴹπ₁ᴹ↑ᴹ    = {!   !}
      ; [_]tᴹ_      = {!   !}
      ; [idSᴹ]tᴹ    = {!   !}
      ; [⨟ᴹ]tᴹ      = {!   !}
      ; [π₁ᴹ,ˢᴹ]tᴹ  = {!   !}
      ; [π₁ᴹ⨟ᴹ]tᴹ   = {!   !}
      ; [∅ˢᴹ]tᴹ     = {!   !}
      ; [,ˢᴹ]tᴹ     = {!   !}
      ; [π₁ᴹidSᴹ]tᴹ = {!   !}
      ; [π₁ᴹπ₁ᴹ]tᴹ  = {!   !}
      ; _⨟ᴹidSᴹ     = λ _
        → {!   !}
      ; idSᴹ⨟ᴹ_     = λ σᴹ
        → {!   !}
      ; ⨟ᴹ-assoc    = {!   !}
      ; π₁ᴹ,ˢᴹ      = {!   !}
      ; ⨟ᴹ,ˢᴹ       = {!   !}
      ; η∅ˢᴹ        = {!   !}
      ; η,ˢᴹ        = {!   !}
      ; [idSᴹ]tmᴹ   = {!   !}
      ; [⨟ᴹ]tmᴹ     = {!   !}
      ; π₂ᴹ,ˢᴹ      = {!   !}
      }
    ; univ = record
      { Uᴹ       = {!   !}
      ; Elᴹ      = {!   !}
      ; Liftᴹ    = {!   !}
      ; cᴹ       = {!   !}
      ; mkᴹ      = {!   !}
      ; unᴹ      = {!   !}
      ; []ᴹUᴹ    = {!   !}
      ; []ᴹElᴹ   = {!   !}
      ; []ᴹLiftᴹ = {!   !}
      ; []tᴹcᴹ   = {!   !}
      ; []mkᴹ    = {!   !}
      ; []unᴹ    = {!   !}
      ; Uᴹβ      = {!   !}
      ; Uᴹη      = {!   !}
      ; Liftᴹβ   = {!   !}
      ; Liftᴹη   = {!   !}
      }
    ; piTy = record
      { Πᴹ    = {!   !}
      ; ƛᴹ_   = {!   !}
      ; appᴹ  = {!   !}
      ; []ᴹΠᴹ = {!   !}
      ; []ƛᴹ  = {!   !}
      ; Πβᴹ = {!   !}
      ; Πηᴹ = {!   !}
      }
    ; idTy = record
      { Idᴹ      = {!   !}
      ; []ᴹIdᴹ   = {!   !}
      ; reflectᴹ = {!   !}
      }
    }
