open import Prelude
-- copy and modify from Theory
module SC+U+Pi+Id.Translation.Model.toQIIT where

open import SC+U+Pi+Id.QIIT.Syntax     as QIIT
open import SC+U+Pi+Id.QIIT.Properties as QIIT
open import SC+U+Pi+Id.QIIT.Elimination as QE

import SC+U+Pi+Id.QIIRT.Syntax as R
  hiding (i) 

import SC+U+Pi+Id.QIIRT.Elimination as RM

open ≡-Reasoning
module _ {ℓ ℓ′}(QM : Eliminator {ℓ} {ℓ′}) where
  open Eliminator QM
  open import SC+U+Pi+Id.Translation.Syntax.Translate
  open QIIRT→QIIT
  
  toQIIT : RM.Eliminator {ℓ} {ℓ′}
  toQIIT .RM.Eliminator.mot = record
    { Ctxᴹ = λ Γ → Ctxᴹ (Γ >c)
    ; Tyᴹ  = λ Γᴹ i A → Tyᴹ Γᴹ i (A >ty)
    ; Subᴹ = λ Γᴹ Δᴹ σ → Subᴹ Γᴹ Δᴹ (σ >s)
    ; Tmᴹ  = λ Γᴹ Aᴹ t → Tmᴹ Γᴹ Aᴹ (t >tm)
    }
  toQIIT .RM.Eliminator.met = record
    { 𝒞    = record
      { [_]ᴹ_       = λ {Γ} {Γᴹ} {Δ} {Δᴹ} {σ} {i} {A} σᴹ Aᴹ → tr TyᴹFam ([]>ty σ A) ([ σᴹ ]ᴹ Aᴹ)
      ; ∅ᶜᴹ         = ∅ᶜᴹ
      ; _,ᶜᴹ_       = _,ᶜᴹ_
      ; ∅ˢᴹ         = ∅ˢᴹ
      ; _,ˢᴹ_       = λ {Γ} {Γᴹ} {Δ} {Δᴹ} {σ} {_} {A} {Aᴹ} {t} σᴹ tᴹ
                    → σᴹ ,ˢᴹ
                      trTmᴹₜ (sym $ []>ty σ A)
                                      (tr² ([]>ty σ A) ∙ cong (λ p → tr TyᴹFam p ([ σᴹ ]ᴹ Aᴹ)) (trans-symʳ ([]>ty σ A)))
                                      tᴹ
      ; idSᴹ        = idSᴹ
      ; _⨟ᴹ_        = _⨟ᴹ_
          -- λ {Γ} {Γᴹ} {Δ} {Δᴹ} {τ} {Θ} {Θᴹ} {σ} τᴹ σᴹ → τᴹ ⨟ᴹ σᴹ
      ; π₁ᴹ         = π₁ᴹ
          -- λ {Γ} {Γᴹ} {Δ} {Δᴹ} {i} {A} {Aᴹ} {σ} σᴹ → π₁ᴹ σᴹ
      ; [idSᴹ]      = λ {Γ} {Γᴹ} {i} {A} {Aᴹ}
                    → cong (tr TyᴹFam ([]>ty R.idS A)) (flip [idSᴹ])
                    ∙ tr² (sym [idS]) {[]>ty R.idS A}
                    ∙ cong (λ p → tr TyᴹFam p Aᴹ) (uip (sym [idS] ∙ []>ty R.idS A) refl)
      ; [⨟ᴹ]ᴹ       = λ {Γ} {Γᴹ} {Δ} {Δᴹ} {τ} {τᴹ} {Θ} {Θᴹ} {σ} {σᴹ} {i} {A} {Aᴹ}
                    → cong (tr TyᴹFam ([]>ty (τ R.⨟ σ) A)) (flip [⨟ᴹ]ᴹ)
                    ∙ tr² (sym [⨟]) {[]>ty (τ R.⨟ σ) A}
                    ∙ cong (λ p → tr TyᴹFam p ([ τᴹ ]ᴹ ([ σᴹ ]ᴹ Aᴹ)))
                           (uip (sym [⨟] ∙ []>ty (τ R.⨟ σ) A) (cong ([ τ >s ]_) ([]>ty σ A) ∙ []>ty τ (R.[ σ ] A)))
                    ∙ sym (
                      cong (tr TyᴹFam ([]>ty τ (R.[ σ ] A))) (sym $ tr-nat TyᴹFam (λ _ x → [ τᴹ ]ᴹ x) ([]>ty σ A))
                    ∙ cong (tr TyᴹFam ([]>ty τ (R.[ σ ] A))) (tr-cong ([]>ty σ A))
                    ∙ tr² (cong ([ τ >s ]_) ([]>ty σ A)) {[]>ty τ (R.[ σ ] A)}
                    )
      ; [π₁ᴹ,ˢᴹ]ᴹ   = λ {Γ} {Γᴹ} {Δ} {Δᴹ} {σ} {σᴹ} {i} {A'} {t} {A'ᴹ} {tᴹ} {j} {A} {Aᴹ}
                    → cong (tr TyᴹFam ([]>ty (R.π₁ (σ R., t)) A)) (flip $ [π₁ᴹ,ˢᴹ]ᴹ σᴹ (trTmᴹₜ _ _ tᴹ) Aᴹ)
                    ∙ tr² (sym $ cong ([_] A >ty) π₁,) {[]>ty (R.π₁ (σ R., t)) A}
                    ∙ cong (λ p → tr TyᴹFam p ([ σᴹ ]ᴹ Aᴹ))
                           (uip (sym (cong ([_] A >ty) π₁,) ∙ []>ty (R.π₁ (σ R., t)) A) ([]>ty σ A))
      ; [π₁ᴹ⨟ᴹ]ᴹ    = {!   !}
      ; π₂ᴹ         = λ {Γ} {Γᴹ} {Δ} {Δᴹ} {i} {A} {Aᴹ} {σ} σᴹ
                    → trTmᴹₜ ([]>ty (R.π₁ σ) A) refl (π₂ᴹ σᴹ)
      ; [_]tmᴹ_     = λ {Γ} {Γᴹ} {Δ} {Δᴹ} {σ} {i} {A} {t} σᴹ {Aᴹ} tᴹ
                    → trTmᴹₜ ([]>ty σ A) refl ([ σᴹ ]tmᴹ tᴹ)
      ; _↑ᴹ_        = {!   !}
      -- ; idSᴹ↑ᴹ      = {!   !}
      -- ; ⨟ᴹ↑ᴹ        = {!   !}
      -- ; π₁ᴹ,ˢᴹ↑ᴹ    = {!   !}
      -- ; π₁ᴹ⨟ᴹ↑ᴹ     = {!   !}
      -- ; ∅ˢᴹ↑ᴹ       = {!   !}
      -- ; ,ˢᴹ↑ᴹ       = {!   !}
      -- ; π₁ᴹidSᴹ↑ᴹ   = {!   !}
      -- ; π₁ᴹπ₁ᴹ↑ᴹ    = {!   !}
      -- ; [_]tᴹ_      = {!   !}
      -- ; [idSᴹ]tᴹ    = {!   !}
      -- ; [⨟ᴹ]tᴹ      = {!   !}
      -- ; [π₁ᴹ,ˢᴹ]tᴹ  = {!   !}
      -- ; [π₁ᴹ⨟ᴹ]tᴹ   = {!   !}
      -- ; [∅ˢᴹ]tᴹ     = {!   !}
      -- ; [,ˢᴹ]tᴹ     = {!   !}
      -- ; [π₁ᴹidSᴹ]tᴹ = {!   !}
      -- ; [π₁ᴹπ₁ᴹ]tᴹ  = {!   !}
      -- ; _⨟ᴹidSᴹ     = λ _
      --   → {!   !}
      -- ; idSᴹ⨟ᴹ_     = λ σᴹ
      --   → {!   !}
      -- ; ⨟ᴹ-assoc    = {!   !}
      -- ; π₁ᴹ,ˢᴹ      = {!   !}
      -- ; ⨟ᴹ,ˢᴹ       = {!   !}
      -- ; η∅ˢᴹ        = {!   !}
      -- ; η,ˢᴹ        = {!   !}
      -- ; [idSᴹ]tmᴹ   = {!   !}
      -- ; [⨟ᴹ]tmᴹ     = {!   !}
      -- ; π₂ᴹ,ˢᴹ      = {!   !}
      }
    }
    -- ; univ =
    --   record
    --   { Uᴹ       = {!   !}
    --   ; Elᴹ      = {!   !}
    --   ; Liftᴹ    = {!   !}
    --   ; cᴹ       = {!   !}
    --   ; mkᴹ      = {!   !}
    --   ; unᴹ      = {!   !}
    --   ; []ᴹUᴹ    = {!   !}
    --   ; []ᴹElᴹ   = {!   !}
    --   ; []ᴹLiftᴹ = {!   !}
    --   ; []tᴹcᴹ   = {!   !}
    --   ; []mkᴹ    = {!   !}
    --   ; []unᴹ    = {!   !}
    --   ; Uᴹβ      = {!   !}
    --   ; Uᴹη      = {!   !}
    --   ; Liftᴹβ   = {!   !}
    --   ; Liftᴹη   = {!   !}
    --   }
    -- ; piTy = record
    --   { Πᴹ    = {!   !}
    --   ; ƛᴹ_   = {!   !}
    --   ; appᴹ  = {!   !}
    --   ; []ᴹΠᴹ = {!   !}
    --   ; []ƛᴹ  = {!   !}
    --   ; Πβᴹ = {!   !}
    --   ; Πηᴹ = {!   !}
    --   }
    -- ; idTy = record
    --   { Idᴹ      = {!   !}
    --   ; []ᴹIdᴹ   = {!   !}
    --   ; reflᴹ    = {!   !}
    --   ; []reflᴹ  = {!   !}
    --   ; reflectᴹ = {!   !}
      -- }
    -- }
