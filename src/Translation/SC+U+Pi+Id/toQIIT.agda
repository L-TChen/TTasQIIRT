open import Prelude

module Translation.SC+U+Pi+Id.toQIIT where

open import Theory.SC+U+Pi+Id.QIIT.Syntax     as QIIT
open import Theory.SC+U+Pi+Id.QIIT.Properties as QIIT

import Theory.SC+U+Pi+Id.QIIRT.Syntax as R
  hiding (i)

open import Theory.SC+U+Pi+Id.QIIRT.Elimination

open Eliminator

open ≡-Reasoning
toQIIT : Eliminator 
toQIIT .mot = record
  { Ctxᴹ = λ Γ → Ctx
  ; Tyᴹ  = λ Γ i A → Ty Γ i
  ; Subᴹ = λ Γ Δ σ → Sub Γ Δ
  ; Tmᴹ  = λ Γ A t → Tm Γ A
  }
toQIIT .met = record
  { 𝒞    = record
    { [_]ᴹ_       = [_]_
    ; ∅ᶜᴹ         = ∅
    ; _,ᶜᴹ_       = _,_
    ; ∅ˢᴹ         = ∅
    ; _,ˢᴹ_       = λ σ t → σ , t
    ; idSᴹ        = idS
    ; _⨟ᴹ_        = _⨟_
    ; π₁ᴹ         = π₁
    ; [idSᴹ]      = [idS]
    ; [⨟ᴹ]ᴹ       = [⨟]
    ; [π₁ᴹ,ˢᴹ]ᴹ   = λ {Aᴹ = Aᴹ} → cong ([_] Aᴹ) π₁,
    ; [π₁ᴹ⨟ᴹ]ᴹ    = λ {Aᴹ = Aᴹ} → cong ([_] Aᴹ) (π₁⨟ _ _) ∙ [⨟]
    ; π₂ᴹ         = π₂
    ; [_]tmᴹ_     = [_]tm_
    ; _↑ᴹ_        = λ σ A → σ ↑ A
    ; idSᴹ↑ᴹ      = id⁺ _ _
    ; ⨟ᴹ↑ᴹ        = λ {Γ} {Γᴹ} {Δ} {Δᴹ} {σ} {σᴹ} {Θ} {Θᴹ} {τ} {τᴹ} {_} {A} {Aᴹ} → ⨟⁺ σᴹ τᴹ Aᴹ
    ; π₁ᴹ,ˢᴹ↑ᴹ    = π₁,⁺
    ; π₁ᴹ⨟ᴹ↑ᴹ     = π₁⨟⁺
    ; ∅ˢᴹ↑ᴹ       = refl
    ; ,ˢᴹ↑ᴹ       = refl
    ; π₁ᴹidSᴹ↑ᴹ   = refl
    ; π₁ᴹπ₁ᴹ↑ᴹ    = refl
    ; [_]tᴹ_      = λ σ t → [ σ ]tm t
    ; [idSᴹ]tᴹ    = [idS]tm
    ; [⨟ᴹ]tᴹ      = [⨟]tm
    ; [π₁ᴹ,ˢᴹ]tᴹ  = (sym $ tr-cong π₁,) ∙ apd ([_]tm _) π₁,
    ; [π₁ᴹ⨟ᴹ]tᴹ   = λ {Γ} {Γᴹ} {Δ} {Δᴹ} {σ} {σᴹ} {Θ} {i} {A} {τ} {Θᴹ} {Aᴹ} {τᴹ} {j} {B} {Bᴹ} {t} {tᴹ}
      → begin -- L-T (11-01-2025: All about transports ...)
        tr (Tm Γᴹ) (trans (cong ([_] Bᴹ) (π₁⨟ σᴹ τᴹ)) [⨟]) ([ π₁ (σᴹ ⨟ τᴹ) ]tm tᴹ)
          ≡⟨ tr² (cong ([_] Bᴹ) (π₁⨟ σᴹ τᴹ)) ⟨
        tr (Tm Γᴹ) [⨟] (tr (Tm Γᴹ) (cong ([_] Bᴹ) (π₁⨟ σᴹ τᴹ)) ([ π₁ (σᴹ ⨟ τᴹ) ]tm tᴹ))
          ≡⟨ cong (tr (Tm Γᴹ) [⨟]) (tr-cong (π₁⨟ σᴹ τᴹ)) ⟨
        tr (Tm Γᴹ) [⨟] (tr (λ σ → Tm Γᴹ ([ σ ] Bᴹ)) (π₁⨟ σᴹ τᴹ) ([ π₁ (σᴹ ⨟ τᴹ) ]tm tᴹ))
          ≡⟨ cong (tr (Tm Γᴹ) [⨟]) (apd ([_]tm tᴹ) (π₁⨟ σᴹ τᴹ)) ⟩
        tr (Tm Γᴹ) [⨟] ([ σᴹ ⨟ π₁ τᴹ ]tm tᴹ)
          ≡⟨ [⨟]tm ⟩
        [ σᴹ ]tm [ π₁ τᴹ ]tm tᴹ
          ∎
    ; [∅ˢᴹ]tᴹ     = refl
    ; [,ˢᴹ]tᴹ     = refl
    ; [π₁ᴹidSᴹ]tᴹ = refl
    ; [π₁ᴹπ₁ᴹ]tᴹ  = refl
    ; _⨟ᴹidSᴹ     = λ _
      → (tr-const (_ R.⨟idS)) ∙ (_ ⨟idS)
    ; idSᴹ⨟ᴹ_     = λ σᴹ
      → (tr-const (R.idS⨟ _)) ∙ (idS⨟ _)
    ; ⨟ᴹ-assoc    = tr-const R.⨟-assoc ∙ ⨟-assoc
    ; π₁ᴹ,ˢᴹ      = tr-const R.π₁, ∙ π₁,
    ; ⨟ᴹ,ˢᴹ       = tr-const R.⨟, ∙ ⨟,
    ; η∅ˢᴹ        = tr-const R.η∅ ∙ η∅
    ; η,ˢᴹ        = tr-const R.η, ∙ η,
    ; [idSᴹ]tmᴹ   = cong (tr (Tm _) [idS]) (tr-const R.[idS]tm) ∙ [idS]tm
    ; [⨟ᴹ]tmᴹ     = cong (tr (Tm _) [⨟]) (tr-const R.[⨟]tm) ∙ [⨟]tm
    ; π₂ᴹ,ˢᴹ      = λ {Γ} {Γᴹ} {Δ} {Δᴹ} {σ} {σᴹ} {i} {A} {t} {Aᴹ} {tᴹ}
      → begin
        tr (Tm Γᴹ) (cong ([_] Aᴹ) π₁,) (tr (λ _ → Tm Γᴹ ([ π₁ (σᴹ , tᴹ) ] Aᴹ)) R.π₂, (π₂ (σᴹ , tᴹ)))
          ≡⟨ tr-cong π₁, ⟨
        tr (λ σ → Tm Γᴹ ([ σ ] Aᴹ)) π₁, (tr (λ _ → Tm Γᴹ ([ π₁ (σᴹ , tᴹ) ] Aᴹ)) R.π₂, (π₂ (σᴹ , tᴹ)))
          ≡⟨ cong (tr (λ σ → Tm Γᴹ ([ σ ] Aᴹ)) π₁,) (tr-const R.π₂,) ⟩
        tr (λ σ → Tm Γᴹ ([ σ ] Aᴹ)) π₁, (π₂ (σᴹ , tᴹ))
          ≡⟨ π₂, ⟩
        tᴹ
          ∎
    }
  ; univ = record
    { Uᴹ       = U
    ; Elᴹ      = El
    ; Liftᴹ    = Lift
    ; cᴹ       = c
    ; mkᴹ      = mk
    ; unᴹ      = un
    ; []ᴹUᴹ    = []U
    ; []ᴹElᴹ   = []El
    ; []ᴹLiftᴹ = []Lift
    ; []tᴹcᴹ   = λ σᴹ Aᴹ →
      cong (tr (Tm _) []U) (tr-const (R.[]tc _ _)) ∙ ([]tc σᴹ Aᴹ)
    ; []mkᴹ    = λ σ  σᴹ →
      cong (tr (Tm _) []Lift) (tr-const (R.[]mk σ _)) ∙ []mk σᴹ _
    ; []unᴹ    = λ σ σᴹ →
      tr-const (R.[]un σ _ _) ∙  []un σᴹ _ _
    ; Uᴹβ      = tr-const R.Uβ ∙ Uβ
    ; Uᴹη      = tr-const R.Uη ∙ Uη
    ; Liftᴹβ   = tr-const R.Liftβ ∙ Liftβ
    ; Liftᴹη   = tr-const R.Liftη ∙ Liftη
    }
  ; piTy = record
    { Πᴹ    = Π
    ; ƛᴹ_   = ƛ_
    ; appᴹ  = app
    ; []ᴹΠᴹ = []Π
    ; []ƛᴹ  = λ {Γ} {Δ} {Γᴹ} {Δᴹ} {i} {A} {B} {Aᴹ} {Bᴹ} {t} {tᴹ} σ σᴹ
      → cong (tr (Tm Γᴹ) []Π) (tr-const (R.[]ƛ σ t)) ∙ []ƛ σᴹ tᴹ }
  ; idTy = record
    { Idᴹ      = Id
    ; []ᴹIdᴹ   = []Id
    ; reflectᴹ = λ where
      {p = p} pᴹ → tr-const (R.reflect p) ∙ reflect pᴹ
    }
  }
