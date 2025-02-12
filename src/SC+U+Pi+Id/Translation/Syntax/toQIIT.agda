open import Prelude
-- copy and modify from Theory
module SC+U+Pi+Id.Translation.Syntax.toQIIT where

open import SC+U+Pi+Id.QIIT.Syntax
open import SC+U+Pi+Id.QIIT.Properties
open import SC+U+Pi+Id.QIIRT.Recursion

open ≡-Reasoning
open Recursor

toQIIT : Recursor
toQIIT .Mot = record
  { Ctxᴹ = Ctx
  ; Tyᴹ  = Ty
  ; Subᴹ = Sub
  ; Tmᴹ  = Tm
  }
toQIIT .Met = record
  { 𝒞    = record
    { [_]ᴹ_       = [_]_
    ; ∅ᶜᴹ         = ∅
    ; _,ᶜᴹ_       = _,_
    ; ∅ˢᴹ         = ∅
    ; _,ˢᴹ_       = _,_
    ; idSᴹ        = idS
    ; _⨟ᴹ_        = _⨟_
    ; π₁ᴹ         = π₁
    ; [idSᴹ]      = [idS]
    ; [⨟ᴹ]ᴹ       = [⨟]
    ; [π₁ᴹ,ˢᴹ]ᴹ   = λ {Γ} {Δ} {σ} {_} {A} {t} {_} {B}
      → cong ([_] B) π₁,
    ; [π₁ᴹ⨟ᴹ]ᴹ    = λ {Γ} {Δ} {σ} {Θ} {_} {A} {τ} {_} {B}
      → cong ([_] B) (π₁⨟ σ τ)  ∙ [⨟] 
    ; π₂ᴹ         = π₂
    ; [_]tmᴹ_     = [_]tm_
    ; _↑ᴹ_        = _↑_
    ; idSᴹ↑ᴹ      = id⁺ _ _
    ; ⨟ᴹ↑ᴹ        = ⨟⁺ _ _ _
    ; π₁ᴹ,ˢᴹ↑ᴹ    = π₁,⁺
    ; π₁ᴹ⨟ᴹ↑ᴹ     = π₁⨟⁺
    ; ∅ˢᴹ↑ᴹ       = refl
    ; ,ˢᴹ↑ᴹ       = refl
    ; π₁ᴹidSᴹ↑ᴹ   = refl
    ; π₁ᴹπ₁ᴹ↑ᴹ    = refl
    ; [_]tᴹ_      = [_]tm_
    ; [idSᴹ]tᴹ    = [idS]tm
    ; [⨟ᴹ]tᴹ      = [⨟]tm
    ; [π₁ᴹ,ˢᴹ]tᴹ  = (sym $ tr-cong π₁,) ∙ apd ([_]tm _) π₁,
    ; [π₁ᴹ⨟ᴹ]tᴹ   = λ {Γ} {Δ} {σ} {Θ} {_} {A} {τ} {_} {B} {t} →
      begin -- L-T (11-01-2025: All about transports ...)
        tr (Tm Γ) (trans (cong ([_] B) (π₁⨟ σ τ)) [⨟]) ([ π₁ (σ ⨟ τ) ]tm t)
          ≡⟨ tr² (cong ([_] B) (π₁⨟ σ τ)) ⟨
        tr (Tm Γ) [⨟] (tr (Tm Γ) (cong ([_] B) (π₁⨟ σ τ)) ([ π₁ (σ ⨟ τ) ]tm t))
          ≡⟨ cong (tr (Tm Γ) [⨟]) (tr-cong (π₁⨟ σ τ)) ⟨
        tr (Tm Γ) [⨟] (tr (λ σ → Tm Γ ([ σ ] B)) (π₁⨟ σ τ) ([ π₁ (σ ⨟ τ) ]tm t))
          ≡⟨ cong (tr (Tm Γ) [⨟]) (apd ([_]tm t) (π₁⨟ σ τ)) ⟩
        tr (Tm Γ) [⨟] ([ σ ⨟ π₁ τ ]tm t)
          ≡⟨ [⨟]tm ⟩
        [ σ ]tm [ π₁ τ ]tm t
          ∎
    ; [∅ˢᴹ]tᴹ     = refl
    ; [,ˢᴹ]tᴹ     = refl
    ; [π₁ᴹidSᴹ]tᴹ = refl
    ; [π₁ᴹπ₁ᴹ]tᴹ  = refl
    ; _⨟ᴹidSᴹ     = _⨟idS
    ; idSᴹ⨟ᴹ_     = idS⨟_
    ; ⨟ᴹ-assoc    = ⨟-assoc
    ; π₁ᴹ,ˢᴹ      = π₁,
    ; ⨟ᴹ,ˢᴹ       = ⨟,
    ; η∅ˢᴹ        = η∅
    ; η,ˢᴹ        = η,
    ; [idSᴹ]tmᴹ   = [idS]tm
    ; [⨟ᴹ]tmᴹ     = [⨟]tm
    ; π₂ᴹ,ˢᴹ      = λ {Γ} {Δ} {σ} {_} {A} {t} → begin
      tr (Tm Γ) (cong ([_] A) π₁,) (π₂ (σ , t))
        ≡⟨ tr-cong π₁, ⟨
      tr (λ σ → Tm Γ ([ σ ] A)) π₁, (π₂ (σ , t))
        ≡⟨ π₂, ⟩
      t ∎

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
    ; []tᴹcᴹ   = []tc
    ; []mkᴹ    = []mk
    ; []unᴹ    = []un
    ; Uᴹβ      = Uβ
    ; Uᴹη      = Uη
    ; Liftᴹβ   = Liftβ
    ; Liftᴹη   = Liftη
    }
  ; piTy = record
    { Πᴹ    = Π
    ; ƛᴹ_   = ƛ_
    ; appᴹ  = app
    ; []ᴹΠᴹ = []Π
    ; []ƛᴹ  = []ƛ
    ; Πβᴹ   = Πβ
    ; Πηᴹ   = Πη
    }
  ; idTy = record
    { Idᴹ      = Id
    ; []ᴹIdᴹ   = []Id
    ; reflᴹ    = refl
    ; []reflᴹ  = []refl
    ; reflectᴹ = reflect
    }
  }
