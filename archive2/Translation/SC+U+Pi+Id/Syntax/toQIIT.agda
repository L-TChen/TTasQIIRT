open import Prelude
-- copy and modify from Theory
module Translation.SC+U+Pi+Id.Syntax.toQIIT where

open import Theory.SC+U+Pi+Id.QIIT.Syntax
open import Theory.SC+U+Pi+Id.QIIT.Properties
open import Theory.SC+U+Pi+Id.QIIRT.Recursion

open ≡-Reasoning
open Recursor

toQIIT : Recursor
toQIIT .mot = record
  { Ctxᴹ = Ctx
  ; Tyᴹ  = Ty
  ; Subᴹ = Sub
  ; Tmᴹ  = Tm
  }
toQIIT .met = record
  { 𝒞    = record
    { [_]ᴹ_       = [_]_
    ; ∅ᶜᴹ         = ∅
    ; _,ᶜᴹ_       = _,_
    ; ∅ˢᴹ         = ∅
    ; _,ˢᴹ_       = _,_
    ; idSᴹ        = idS
    ; _⨟ᴹ_        = _⨟_
    ; π₁ᴹ         = π₁
    ; [idS]ᴹ      = [idS]
    ; [⨟]ᴹ       = [⨟]
    ; [π₁,]ᴹ   = λ {Γ} {Δ} {σ} {_} {A} {t} {_} {B} → cong ([_] B) π₁,
    ; [π₁⨟]ᴹ    = λ {Γ} {Δ} {σ} {Θ} {_} {A} {τ} {_} {B} → cong ([_] B) (π₁⨟ σ τ)  ∙ [⨟] 
    ; π₂ᴹ         = π₂
    ; [_]tmᴹ_     = [_]tm_
    ; _↑ᴹ_        = _↑_
    ; idS↑ᴹ      = id⁺ _ _
    ; ⨟↑ᴹ        = ⨟⁺ _ _ _
    ; π₁,↑ᴹ    = π₁,⁺
    ; π₁⨟↑ᴹ     = π₁⨟⁺
    ; ∅↑ᴹ       = refl
    ; ,↑ᴹ       = refl
    ; π₁idS↑ᴹ   = refl
    ; π₁π₁↑ᴹ    = refl
    ; [_]tᴹ_      = [_]tm_
    ; [idS]tᴹ    = [idS]tm
    ; [⨟]tᴹ      = [⨟]tm
    ; [π₁,]tᴹ  = (sym $ tr-cong π₁,) ∙ apd ([_]tm _) π₁,
    ; [π₁⨟]tᴹ   = λ {Γ} {Δ} {σ} {Θ} {_} {A} {τ} {_} {B} {t} →
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
    ; [∅]tᴹ     = refl
    ; [,]tᴹ     = refl
    ; [π₁idS]tᴹ = refl
    ; [π₁π₁]tᴹ  = refl
    ; _⨟idSᴹ     = _⨟idS
    ; idS⨟ᴹ_     = idS⨟_
    ; ⨟-assocᴹ    = ⨟-assoc
    ; π₁,ᴹ      = π₁,
    ; ⨟,ᴹ       = ⨟,
    ; η∅ᴹ        = η∅
    ; η,ᴹ        = η,
    ; [idS]tmᴹ   = [idS]tm
    ; [⨟]tmᴹ     = [⨟]tm
    ; π₂,ᴹ      = λ {Γ} {Δ} {σ} {_} {A} {t} → begin
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
    ; []Uᴹ    = []U
    ; []Elᴹ   = []El
    ; []Liftᴹ = []Lift
    ; []tcᴹ   = []tc
    ; []mkᴹ    = []mk
    ; []unᴹ    = []un
    ; Uβᴹ      = Uβ
    ; Uηᴹ      = Uη
    ; Liftβᴹ   = Liftβ
    ; Liftηᴹ   = Liftη
    }
  ; piTy = record
    { Πᴹ    = Π
    ; ƛᴹ_   = ƛ_
    ; appᴹ  = app
    ; []Πᴹ = []Π
    ; []ƛᴹ  = []ƛ
    ; Πβᴹ   = Πβ
    ; Πηᴹ   = Πη
    }
  ; idTy = record
    { Idᴹ      = Id
    ; []Idᴹ   = []Id
    ; reflᴹ    = refl
    ; []reflᴹ  = []refl
    ; reflectᴹ = reflect
    }
  }
