open import Prelude

module Theory.SC.QIIRT-tyOf.Models.Term where

open import Theory.SC.QIIRT-tyOf.Syntax
open import Theory.SC.QIIRT-tyOf.Model

Termᵃ : Motive _ _ _ _
Termᵃ = record
  { Ctxᴬ       = Ctx
  ; Tyᴬ        = Ty
  ; Subᴬ       = Sub
  ; Tmᴬ        = Tm
  ; tyOfᴬ      = tyOf
  ; Tyᴬ-is-set = Ty-is-set
  }

Termᵐ : SCᴹ Termᵃ
Termᵐ = record
  { ∅ᴹ       = ∅
  ; _,ᴹ_     = _,_
  ; _[_]Tᴹ   = _[_]
  ; _[_]tᴹ   = _[_]
  ; tyOf[]ᴹ  = refl
  ; ∅Sᴹ      = ∅S
  ; _,ᴹ_∶[_] = _,_∶[_]
  ; idSᴹ     = idS
  ; _∘ᴹ_     = _∘_
  ; π₁ᴹ      = π₁
  ; π₂ᴹ      = π₂
  ; tyOfπ₂ᴹ  = tyOfπ₂
  ; idS∘ᴹ_   = idS∘_
  ; _∘idSᴹ   = _∘idS
  ; assocSᴹ  = assocS
  ; [idS]Tᴹ  = [idS]T
  ; [∘]Tᴹ    = [∘]T
  ; ,∘ᴹ      = ,∘
  ; ηπᴹ      = ηπ
  ; η∅ᴹ      = η∅
  ; βπ₁ᴹ     = βπ₁
  ; βπ₂ᴹ     = λ {Γ} {Δ} {A} σ t p
    → βπ₂ σ t p (cong (A [_]) (βπ₁ σ t p) ∙ sym p)
  ; [idS]tᴹ  = [idS]t
  ; [∘]tᴹ    = [∘]t
  ; Uᴹ       = U
  ; U[]ᴹ     = U[]
  }
