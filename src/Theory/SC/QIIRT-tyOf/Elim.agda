open import Prelude

open import Theory.SC.QIIRT-tyOf.IxModel

module Theory.SC.QIIRT-tyOf.Elim (C : SC∙ ℓ₁ ℓ₂ ℓ₃ ℓ₄) where

open SC∙ C
open Var

import Theory.SC.QIIRT-tyOf.Syntax as S
open S.Var

elimCtx  : (Γ : S.Ctx) → Ctx∙ Γ
elimTy   : (A : S.Ty Γ) → Ty∙ (elimCtx Γ) A
elimTm   : (t : S.Tm Γ) → Tm∙ (elimCtx Γ) t
elimSub  : (σ : S.Sub Γ Δ) → Sub∙ (elimCtx Γ) (elimCtx Δ) σ
elimTyOf : (t : S.Tm Γ)
  → (p : S.tyOf t ≡ A)
  → tyOf∙ (elimTm t) ≡Ty[ p ] elimTy A

elimCtx S.∅        = ∅∙
elimCtx (Γ S., A)  = elimCtx Γ ,∙ elimTy A
elimTy (A S.[ σ ]) = {!!}
elimTy S.U         = {!!}
elimTy (S.[idS]T i) = {!!}
elimTy (S.[∘]T A σ τ i) = {!!}
elimTy (S.U[] i) = {!!}
elimSub σ = {!!}
elimTm t  = {!!}
elimTyOf t = {!!}
