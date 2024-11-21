-- Elimination of Substitution Calculus
module SC.QIIRT.Elimination where

open import Prelude
open import SC.QIIRT.Base
open import SC.QIIRT.Model

module elim {i j}(P : Pdc {i} {j})(indP : IH P)(indPEq : IHEq P indP) where
  open Pdc P
  open IH indP
  open IHEq indPEq

  ElimCtx : (Γ : Ctx) → PCtx Γ
  ElimTy : (A : Ty Γ) → PTy (ElimCtx Γ) A
  ElimCtx ∅ = ∅Ctx
  ElimCtx (Γ ‣ A) = ElimCtx Γ ‣Ctx ElimTy A
  ElimTy U = PU

  ElimSub : (σ : Sub Δ Γ) → PSub (ElimCtx Δ) (ElimCtx Γ) σ
  ElimTm : (t : Tm Γ A) → PTm (ElimCtx Γ) (ElimTy A) t 
  ElimTy[] : (A : Ty Γ)(σ : Sub Δ Γ) → ElimTy A [ ElimSub σ ]P ≡ ElimTy (A [ σ ])
  ElimTy[] U σ = PU[]
  ElimSub ∅ = ∅Sub
  ElimSub {Δ} (_‣_ {A = A} σ t) = ElimSub σ ‣Sub tr (λ y → PTm (ElimCtx Δ) y t) (sym (ElimTy[] A σ)) (ElimTm t)
  ElimSub idS = PidS
  ElimSub (σ ∘ τ) = ElimSub σ ∘P ElimSub τ
  ElimSub (π₁ σ) = π₁P (ElimSub σ)
  ElimTm {Γ} (π₂ {A = A} σ) = tr (λ y → PTm (ElimCtx Γ) y (π₂ σ)) (ElimTy[] A (π₁ σ)) (π₂P (ElimSub σ))
  ElimTm {Γ} (_[_]tm {A = A} t σ) = tr (λ y → PTm (ElimCtx Γ) y (t [ σ ]tm)) (ElimTy[] A σ) (ElimTm t [ ElimSub σ ]tmP)

