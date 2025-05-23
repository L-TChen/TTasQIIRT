-- Elimination of Substitution Calculus
module Theory.SC.QIIT.Elimination where

open import Prelude
  hiding (_∘_)
open import Theory.SC.QIIT.Syntax
open import Theory.SC.QIIT.Model

module elim {i j}(P : Pdc {i} {j})(indP : IH P) where
  open Pdc P
  open IH indP

  ElimCtx : (Γ : Ctx) → PCtx Γ
  ElimTy : (A : Ty Γ) → PTy (ElimCtx Γ) A
  ElimSub : (σ : Sub Δ Γ) → PSub (ElimCtx Δ) (ElimCtx Γ) σ
  ElimTm : (t : Tm Γ A) → PTm (ElimCtx Γ) (ElimTy A) t
  
  ElimCtx ∅ = ∅Ctx
  ElimCtx (Γ , A) = ElimCtx Γ ,Ctx ElimTy A
  ElimTy U = PU
  ElimTy (A [ σ ]) = ElimTy A [ ElimSub σ ]P -- additional
  ElimSub ∅ = ∅Sub
  ElimSub (σ , t) = ElimSub σ ,Sub ElimTm t -- no need to transport
  ElimSub idS = PidS
  ElimSub (σ ∘ τ) = ElimSub σ ∘P ElimSub τ
  ElimSub (π₁ σ) = π₁P (ElimSub σ)
  ElimTm (π₂ σ) = π₂P (ElimSub σ)
  ElimTm (t [ σ ]) = ElimTm t [ ElimSub σ ]tP