-- Elimination of Substitution Calculus
module SC+U+Pi.QIIRT.Elimination where

open import Prelude
  hiding (_,_)
open import SC+U+Pi.QIIRT.Base
open import SC+U+Pi.QIIRT.Model

module elim {ℓ ℓ′}(P : Pdc {ℓ} {ℓ′})(indP : IH P) where
  open Pdc P
  open IH indP

  {-# TERMINATING #-}
  ElimCtx : (Γ : Ctx) → PCtx Γ
  ElimTy : (A : Ty Γ i) → PTy (ElimCtx Γ) i A
  ElimSub : (σ : Sub Δ Γ) → PSub (ElimCtx Δ) (ElimCtx Γ) σ
  ElimTm : (t : Tm Γ A) → PTm (ElimCtx Γ) (ElimTy A) t

  ElimTy[] : (σ : Sub Δ Γ)(A : Ty Γ i) → [ ElimSub σ ]P ElimTy A ≡ ElimTy ([ σ ] A)
  
  ElimCtx ∅ = ∅Ctx
  ElimCtx (Γ , A) = ElimCtx Γ ,Ctx ElimTy A
  ElimTy (U i) = PU i
  ElimTy (Π A B) = PΠ (ElimTy A) (ElimTy B)
  ElimTy (El u) = PEl (ElimTm u)
  ElimSub ∅ = ∅Sub
  ElimSub {Δ} (_,_ σ {A} t) = ElimSub σ ,Sub tr PTmFamₜ (sym $ ElimTy[] σ A) (ElimTm t)
  ElimSub idS = PidS
  ElimSub (τ ⨟ σ) = ElimSub τ ⨟P ElimSub σ
  ElimSub (π₁ σ) = π₁P (ElimSub σ)
  ElimTm {Γ} (π₂ {A = A} σ) = tr PTmFamₜ (ElimTy[] (π₁ σ) A) (π₂P (ElimSub σ))
  ElimTm {Γ} ([_]tm_ σ {A} t) = tr PTmFamₜ (ElimTy[] σ A) ([ ElimSub σ ]tmP ElimTm t)
  ElimTm (c A) = cP (ElimTy A)
  ElimTm (ƛ t) = ƛP (ElimTm t)
  ElimTm (app t) = appP (ElimTm t)
  ElimTy[] σ (U i) = PU[]
  ElimTy[] σ (El u) = begin
    [ ElimSub σ ]P ElimTy (El u)
      ≡⟨ PEl[] (ElimSub σ) (ElimTm u) ⟩
    PEl (tr PTmFamₜ PU[] ([ ElimSub σ ]tP ElimTm u))
      ≡⟨ {!   !} ⟩
    {!   !}
    where open ≡-Reasoning
  ElimTy[] σ (Π A B) = {!   !}

