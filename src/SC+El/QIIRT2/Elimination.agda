-- Elimination of Substitution Calculus
module SC+El.QIIRT2.Elimination where

open import Prelude
open import SC+El.QIIRT2.Base
open import SC+El.QIIRT2.Model
open ≡-Reasoning

module elim {i j}(P : Pdc {i} {j})(indP : IH P) where
  open Pdc P
  open IH indP

  {-# TERMINATING #-}
  ElimCtx : (Γ : Ctx) → PCtx Γ
  ElimTy : (A : Ty Γ) → PTy (ElimCtx Γ) A
  ElimSub : (σ : Sub Δ Γ) → PSub (ElimCtx Δ) (ElimCtx Γ) σ
  ElimTm : (t : Tm Γ A) → PTm (ElimCtx Γ) (ElimTy A) t
  ElimTy[] : (A : Ty Γ)(σ : Sub Δ Γ) → ElimTy A [ ElimSub σ ]P ≡ ElimTy (A [ σ ])
  ElimTm[] : (t : Tm Γ A)(σ : Sub Δ Γ) → ElimTm t [ ElimSub σ ]tP ≡ {! t    !} -- ElimTm (t [ σ ]tP)

  ElimCtx ∅ = ∅Ctx
  ElimCtx (Γ , A) = ElimCtx Γ ,Ctx ElimTy A
  ElimTy U = PU
  ElimTy (El u) = PEl (ElimTm u)
  ElimTy[] U σ = PU[]
  ElimTy[] {Γ} {Δ} (El u) σ = begin
      (ElimTy (El u) [ ElimSub σ ]P)
    ≡⟨ PEl[] {Pu = ElimTm u} (ElimSub σ) ⟩
      PEl (conv (cong (λ PA → PTm (ElimCtx Δ) PA (u [ σ ]t)) PU[])
                (ElimTm u [ ElimSub σ ]tP))
    ≡⟨ {!   !} ⟩
      {!   !}
  ElimSub ∅ = ∅Sub
  ElimSub {Δ} (_,_ {A = A} σ t) = ElimSub σ ,Sub conv (congPTm {PΓ = ElimCtx Δ} {ElimTy (A [ σ ])} {t = t} refl (sym (ElimTy[] A σ)) refl)
                                                      (ElimTm t)
  ElimSub idS = PidS
  ElimSub (σ ∘ τ) = ElimSub σ ∘P ElimSub τ
  ElimSub (π₁ σ) = π₁P (ElimSub σ)
  ElimTm {Γ} (π₂ {A = A} σ) = conv (cong (λ PA → PTm (ElimCtx Γ) PA (π₂ σ)) (ElimTy[] A (π₁ σ))) (π₂P (ElimSub σ)) 
  ElimTm (t [ σ ]tm) = {!   !}