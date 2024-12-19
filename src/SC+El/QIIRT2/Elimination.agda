-- Elimination of Substitution Calculus
module SC+El.QIIRT2.Elimination where

open import Prelude
open import SC+El.QIIRT2.Base
open import SC+El.QIIRT2.Model

module elim {i j}(P : Pdc {i} {j})(indP : IH P) where
  open Pdc P
  open IH indP

  {-# TERMINATING #-}
  ElimCtx : (Γ : Ctx) → PCtx Γ
  ElimTy : (A : Ty Γ) → PTy (ElimCtx Γ) A
  ElimSub : (σ : Sub Δ Γ) → PSub (ElimCtx Δ) (ElimCtx Γ) σ
  ElimTm : (t : Tm Γ A) → PTm (ElimCtx Γ) (ElimTy A) t
  ElimTy[] : (A : Ty Γ)(σ : Sub Δ Γ) → ElimTy A [ ElimSub σ ]P ≡ ElimTy (A [ σ ])
  ElimTm[] : (t : Tm Γ A)(σ : Sub Δ Γ)
           → conv (PTmPΓ` refl (ElimTy[] A σ) refl) (ElimTm t [ ElimSub σ ]tP) ≡ ElimTm (t [ σ ]t)

  ElimCtx ∅ = ∅Ctx
  ElimCtx (Γ , A) = ElimCtx Γ ,Ctx ElimTy A
  ElimTy U = PU
  ElimTy (El u) = PEl (ElimTm u)
  ElimTy[] U σ = PU[]
  ElimTy[] {Γ} {Δ} (El u) σ = begin
      (ElimTy (El u) [ ElimSub σ ]P)
    ≡⟨ PEl[] {Pu = ElimTm u} (ElimSub σ) ⟩
      PEl (conv (PTmPΓ` refl PU[] refl) (ElimTm u [ ElimSub σ ]tP))
    ≡⟨ cong PEl (ElimTm[] u σ) ⟩
      PEl (ElimTm (u [ σ ]t))
    ∎
    where open ≡-Reasoning
  ElimSub ∅ = ∅Sub
  ElimSub {Δ} (_,_ {A = A} σ t) = ElimSub σ ,Sub conv (PTmPΓ` refl (sym (ElimTy[] A σ)) refl)
                                                      (ElimTm t)
  ElimSub idS = PidS
  ElimSub (σ ∘ τ) = ElimSub σ ∘P ElimSub τ
  ElimSub (π₁ σ) = π₁P (ElimSub σ)
  ElimTm {Γ} (π₂ {A = A} σ) = conv (PTmPΓ` refl (ElimTy[] A (π₁ σ)) refl) (π₂P (ElimSub σ))
  ElimTm {Γ} (_[_]tm {A = A} t σ) = conv (PTmPΓ` refl (ElimTy[] A σ) refl) (ElimTm t [ ElimSub σ ]tmP)
  ElimTm[] (π₂ {A = A} σ) τ = ≅-to-≡ $ begin
      conv (PTmPΓ` refl (ElimTy[] (A [ π₁ σ ]) τ) refl) (ElimTm (π₂ σ) [ ElimSub τ ]tP)
    ≅⟨ conv-rm (PTmPΓ` refl (ElimTy[] (A [ π₁ σ ]) τ) refl) _ ⟩
      ElimTm (π₂ σ) [ ElimSub τ ]tP
    ≅⟨ ≡-to-≅ (sym ([]tmP≡[]tP (ElimTm (π₂ σ)) (ElimSub τ))) ⟩
      conv (PTmPΓ` refl refl ([]tm≡[]t (π₂ σ) τ)) (ElimTm (π₂ σ) [ ElimSub τ ]tmP)
    ≅⟨ conv~unique (PTmPΓ` refl refl ([]tm≡[]t (π₂ σ) τ)) (PTmPΓ` refl (ElimTy[] (A [ π₁ σ ]) τ) refl) _ ⟩
      conv (PTmPΓ` refl (ElimTy[] (A [ π₁ σ ]) τ) refl) (ElimTm (π₂ σ) [ ElimSub τ ]tmP)
    ≅⟨ refl ⟩
      ElimTm (π₂ σ [ τ ]tm)
    ≅⟨ HEq.cong ElimTm (≡-to-≅ ([]tm≡[]t (π₂ σ) τ)) ⟩
      ElimTm (π₂ σ [ τ ]t)
    ∎
    where open ≅-Reasoning 
  ElimTm[] (_[_]tm {A = A} t σ) τ = ≅-to-≡ $ begin
      conv (PTmPΓ` refl (ElimTy[] (A [ σ ]) τ) refl) (ElimTm (t [ σ ]tm) [ ElimSub τ ]tP)
    ≅⟨ conv-rm (PTmPΓ` refl (ElimTy[] (A [ σ ]) τ) refl) _ ⟩
      ElimTm (t [ σ ]tm) [ ElimSub τ ]tP
    ≅⟨ ≡-to-≅ (sym ([]tmP≡[]tP (ElimTm (t [ σ ]tm)) (ElimSub τ))) ⟩
      conv (PTmPΓ` refl refl ([]tm≡[]t (t [ σ ]tm) τ)) (ElimTm (t [ σ ]tm) [ ElimSub τ ]tmP)
    ≅⟨ conv~unique (PTmPΓ` refl refl ([]tm≡[]t (t [ σ ]tm) τ)) (PTmPΓ` refl (ElimTy[] (A [ σ ]) τ) refl) _ ⟩
      conv (PTmPΓ` refl (ElimTy[] (A [ σ ]) τ) refl) (ElimTm (t [ σ ]tm) [ ElimSub τ ]tmP)
    ≅⟨ refl ⟩
      ElimTm (t [ σ ]tm [ τ ]tm)
    ≅⟨ HEq.cong ElimTm (≡-to-≅ ([]tm≡[]t (t [ σ ]tm) τ)) ⟩
      ElimTm (t [ σ ]tm [ τ ]t)
    ∎
    where open ≅-Reasoning 