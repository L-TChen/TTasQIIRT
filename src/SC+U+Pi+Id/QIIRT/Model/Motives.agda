-- Motives of Model of Substitution Calculus
module SC+U+Pi.QIIRT.Model.Motives where

open import Prelude
  hiding (_,_)
open import Data.Nat hiding (_⊔_)
open import SC+U+Pi.QIIRT.Base

record Predicate {ℓ ℓ′} : Set (lsuc (ℓ ⊔ ℓ′)) where
  field
    PCtx
      : Ctx → Set ℓ
    PTy
      : PCtx Γ → (i : ℕ) → Ty Γ i → Set ℓ
    PSub
      : PCtx Γ → PCtx Δ → Sub Γ Δ → Set ℓ′
    PTm
      : (PΓ : PCtx Γ) → PTy PΓ i A → Tm Γ A → Set ℓ′
  
  PTyFam : {PΓ : PCtx Γ}{i : ℕ} → Ty Γ i → Set ℓ
  PTyFam {PΓ = PΓ} {i} = PTy PΓ i

  PTmFam : {PΓ : PCtx Γ}{PA : PTy PΓ i A} → Tm Γ A → Set ℓ′
  PTmFam {PΓ = PΓ} {PA} = PTm PΓ PA
  
  PTmFamₜ : {PΓ : PCtx Γ}{t : Tm Γ A} → PTy PΓ i A → Set ℓ′
  PTmFamₜ {PΓ = PΓ} {t} PA = PTm PΓ PA t

  PSubFam : {PΓ : PCtx Γ}{PΔ : PCtx Δ} → Sub Γ Δ → Set ℓ′
  PSubFam {PΓ = PΓ} {PΔ} = PSub PΓ PΔ