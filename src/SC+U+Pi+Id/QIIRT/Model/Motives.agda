-- Motives of Model of Substitution Calculus
module SC+U+Pi+Id.QIIRT.Model.Motives where

open import Prelude
  hiding (_,_)
open import Data.Nat hiding (_⊔_)
open import SC+U+Pi+Id.QIIRT.Base

record PredOverPCtx ({ℓ} ℓ′ : Level) (PCtx : Ctx → Set ℓ) {Γ : Ctx} (PΓ : PCtx Γ) : Set (lsuc (ℓ ⊔ ℓ′)) where
  field
    PTy  : (i : ℕ) → Ty Γ i → Set ℓ
    PSub : PCtx Δ → Sub Γ Δ → Set ℓ′
-- open PredOverPCtx

record Pred {ℓ ℓ′} : Set (lsuc (ℓ ⊔ ℓ′)) where
  field
    PCtx
      : Ctx → Set ℓ
    PTySub
      : (PΓ : PCtx Γ)
      → PredOverPCtx ℓ′ _ PΓ
    PTm
      : (PΓ : PCtx Γ) (PA : PTySub PΓ .PredOverPCtx.PTy i A)
      → Tm Γ A → Set ℓ′

  PTy : (PΓ : PCtx Γ) → (i : ℕ) → Ty Γ i → Set ℓ
  PTy PΓ = PTySub _ .PredOverPCtx.PTy

  PSub : (PΓ : PCtx Γ) {Δ : Ctx} (PΔ : PCtx Δ) → Sub Γ Δ → Set ℓ′
  PSub PΓ = PTySub PΓ .PredOverPCtx.PSub

  PTyFam : {PΓ : PCtx Γ}{i : ℕ} → Ty Γ i → Set ℓ
  PTyFam {PΓ = PΓ} {i} = PTy PΓ i

  PTmFam : {PΓ : PCtx Γ}{PA : PTy PΓ i A} → Tm Γ A → Set ℓ′
  PTmFam {PΓ = PΓ} {PA} = PTm PΓ PA
  
  PTmFamₜ : {PΓ : PCtx Γ}{t : Tm Γ A} → PTy PΓ i A → Set ℓ′
  PTmFamₜ {PΓ = PΓ} {t} PA = PTm PΓ PA t

  PSubFam : {PΓ : PCtx Γ}{PΔ : PCtx Δ} → Sub Γ Δ → Set ℓ′
  PSubFam {PΓ = PΓ} {PΔ} = PSub PΓ PΔ
