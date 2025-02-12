-- Motives of Model of Substitution Calculus
module SC+U+Pi+Id.QIIRT.Model.Motives where

open import Prelude
  hiding (_,_)
open import Data.Nat hiding (_⊔_)
open import SC+U+Pi+Id.QIIRT.Base

record Motive {ℓ ℓ′} : Set (lsuc (ℓ ⊔ ℓ′)) where
  field
    Ctxᴹ
      : Ctx → Set ℓ
    Tyᴹ
      : Ctxᴹ Γ → (i : ℕ) → Ty Γ i → Set ℓ
    Subᴹ
      : Ctxᴹ Γ → Ctxᴹ Δ → Sub Γ Δ → Set ℓ′
    Tmᴹ
      : (Γᴹ : Ctxᴹ Γ) (Aᴹ : Tyᴹ Γᴹ i A)
      → Tm Γ A → Set ℓ′

  TyᴹFam : {Γᴹ : Ctxᴹ Γ}{i : ℕ} → Ty Γ i → Set ℓ
  TyᴹFam {Γᴹ = Γᴹ} {i} = Tyᴹ Γᴹ i

  TmᴹFam : {Γᴹ : Ctxᴹ Γ}{Aᴹ : Tyᴹ Γᴹ i A} → Tm Γ A → Set ℓ′
  TmᴹFam {Γᴹ = Γᴹ} {Aᴹ} = Tmᴹ Γᴹ Aᴹ

  TmᴹFamₜ : {Γᴹ : Ctxᴹ Γ}{t : Tm Γ A} → Tyᴹ Γᴹ i A → Set ℓ′
  TmᴹFamₜ {Γᴹ = Γᴹ} {t} Aᴹ = Tmᴹ Γᴹ Aᴹ t

  SubᴹFam : {Γᴹ : Ctxᴹ Γ}{Δᴹ : Ctxᴹ Δ} → Sub Γ Δ → Set ℓ′
  SubᴹFam {Γᴹ = Γᴹ} {Δᴹ = Δᴹ} = Subᴹ Γᴹ Δᴹ
