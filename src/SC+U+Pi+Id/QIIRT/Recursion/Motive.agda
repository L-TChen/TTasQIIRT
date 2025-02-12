-- Motives of Model of Substitution Calculus
module SC+U+Pi+Id.QIIRT.Recursion.Motive where

open import Prelude
  hiding (_,_)
open import Data.Nat hiding (_⊔_)
open import SC+U+Pi+Id.QIIRT.Syntax

record Motive {ℓ ℓ′} : Set (lsuc (ℓ ⊔ ℓ′)) where
  field
    Ctxᴹ
      : Set ℓ
    Tyᴹ
      : Ctxᴹ → (i : ℕ) → Set ℓ
    Subᴹ
      : Ctxᴹ → Ctxᴹ → Set ℓ′
    Tmᴹ
      : (Γᴹ : Ctxᴹ) (Aᴹ : Tyᴹ Γᴹ i) → Set ℓ′

  TyᴹFam : {Γᴹ : Ctxᴹ}{i : ℕ} → Set ℓ
  TyᴹFam {Γᴹ} {i} = Tyᴹ Γᴹ i

  TmᴹFam : {Γᴹ : Ctxᴹ}{Aᴹ : Tyᴹ Γᴹ i} → Set ℓ′
  TmᴹFam {Γᴹ = Γᴹ} {Aᴹ} = Tmᴹ Γᴹ Aᴹ
  
  TmᴹFamₜ : {Γᴹ : Ctxᴹ} → Tyᴹ Γᴹ i → Set ℓ′
  TmᴹFamₜ {Γᴹ = Γᴹ} Aᴹ = Tmᴹ Γᴹ Aᴹ
{-
  SubᴹFam : {Γᴹ : Ctxᴹ}{Δᴹ : Ctxᴹ} → Set ℓ′
  SubᴹFam {Γᴹ = Γᴹ} {Δᴹ = Δᴹ} = Subᴹ Γᴹ Δᴹ
-}
