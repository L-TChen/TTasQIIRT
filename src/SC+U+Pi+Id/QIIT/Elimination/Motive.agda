open import Prelude
-- Motives of SC+U+Pi+Id/QIIT
module SC+U+Pi+Id.QIIT.Elimination.Motive where

open import SC+U+Pi+Id.QIIT.Syntax

record Motive (ℓ ℓ′ : Level) : Set (lsuc (ℓ ⊔ ℓ′)) where
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

  ExTmᴹ : (A : Ty Γ i)(t : Tm Γ A)(Γᴹ : Ctxᴹ Γ)(Aᴹ : Tyᴹ Γᴹ i A) → Set ℓ′
  ExTmᴹ _ t Γᴹ Aᴹ = Tmᴹ Γᴹ Aᴹ t

  TmᴹFam : {Γᴹ : Ctxᴹ Γ}{Aᴹ : Tyᴹ Γᴹ i A} → Tm Γ A → Set ℓ′
  TmᴹFam {Γᴹ = Γᴹ} {Aᴹ} = Tmᴹ Γᴹ Aᴹ
  
  TmᴹFamₜ : {Γᴹ : Ctxᴹ Γ}{t : Tm Γ A} → Tyᴹ Γᴹ i A → Set ℓ′
  TmᴹFamₜ {Γᴹ = Γᴹ} {t} Aᴹ = Tmᴹ Γᴹ Aᴹ t

  SubᴹFam : {Γᴹ : Ctxᴹ Γ}{Δᴹ : Ctxᴹ Δ} → Sub Γ Δ → Set ℓ′
  SubᴹFam {Γᴹ = Γᴹ} {Δᴹ = Δᴹ} = Subᴹ Γᴹ Δᴹ

  trTmᴹₜ : {A A' : Ty Γ i}{Γᴹ : Ctxᴹ Γ}(A≡A' : A ≡ A')
           {Aᴹ : Tyᴹ Γᴹ i A}{A'ᴹ : Tyᴹ Γᴹ i A'}
           (Aᴹ≡A'ᴹ : tr TyᴹFam A≡A' Aᴹ ≡ A'ᴹ){t : Tm Γ A}
         → Tmᴹ Γᴹ Aᴹ t → Tmᴹ Γᴹ A'ᴹ (tr (Tm Γ) A≡A' t)
  trTmᴹₜ refl Aᴹ≡A'ᴹ = tr TmᴹFamₜ Aᴹ≡A'ᴹ
