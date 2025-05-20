open import Prelude
-- Motives of SC+U+Pi+Id/QIIT
module Theory.SC+U+Pi+Id.QIIT.Elimination.Motive where

open import Theory.SC+U+Pi+Id.QIIT.Syntax

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

  TmᴹFam : {Γᴹ : Ctxᴹ Γ}{Aᴹ : Tyᴹ Γᴹ i A} → Tm Γ A → Set ℓ′
  TmᴹFam {Γᴹ = Γᴹ} {Aᴹ} = Tmᴹ Γᴹ Aᴹ
  
  TmᴹFamₜ : {Γᴹ : Ctxᴹ Γ}{t : Tm Γ A} → Tyᴹ Γᴹ i A → Set ℓ′
  TmᴹFamₜ {Γᴹ = Γᴹ} {t} Aᴹ = Tmᴹ Γᴹ Aᴹ t

  SubᴹFam : {Γᴹ : Ctxᴹ Γ}{Δᴹ : Ctxᴹ Δ} → Sub Γ Δ → Set ℓ′
  SubᴹFam {Γᴹ = Γᴹ} {Δᴹ = Δᴹ} = Subᴹ Γᴹ Δᴹ

  trTmᴹₜ : {A A' : Ty Γ i}{Γᴹ : Ctxᴹ Γ}(A≡A' : A ≡ A')
            {Aᴹ : Tyᴹ Γᴹ i A}{A'ᴹ : Tyᴹ Γᴹ i A'}
            (Aᴹ≡A'ᴹ : tr TyᴹFam A≡A' Aᴹ ≡ A'ᴹ){t : Tm Γ A}
          → Tmᴹ Γᴹ Aᴹ t
          → Tmᴹ Γᴹ A'ᴹ (tr (Tm Γ) A≡A' t)
  trTmᴹₜ {Γ} {i} {A} {A'} {Γᴹ} A≡A' {Aᴹ} {A'ᴹ} Aᴹ≡A'ᴹ {t} =
    tr (λ (A , (Aᴹ , t)) → Tmᴹ Γᴹ Aᴹ t) eq
    where
      I : Set ℓ
      I = Σ (Ty Γ i) λ A → Tyᴹ Γᴹ i A × Tm Γ A

      eq : _≡_ {A = I} (A , (Aᴹ , t)) (A' , (A'ᴹ , tr (Tm Γ) A≡A' t))
      eq = (A≡A' ,Σ≡ Aᴹ≡A'ᴹ) ,≡₂ lift (Tm Γ) t A≡A'
      