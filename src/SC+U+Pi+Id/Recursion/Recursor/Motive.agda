-- Motive for SC+U+Pi+Id Recursor
module SC+U+Pi+Id.Recursion.Recursor.Motive where

open import Prelude

record Motive (ℓ ℓ′ : Level) : Set (lsuc (ℓ ⊔ ℓ′)) where
  field
    Ctxᴹ
      : Set ℓ
    Tyᴹ
      : Ctxᴹ → (i : ℕ) → Set ℓ
    Subᴹ
      : Ctxᴹ → Ctxᴹ → Set ℓ′
    Tmᴹ
      : {i : ℕ}(Γᴹ : Ctxᴹ)(Aᴹ : Tyᴹ Γᴹ i) → Set ℓ′

  TmᴹFam : {i : ℕ}{Γᴹ : Ctxᴹ}(Aᴹ : Tyᴹ Γᴹ i) → Set ℓ′
  TmᴹFam {Γᴹ = Γᴹ} = Tmᴹ Γᴹ