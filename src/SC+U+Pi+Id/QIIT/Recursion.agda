-- Recursion for SC+U+Pi+Id
open import Prelude

module SC+U+Pi+Id.QIIT.Recursion where

open import SC+U+Pi+Id.QIIT.Recursion.Motive
open import SC+U+Pi+Id.QIIT.Recursion.Method

record Recursor {ℓ ℓ′ : Level} : Set (lsuc (ℓ ⊔ ℓ′)) where
  field
    mot : Motive ℓ ℓ′
    met : Method mot

  open Motive mot public
  open Method met public

module _ {ℓ ℓ′ : Level} (rec : Recursor {ℓ} {ℓ′}) where
  open Recursor rec
  open import SC+U+Pi+Id.QIIT.Syntax
  
  {-# TERMINATING #-}
  recCtx
    : (Γ : Ctx) → Ctxᴹ
  recTy
    : (A : Ty Γ i) → Tyᴹ (recCtx Γ) i
  recSub
    : (σ : Sub Δ Γ) → Subᴹ (recCtx Δ) (recCtx Γ)
  recTm
    : (t : Tm Γ A) → Tmᴹ (recCtx Γ) (recTy A)
  
  recCtx ∅ = ∅ᶜᴹ
  recCtx (Γ , A) = recCtx Γ ,ᶜᴹ recTy A
  recTy ([ σ ] A) = [ recSub σ ]ᴹ recTy A
  recTy (U i) = Uᴹ i
  recTy (El u) = Elᴹ (recTm u)
  recTy (Lift A) = Liftᴹ (recTy A)
  recTy (Π A B) = Πᴹ (recTy A) (recTy B)
  recTy (Id a t u) = Idᴹ (recTm a) (recTm t) (recTm u)
  recSub ∅ = ∅ˢᴹ
  recSub (σ , t) = recSub σ ,ˢᴹ recTm t
  recSub idS = idSᴹ
  recSub (τ ⨟ σ) = recSub τ ⨟ᴹ recSub σ
  recSub (π₁ σ) = π₁ᴹ (recSub σ)
  recTm (π₂ σ) = π₂ᴹ (recSub σ)
  recTm ([ σ ]tm t) = [ recSub σ ]tmᴹ recTm t
  recTm (c A) = cᴹ (recTy A)
  recTm (mk t) = mkᴹ (recTm t)
  recTm (un t) = unᴹ (recTm t)
  recTm (ƛ t) = ƛᴹ recTm t
  recTm (app t) = appᴹ (recTm t)
