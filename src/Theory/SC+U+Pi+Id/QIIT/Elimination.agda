open import Prelude
  renaming (_,_ to _,'_)

module Theory.SC+U+Pi+Id.QIIT.Elimination where

open import Theory.SC+U+Pi+Id.QIIT.Syntax
open import Theory.SC+U+Pi+Id.QIIT.Elimination.Motive
open import Theory.SC+U+Pi+Id.QIIT.Elimination.Method

record Eliminator {ℓ ℓ′ : Level} : Set (lsuc (ℓ ⊔ ℓ′)) where
  field
    mot : Motive ℓ ℓ′
    met : Method mot

  open Motive mot public
  open Method met public

module _ {ℓ ℓ′ : Level} (elim : Eliminator {ℓ} {ℓ′}) where
  open Eliminator elim
  
  {-# TERMINATING #-}
  elimCtx
    : (Γ : Ctx) → Ctxᴹ Γ
  elimTy
    : (A : Ty Γ i) → Tyᴹ (elimCtx Γ) i A
  elimSub
    : (σ : Sub Δ Γ) → Subᴹ (elimCtx Δ) (elimCtx Γ) σ
  elimTm
    : (t : Tm Γ A) → Tmᴹ (elimCtx Γ) (elimTy A) t
  
  elimCtx ∅          = ∅ᶜᴹ
  elimCtx (Γ , A)    = elimCtx Γ ,ᶜᴹ elimTy A
  elimTy (U i)       = Uᴹ i
  elimTy (El u)      = Elᴹ (elimTm u)
  elimTy (Lift A)    = Liftᴹ (elimTy A)
  elimTy (Π A B)     = Πᴹ (elimTy A) (elimTy B)
  elimTy (Id a t u)  = Idᴹ (elimTm a) (elimTm t) (elimTm u)
  elimTy ([ σ ] A)   = [ elimSub σ ]ᴹ elimTy A
  elimSub ∅          = ∅ˢᴹ
  elimSub (σ , t)    = elimSub σ ,ˢᴹ elimTm t
  elimSub idS        = idSᴹ
  elimSub (τ ⨟ σ)    = elimSub τ ⨟ᴹ elimSub σ
  elimSub (π₁ σ)     = π₁ᴹ (elimSub σ)
  elimTm (π₂ σ)      = π₂ᴹ (elimSub σ)
  elimTm ([ σ ]tm t) = [ elimSub σ ]tmᴹ elimTm t
  elimTm (c A)       = cᴹ (elimTy A)
  elimTm (mk t)      = mkᴹ (elimTm t)
  elimTm (un t)      = unᴹ (elimTm t)
  elimTm (ƛ t)       = ƛᴹ elimTm t
  elimTm (app t)     = appᴹ (elimTm t)
  elimTm (refl t)     = reflᴹ (elimTm t)

