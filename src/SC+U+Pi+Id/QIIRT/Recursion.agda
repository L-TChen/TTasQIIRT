-- Elimination of Substitution Calculus
module SC+U+Pi+Id.QIIRT.Recursion where

open import Prelude
  renaming (_,_ to _,'_)
open import SC+U+Pi+Id.QIIRT.Syntax
open import SC+U+Pi+Id.QIIRT.Recursion.Motive
open import SC+U+Pi+Id.QIIRT.Recursion.Method
open import SC+U+Pi+Id.QIIRT.Properties

record Recursor {ℓ ℓ′} : Set (lsuc (ℓ ⊔ ℓ′)) where
  field
    Mot : Motive {ℓ} {ℓ′}
    Met : Method Mot
  
  open Motive Mot public
  open Method Met public

module rec {ℓ ℓ′}(M : Recursor {ℓ} {ℓ′}) where
  open Recursor M

  {-# TERMINATING #-}
  recCtx
    : Ctx → Ctxᴹ
  recTy
    : Ty Γ i → Tyᴹ (recCtx Γ) i
  recSub
    : Sub Γ Δ → Subᴹ (recCtx Γ) (recCtx Δ)
  recTm
    : Tm Γ A → Tmᴹ (recCtx Γ) (recTy A)
  postulate -- already proved in Elimination
    recTy[]
      : (σ : Sub Γ Δ) (A : Ty Δ i)
      → [ recSub σ ]ᴹ recTy A ≡ recTy ([ σ ] A)
    recTm[]
      : (σ : Sub Γ Δ) {A : Ty Δ i}(t : Tm Δ A)
      → tr TmᴹFam (recTy[] σ A) ([ recSub σ ]tᴹ recTm t) ≡ recTm ([ σ ]t t)
  
  recCtx ∅          = ∅ᶜᴹ
  recCtx (Γ , A)    = recCtx Γ ,ᶜᴹ recTy A
  recTy (U i)       = Uᴹ i
  recTy (El u)      = Elᴹ (recTm u)
  recTy (Lift A)    = Liftᴹ (recTy A)
  recTy (Π A B)     = Πᴹ (recTy A) (recTy B)
  recTy (Id a t u)  = Idᴹ (recTm a) (recTm t) (recTm u)
  recSub ∅          = ∅ˢᴹ
  recSub (_,_ σ {A} t) = recSub σ ,ˢᴹ tr (Tmᴹ _) (sym $ recTy[] σ A) (recTm t)
  recSub idS        = idSᴹ
  recSub (τ ⨟ σ)    = recSub τ ⨟ᴹ recSub σ
  recSub (π₁ σ)     = π₁ᴹ (recSub σ)
  recTm (π₂ {A = A} σ)   = tr TmᴹFam (recTy[] (π₁ σ) A) (π₂ᴹ (recSub σ))
  recTm ([_]tm_ σ {A} t) = tr TmᴹFam (recTy[] σ A) ([ recSub σ ]tmᴹ recTm t)
  recTm (c A)       = cᴹ (recTy A)
  recTm (mk t)      = mkᴹ (recTm t)
  recTm (un t)      = unᴹ (recTm t)
  recTm (ƛ t)       = (ƛᴹ recTm t)
  recTm (app t)     = appᴹ (recTm t)
  recTm (refl t)    = reflᴹ (recTm t)

open rec public
