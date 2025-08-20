{-# OPTIONS --hidden-argument-puns #-}
open import Prelude

open import Theory.SC.QIIRT-tyOf.IxModel

module Theory.SC.QIIRT-tyOf.Elim (C : SC∙ ℓ₁ ℓ₂ ℓ₃ ℓ₄) where

open SC∙ C
  hiding (module Var)

open import Theory.SC.QIIRT-tyOf.Syntax
open Var

elimCtx  : (Γ : Ctx) → Ctx∙ Γ
{-# TERMINATING #-}
elimTy   : (A : Ty Γ) → Ty∙ (elimCtx Γ) A
elimTm   : (t : Tm Γ) → Tm∙ (elimCtx Γ) t
elimSub  : (σ : Sub Γ Δ) → Sub∙ (elimCtx Γ) (elimCtx Δ) σ
elimTyOf : (t : Tm Γ) (p : tyOf t ≡ A)
  →  tyOf∙ (elimTm t) ≡Ty[ p ] elimTy A

elimCtx ∅        = ∅∙
elimCtx (Γ , A)  = elimCtx Γ ,∙ elimTy A

elimTy (A [ σ ]) = elimTy A [ elimSub σ ]T∙
elimTy U         = U∙
elimTy ([idS]T {A} i) = [idS]T∙ (elimTy A) i
elimTy ([∘]T A σ τ i) = [∘]T∙ (elimTy A) (elimSub σ) (elimSub τ) i
elimTy (U[] {σ} i) = U[]∙ {σ∙ = elimSub σ} i

elimTm (t [ σ ]) = elimTm t [ elimSub σ ]t∙
elimTm (π₂ σ)    = π₂∙ (elimSub σ)
elimTm (βπ₂ {A} σ t p q i) =
  βπ₂∙ (elimSub σ) (elimTm t) p (elimTyOf _ p) q
  {!!} i
elimTm ([idS]t t i)    = [idS]t∙ (elimTm t) i
elimTm ([∘]t t σ τ i)  = [∘]t∙ (elimTm t) (elimSub σ) (elimSub τ) i

elimSub ∅              = ∅S∙
elimSub (σ , t ∶[ p ]) =
  elimSub σ ,  elimTm t ∶[ p , elimTyOf _ p ]∙
elimSub idS            = idS∙
elimSub (σ ∘ τ)       = elimSub σ ∘∙ elimSub τ
elimSub (π₁ σ)        = π₁∙ (elimSub σ)
elimSub (βπ₁ σ t p i) = βπ₁∙ (elimSub σ) (elimTm t) p (elimTyOf _ p) i
elimSub ((idS∘ σ) i)  = (idS∘∙ elimSub σ) i
elimSub ((σ ∘idS) i)  = (elimSub σ ∘idS∙) i
elimSub (assocS σ τ γ i) = assocS∙ (elimSub σ) (elimSub τ) (elimSub γ) i
elimSub (,∘ σ t τ p q i) =
  ,∘∙ (elimSub σ) (elimTm t) (elimSub τ) p (elimTyOf _ p) q (elimTyOf _ q) i
elimSub (η∅ σ i) = η∅∙ (elimSub σ) i
elimSub (ηπ {Γ} {Δ} {A} σ i) = {!ηπ∙ (elimSub σ) !}

elimTyOf {Γ} {A} (t [ σ ]) p =
   transport (λ i →
    tyOf∙ (elimTm t [ elimSub σ ]t∙) ≡Ty[ UIP {x = tyOf (t [ σ ])} {A}
    (refl ∙ refl ∙ p) p i  ] elimTy A)
    (tyOf[]∙ ∙Ty[] cong _[ elimSub σ ]T∙ (elimTyOf t refl) ∙Ty[] cong elimTy p)
  
elimTyOf (π₂ σ)          p = {!!}
elimTyOf (βπ₂ σ t p q i) p' = {!!}
elimTyOf ([idS]t t i)    p = {!!}
elimTyOf ([∘]t t σ τ i)  p = {!!}
