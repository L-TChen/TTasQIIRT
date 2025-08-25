{-# OPTIONS --hidden-argument-puns --no-require-unique-meta-solutions #-}
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
  (beginTy
    elimTy A [ π₁∙ (elimSub σ , elimTm t ∶[ p , elimTyOf t p ]∙) ]T∙
      ≡Ty[ cong (A [_]) (βπ₁ σ t p) ]⟨ (λ i → (elimTy A)
        [ βπ₁∙ (elimSub σ) (elimTm t) p (elimTyOf t p) i ]T∙) ⟩
    elimTy A [ elimSub σ ]T∙
      ≡Ty[ sym p ]⟨ symP $ elimTyOf t p ⟩
    tyOf∙ (elimTm t)
    ∎) i
    
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
elimSub (ηπ {Γ} {Δ} {A} σ i) = (beginSub[ ηπ σ ]
  (elimSub σ
    ≡Sub[ ηπ σ ]⟨ ηπ∙ (elimSub σ) ⟩
  π₁∙ (elimSub σ) , π₂∙ (elimSub σ) ∶[ refl , tyOfπ₂∙ (elimSub σ) ]∙
    ≡Sub[ refl ]⟨ cong (π₁∙ (elimSub σ) , π₂∙ (elimSub σ) ∶[ refl ,_]∙) (UIP _ _) ⟩
  π₁∙ (elimSub σ) , elimTm (π₂ σ) ∶[ refl , elimTyOf (π₂ σ) refl ]∙
    ∎)) i

elimTyOf {Γ} {A} (t [ σ ]) p = beginTy
  tyOf∙ (elimTm t [ elimSub σ ]t∙)
    ≡Ty[]⟨ tyOf[]∙ ⟩
  tyOf∙ (elimTm t) [ elimSub σ ]T∙
    ≡Ty[]⟨ (λ i → elimTyOf t refl i [ elimSub σ ]T∙) ⟩
  elimTy (tyOf t) [ elimSub σ ]T∙
    ≡Ty[ p ]⟨ cong elimTy p  ⟩
  elimTy A
    ∎
  
elimTyOf {A} (π₂ {A = B} σ) p = beginTy
  tyOf∙ (elimTm (π₂ σ))
    ≡Ty[]⟨ tyOfπ₂∙ (elimSub σ) ⟩
  elimTy B [ π₁∙ (elimSub σ) ]T∙
    ≡Ty[ p ]⟨ cong elimTy p ⟩
  elimTy A
    ∎
elimTyOf {Γ} {A} (βπ₂ σ t p q i) =
  isProp→PathP {B = λ i →
      (r : tyOf (βπ₂ σ t p q i) ≡ A)
      → tyOf∙ (elimTm (βπ₂ σ t p q i)) ≡Ty[ r ] elimTy A}
   (λ j → isPropΠ λ p → isOfHLevelPathP' {A = λ i → Ty∙ (elimCtx Γ) (p i)} 1
   (λ _ _ → UIP) _ _)
   (elimTyOf (βπ₂ σ t p q i0)) (elimTyOf (βπ₂ σ t p q i1)) i
elimTyOf {Γ} {A} ([idS]t t i) =
  isProp→PathP {B = λ i →
      (r : tyOf ([idS]t t i) ≡ A)
      → tyOf∙ (elimTm ([idS]t t i)) ≡Ty[ r ] elimTy A}
    (λ j → isPropΠ λ p → isOfHLevelPathP' {A = λ i → Ty∙ (elimCtx Γ) (p i)} 1
    (λ _ _ → UIP) _ _)
    (elimTyOf ([idS]t t i0)) (elimTyOf ([idS]t t i1)) i
elimTyOf {Γ} {A} ([∘]t t σ τ i) =
  isProp→PathP {B = λ i →
    (r : tyOf ([∘]t t σ τ i) ≡ A)
    → tyOf∙ (elimTm ([∘]t t σ τ i)) ≡Ty[ r ] elimTy A}
    (λ j → isPropΠ λ p → isOfHLevelPathP' {A = λ i → Ty∙ (elimCtx Γ) (p i)} 1
    (λ _ _ → UIP) _ _)
  (elimTyOf ([∘]t t σ τ i0)) (elimTyOf ([∘]t t σ τ i1)) i
