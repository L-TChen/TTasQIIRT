open import Prelude

open import Theory.SC.QIIRT-tyOf.Model

module Theory.SC.QIIRT-tyOf.Rec (C : SC ℓ₁ ℓ₂ ℓ₃ ℓ₄) where

open SC C

import Theory.SC.QIIRT-tyOf.Syntax as S
open S.Var


recCtx  : S.Ctx → Ctx
{-# TERMINATING #-}
recTy   : S.Ty Γ → Ty (recCtx Γ)
recTm   : S.Tm Γ → Tm (recCtx Γ)
recSub  : S.Sub Γ Δ → Sub (recCtx Γ) (recCtx Δ)
recTyOf : (t : S.Tm Γ) → S.tyOf t ≡ A → tyOf (recTm t) ≡ recTy A

recCtx S.∅ = ∅
recCtx (Γ S., A) = recCtx Γ ,C recTy A

recTy (A S.[ σ ]) = recTy A [ recSub σ ]T
recTy S.U         = U
recTy (S.[idS]T {A = A} i) = [idS]T {A = recTy A} i
recTy (S.[∘]T A σ τ i)     = [∘]T (recTy A) (recSub σ) (recSub τ) i
recTy (S.U[] {σ = σ} i)    = U[] {σ = recSub σ} i
recTy (S.Ty-is-set A B p q i j) =
  isSet→SquareP (λ _ _ → Ty-is-set) (λ i → recTy (p i)) (λ i → recTy (q i)) refl refl i j

recTm (t S.[ σ ])       = recTm t [ recSub σ ]t
recTm (S.π₂ σ)          = π₂ (recSub σ)
recTm (S.βπ₂ {A = A} σ t p _ i) =
  βπ₂ (recSub σ) (recTm t) (recTyOf t p) i
recTm (S.[idS]t t i)    = [idS]t (recTm t) i
recTm (S.[∘]t t σ τ i)  = [∘]t (recTm t) (recSub σ) (recSub τ) i
recTm (S.Tm-is-set t u p q i j) =
  Tm-is-set (recTm t) (recTm u) (cong recTm p) (cong recTm q) i j

recSub S.∅              = ∅S
recSub (σ S., t ∶[ p ]) = recSub σ , recTm t ∶[ recTyOf t p ]
recSub S.idS            = idS
recSub (τ S.∘ σ)        = recSub τ ∘ recSub σ
recSub (S.π₁ σ)         = π₁ (recSub σ)
recSub (S.βπ₁ σ t p i)  = βπ₁ (recSub σ) (recTm t) (recTyOf t p) i
recSub ((S.idS∘ σ) i)   = (idS∘ recSub σ) i
recSub ((σ S.∘idS) i)   = (recSub σ ∘idS) i
recSub (S.assocS σ τ γ i) = assocS (recSub σ) (recSub τ) (recSub γ) i
recSub (S.η∅ σ i) = η∅ (recSub σ) i
recSub (S.ηπ {Γ} {Δ} {A} σ i) =
   (ηπ (recSub σ) ∙ cong (π₁ (recSub σ) , π₂ (recSub σ) ∶[_])
                        (Ty-is-set _ _ (tyOfπ₂ (recSub σ))
                                      (tyOfπ₂ (recSub σ) ∙ (λ i₁ → recTy A [ π₁ (recSub σ) ]T)))) i
recSub (S.,∘ {A = A} τ t σ p q i) =
 ,∘ (recSub τ) (recTm t) (recSub σ) (recTyOf t p) (recTyOf (t S.[ σ ]) q) i
-- -- The following fails to pass the termination checker in SetModel.agda
-- --      (recSub τ , recTm t ∶[ recTyOf t p ]) ∘ recSub σ
-- --        ≡⟨ ,∘ (recSub τ) (recTm t) (recSub σ) (recTyOf t p) ⟩
-- --      (recSub τ ∘ recSub σ) , recTm t [ recSub σ ]t ∶[ _ ]
-- --       ≡[ i ]⟨ ((recSub τ ∘ recSub σ) , recTm t [ recSub σ ]t ∶[ Tyᴬ-is-set _ _ (step-≡ (tyOfᴬ (recTm t [ recSub σ ]t))
-- --                                                           (≡⟨⟩-syntax (tyOfᴬ (recTm t) [ recSub σ ]T)
-- --                                                            (step-≡ ((recTy A [ recSub τ ]T) [ recSub σ ]T)
-- --                                                             ((recTy A [ recSub τ ∘ recSub σ ]T) ∎)
-- --                                                             ([∘]T (recTy A) (recSub σ) (recSub τ)))
-- --                                                            (λ i₁ → recTyOf t p i₁ [ recSub σ ]T))
-- --                                                           tyOf[]) (recTyOf (t [ σ ]) q) i ]) ⟩
-- --      (recSub τ ∘ recSub σ) , recTm t [ recSub σ ]t ∶[ recTyOf (t [ σ ]) q ]
-- --        ∎
recSub (S.Sub-is-set σ σ' p q i j) =
  isSet→SquareP (λ _ _ → Sub-is-set) (λ i → recSub (p i)) (λ i → recSub (q i)) refl refl i j

recTyOf (t S.[ σ ]) p      = tyOf[] ∙ cong _[ recSub σ ]T (recTyOf t refl) ∙ cong recTy p
recTyOf (S.π₂ σ) p         = tyOfπ₂ (recSub σ) ∙ cong recTy p
recTyOf {A = A} (S.βπ₂ σ t p₁ q i) =
-- Ideally we shouldn't have to deal with these coherence proofs as they should hold in set-level cubical type theory.
 isProp→PathP {B = λ i → S.tyOf (S.βπ₂ σ t p₁ q i) ≡ A → tyOf ( recTm (S.βπ₂ σ t p₁ q i) ) ≡ recTy A}
 (λ j → isPropΠ (λ _ → Ty-is-set _ _)) ( recTyOf (S.π₂ (σ S., t ∶[ p₁ ])) ) (recTyOf t) i -- (recTyOf (S.βπ₂ σ t p₁ q i1)) i
recTyOf {A = A} (S.[idS]t t i) =
 isProp→PathP
   {B = λ i → S.tyOf (S.[idS]t t i) ≡ A → tyOf ( recTm (S.[idS]t t i) ) ≡ recTy A}
   (λ j → isPropΠ λ _ → Ty-is-set _ _)
   (recTyOf t)
   (λ (p : (S.tyOf t S.[ S.idS ] ≡ A)) → tyOf[] ∙ cong _[ idS ]T (recTyOf t refl) ∙ cong recTy p ) i
recTyOf {A = A} (S.[∘]t t σ τ i) =
 isProp→PathP {B = λ i → S.tyOf (S.[∘]t t σ τ i) ≡ A → tyOf (recTm (S.[∘]t t σ τ i)) ≡ recTy A}
 (λ j → isPropΠ λ _ → Ty-is-set _ _) (recTyOf (S.[∘]t t σ τ i0)) (recTyOf (S.[∘]t t σ τ i1)) i
recTyOf {A = A} (S.Tm-is-set t u p q i j) =
 isSet→SquareP
  {A = λ i j → S.tyOf (S.Tm-is-set t u p q i j) ≡ A → tyOf (recTm (S.Tm-is-set t u p q i j)) ≡ recTy A}
  (λ i j → isSetΠ λ _ → isProp→isSet (Ty-is-set (tyOf ( recTm (S.Tm-is-set t u p q i j))) (recTy A)))
  (λ j → recTyOf (p j))
  (λ j → recTyOf (q j))
  (λ j → recTyOf t)
  (λ j → recTyOf u) i j
