open import Prelude

open import Theory.SC.QIIRT-tyOf.Model

module Theory.SC.QIIRT-tyOf.Rec (mot : Motive ℓ₁ ℓ₂ ℓ₃ ℓ₄) (m : SC mot) where

open Motive mot
open SC m

import Theory.SC.QIIRT-tyOf.Syntax as S
open S.GVars

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
recTy (S.[idS]T {A = A} i) = [idS]T {A = recTy A} i -- [idS]T {A = recTy A} i
recTy (S.[∘]T A σ τ i)     = [∘]T (recTy A) (recSub σ) (recSub τ) i
recTy (S.U[] {σ = σ} i)    = U[] {σ = recSub σ} i
-- recTy (S.Ty-is-set A B x y i j) = ?
--  isSet→SquareP (λ _ _ → Ty-is-set) (λ i → recTy (x i)) (λ i → recTy (y i)) refl refl i j

recSub⟨π₁,⟩≡π₁,
  : (σ : S.Sub Γ Δ) (A : S.Ty Δ) (p : S.tyOf t ≡ A S.[ σ ])
  → recTy A [ π₁ (recSub σ , recTm t ∶[ recTyOf t p ]) ]T
  ≡ recTy A [ recSub (S.π₁ (σ S., t ∶[ p ])) ]T
  
recTm (t S.[ σ ])       = recTm t [ recSub σ ]t
recTm (S.π₂ σ)          = π₂ (recSub σ)
recTm (S.βπ₂ {A = A} σ t p _ i) = 
  βπ₂ (recSub σ) (recTm t) (recTyOf t p) i
recTm (S.[idS]t t i)    = [idS]t (recTm t) i
recTm (S.[∘]t t σ τ i)  = [∘]t (recTm t) (recSub σ) (recSub τ) i
-- recTm (Tm-is-set t u p q i j) =
--   Tmᴬ-is-set (recTm t) (recTm u) (cong recTm p) (cong recTm q) i j

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
recSub (S.ηπ {Γ} {Δ} {A} σ i) = (ηπ (recSub σ) ∙ bar) i
  where
    bar =
      π₁ (recSub σ) , π₂ (recSub σ) ∶[ tyOfπ₂ (recSub σ) ]
        ≡[ i ]⟨ (π₁ (recSub σ) , π₂ (recSub σ) ∶[ UIP (tyOfπ₂ (recSub σ)) (recTyOf (S.π₂ σ) (S.tyOfπ₂ σ)) i ]) ⟩
        -- ≡[ i ]⟨ (π₁ (recSub σ) , π₂ (recSub σ) ∶[ Tyᴬ-is-set _ _ (tyOfπ₂ (recSub σ)) (recTyOf (π₂ σ) (tyOfπ₂ σ)) i ]) ⟩
      π₁ (recSub σ) , recTm (S.π₂ σ) ∶[ recTyOf (S.π₂ σ) (S.tyOfπ₂ σ) ]
        ∎
 
recSub (S.,∘ {A = A} τ t σ p q i) = foo i
  where
    foo : (recSub τ , recTm t ∶[ recTyOf t p ]) ∘ recSub σ
      ≡ (recSub τ ∘ recSub σ) , recTm t [ recSub σ ]t ∶[ recTyOf (t S.[ σ ]) q ]
    foo =
      (recSub τ , recTm t ∶[ recTyOf t p ]) ∘ recSub σ
        ≡⟨ ,∘ (recSub τ) (recTm t) (recSub σ) (recTyOf t p) (recTyOf (t S.[ σ ]) q) ⟩
      (recSub τ ∘ recSub σ) , recTm t [ recSub σ ]t ∶[ recTyOf (t S.[ σ ]) q ]
        ∎
-- -- Liang-Ting (2025-06-26): The following fails to pass the termination checker in SetModel.agda
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
-- -- recSub (Sub-is-set σ σ' p q i j) = isSet→SquareP (λ _ _ → Subᴬ-is-set) (λ i → recSub (p i)) (λ i → recSub (q i)) refl refl i j

recSub⟨π₁,⟩≡π₁, _ _ _ = refl

recTyOf {A = A} (t S.[ σ ]) p =
  tyOf (recTm t [ recSub σ ]t)
    ≡⟨ tyOf[] ⟩
  (tyOf (recTm t)) [ recSub σ ]T 
    ≡[ i ]⟨ (recTyOf t refl i [ recSub σ ]T) ⟩
  recTy (S.tyOf t S.[ σ ])
    ≡[ i ]⟨ recTy (p i) ⟩
  recTy A
    ∎
  
recTyOf {A = A} (S.π₂ {Γ} {Δ} {B} σ) p =
  tyOf (recTm (S.π₂ σ))
    ≡⟨ tyOfπ₂ (recSub σ) ⟩
  recTy B [ π₁ (recSub σ) ]T
    ≡[ i ]⟨ recTy (p i) ⟩
  recTy A
    ∎
recTyOf {A = A} (S.βπ₂ σ t p₁ q i) = 
  isProp→PathP {B = λ i → S.tyOf (S.βπ₂ σ t p₁ q i) ≡ A → tyOf (recTm (S.βπ₂ σ t p₁ q i)) ≡ recTy A}
  (λ j → isPropΠ λ _ → UIP) (recTyOf (S.βπ₂ σ t p₁ q i0)) (recTyOf (S.βπ₂ σ t p₁ q i1)) i 
--  (λ j → isPropΠ (λ _ → Tyᴬ-is-set _ _)) (recTyOf (βπ₂ σ t p₁ q i0)) (recTyOf (βπ₂ σ t p₁ q i1)) i 
recTyOf {A = A} (S.[idS]t t i) =
  isProp→PathP {B = λ i → S.tyOf (S.[idS]t t i) ≡ A → tyOf (recTm (S.[idS]t t i)) ≡ recTy A}
  (λ j → isPropΠ λ _ → UIP) (recTyOf (S.[idS]t t i0)) (recTyOf (S.[idS]t t i1)) i 
--  (λ j → isPropΠ (λ _ → Tyᴬ-is-set _ _)) (recTyOf ([idS]t t i0)) (recTyOf ([idS]t t i1)) i 
recTyOf {A = A} (S.[∘]t t σ τ i) = 
  isProp→PathP {B = λ i → S.tyOf (S.[∘]t t σ τ i) ≡ A → tyOf (recTm (S.[∘]t t σ τ i)) ≡ recTy A}
  (λ j → isPropΠ λ _ → UIP) (recTyOf (S.[∘]t t σ τ i0)) (recTyOf (S.[∘]t t σ τ i1)) i 
--  (λ j → isPropΠ (λ _ → Tyᴬ-is-set _ _)) (recTyOf ([∘]t t σ τ i0)) (recTyOf ([∘]t t σ τ i1)) i 
-- recTyOf (Tm-is-set t u p q i j) = {!!}
