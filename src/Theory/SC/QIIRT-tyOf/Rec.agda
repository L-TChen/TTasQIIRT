open import Prelude

open import Theory.SC.QIIRT-tyOf.Model

module Theory.SC.QIIRT-tyOf.Rec (mot : Motive ℓ₁ ℓ₂ ℓ₃ ℓ₄) (m : SCᴹ mot) where
open Motive mot
open SCᴹ m

open import Theory.SC.QIIRT-tyOf.Syntax

recCtx  : Ctx → Ctxᴬ
{-# TERMINATING #-}
recTy   : {Γ : Ctx} → Ty Γ → Tyᴬ (recCtx Γ)
recTm   : {Γ : Ctx} → Tm Γ → Tmᴬ (recCtx Γ)
recSub  : {Γ Δ : Ctx} → Sub Γ Δ → Subᴬ (recCtx Γ) (recCtx Δ)
recTyOf : {Γ : Ctx}{A : Ty Γ} → (t : Tm Γ) → tyOf t ≡ A → tyOfᴬ (recTm t) ≡ recTy A

recCtx ∅ = ∅ᴹ
recCtx (Γ , A) = recCtx Γ ,ᴹ recTy A

recTy (A [ σ ]) = recTy A [ recSub σ ]Tᴹ
recTy U = Uᴹ
recTy ([idS]T {A = A} i) = [idS]Tᴹ {Aᴹ = recTy A} i
recTy ([∘]T A σ τ i) = [∘]Tᴹ (recTy A) (recSub σ) (recSub τ) i
recTy (U[] {σ = σ} i) = U[]ᴹ {σᴹ = recSub σ} i
recTy (Ty-is-set A B x y i j) =
  isSet→SquareP (λ _ _ → Tyᴬ-is-set) (λ i → recTy (x i)) (λ i → recTy (y i)) refl refl i j

recSub⟨π₁,⟩≡π₁ᴹ,ᴹ
  : (σ : Sub Γ Δ) (A : Ty Δ) (p : tyOf t ≡ A [ σ ])
  → recTy A [ π₁ᴹ (recSub σ ,ᴹ recTm t ∶[ recTyOf t p ]) ]Tᴹ
  ≡ recTy A [ recSub (π₁ (σ , t ∶[ p ])) ]Tᴹ
  
recTm (t [ σ ])       = recTm t [ recSub σ ]tᴹ
recTm (π₂ σ)          = π₂ᴹ (recSub σ)
recTm (βπ₂ {A = A} σ t p _ i) = 
  βπ₂ᴹ (recSub σ) (recTm t) (recTyOf t p) i
recTm ([idS]t t i)    = [idS]tᴹ (recTm t) i
recTm ([∘]t t σ τ i)  = [∘]tᴹ (recTm t) (recSub σ) (recSub τ) i

recSub ∅S             = ∅Sᴹ
recSub (σ , t ∶[ p ]) = recSub σ ,ᴹ recTm t ∶[ recTyOf t p ]
recSub idS            = idSᴹ
recSub (τ ∘ σ)        = recSub τ ∘ᴹ recSub σ
recSub (π₁ σ)         = π₁ᴹ (recSub σ)
recSub (βπ₁ σ t p i)  = βπ₁ᴹ (recSub σ) (recTm t) (recTyOf t p) i
recSub ((idS∘ σ) i)   = (idS∘ᴹ recSub σ) i
recSub ((σ ∘idS) i)   = (recSub σ ∘idSᴹ) i
recSub (assocS σ τ γ i) = assocSᴹ (recSub σ) (recSub τ) (recSub γ) i
recSub (η∅ σ i) = η∅ᴹ (recSub σ) i
recSub (ηπ {Γ} {Δ} {A} σ i) = (ηπᴹ (recSub σ) ∙ bar) i
  where
    bar =
      π₁ᴹ (recSub σ) ,ᴹ π₂ᴹ (recSub σ) ∶[ tyOfπ₂ᴹ (recTy A) (recSub σ) ]
        ≡[ i ]⟨ (π₁ᴹ (recSub σ) ,ᴹ π₂ᴹ (recSub σ) ∶[ Tyᴬ-is-set _ _ (tyOfπ₂ᴹ (recTy A) (recSub σ)) (recTyOf (π₂ σ) (tyOfπ₂ σ)) i ]) ⟩
      π₁ᴹ (recSub σ) ,ᴹ recTm (π₂ σ) ∶[ recTyOf (π₂ σ) (tyOfπ₂ σ) ]
        ∎
    
recSub (,∘ {A = A} τ t σ p q i) = foo i
  where
    foo : (recSub τ ,ᴹ recTm t ∶[ recTyOf t p ]) ∘ᴹ recSub σ
      ≡ (recSub τ ∘ᴹ recSub σ) ,ᴹ recTm t [ recSub σ ]tᴹ ∶[ recTyOf (t [ σ ]) q ]
    foo =
      (recSub τ ,ᴹ recTm t ∶[ recTyOf t p ]) ∘ᴹ recSub σ
        ≡⟨ ,∘ᴹ (recSub τ) (recTm t) (recSub σ) (recTyOf t p) (recTyOf (t [ σ ]) q) ⟩
      (recSub τ ∘ᴹ recSub σ) ,ᴹ recTm t [ recSub σ ]tᴹ ∶[ recTyOf (t [ σ ]) q ]
        ∎
-- Liang-Ting (2025-06-26): The following fails to pass the termination checker in SetModel.agda
--      (recSub τ ,ᴹ recTm t ∶[ recTyOf t p ]) ∘ᴹ recSub σ
--        ≡⟨ ,∘ᴹ (recSub τ) (recTm t) (recSub σ) (recTyOf t p) ⟩
--      (recSub τ ∘ᴹ recSub σ) ,ᴹ recTm t [ recSub σ ]tᴹ ∶[ _ ]
--       ≡[ i ]⟨ ((recSub τ ∘ᴹ recSub σ) ,ᴹ recTm t [ recSub σ ]tᴹ ∶[ Tyᴬ-is-set _ _ (step-≡ (tyOfᴬ (recTm t [ recSub σ ]tᴹ))
--                                                           (≡⟨⟩-syntax (tyOfᴬ (recTm t) [ recSub σ ]Tᴹ)
--                                                            (step-≡ ((recTy A [ recSub τ ]Tᴹ) [ recSub σ ]Tᴹ)
--                                                             ((recTy A [ recSub τ ∘ᴹ recSub σ ]Tᴹ) ∎)
--                                                             ([∘]Tᴹ (recTy A) (recSub σ) (recSub τ)))
--                                                            (λ i₁ → recTyOf t p i₁ [ recSub σ ]Tᴹ))
--                                                           tyOf[]ᴹ) (recTyOf (t [ σ ]) q) i ]) ⟩
--      (recSub τ ∘ᴹ recSub σ) ,ᴹ recTm t [ recSub σ ]tᴹ ∶[ recTyOf (t [ σ ]) q ]
--        ∎

recSub⟨π₁,⟩≡π₁ᴹ,ᴹ _ _ _ = refl

recTyOf {A = A} (t [ σ ]) p =
  tyOfᴬ (recTm t [ recSub σ ]tᴹ)
    ≡⟨ tyOf[]ᴹ ⟩
  (tyOfᴬ (recTm t)) [ recSub σ ]Tᴹ 
    ≡[ i ]⟨ (recTyOf t refl i [ recSub σ ]Tᴹ) ⟩
  recTy (tyOf t [ σ ])
    ≡[ i ]⟨ recTy (p i) ⟩
  recTy A
    ∎
  
recTyOf {A = A} (π₂ {Γ} {Δ} {B} σ) p =
  tyOfᴬ (recTm (π₂ σ))
    ≡⟨ tyOfπ₂ᴹ (recTy B) (recSub σ) ⟩
  recTy B [ π₁ᴹ (recSub σ) ]Tᴹ
    ≡[ i ]⟨ recTy (p i) ⟩
  recTy A
    ∎
recTyOf {A = A} (βπ₂ σ t p₁ q i) = 
  isProp→PathP {B = λ i → tyOf (βπ₂ σ t p₁ q i) ≡ A → tyOfᴬ (recTm (βπ₂ σ t p₁ q i)) ≡ recTy A}
  (λ j → isPropΠ (λ _ → Tyᴬ-is-set _ _)) (recTyOf (βπ₂ σ t p₁ q i0)) (recTyOf (βπ₂ σ t p₁ q i1)) i 
recTyOf {A = A} ([idS]t t i) =
  isProp→PathP {B = λ i → tyOf ([idS]t t i) ≡ A → tyOfᴬ (recTm ([idS]t t i)) ≡ recTy A}
  (λ j → isPropΠ (λ _ → Tyᴬ-is-set _ _)) (recTyOf ([idS]t t i0)) (recTyOf ([idS]t t i1)) i 
recTyOf {A = A} ([∘]t t σ τ i) = 
  isProp→PathP {B = λ i → tyOf ([∘]t t σ τ i) ≡ A → tyOfᴬ (recTm ([∘]t t σ τ i)) ≡ recTy A}
  (λ j → isPropΠ (λ _ → Tyᴬ-is-set _ _)) (recTyOf ([∘]t t σ τ i0)) (recTyOf ([∘]t t σ τ i1)) i 
