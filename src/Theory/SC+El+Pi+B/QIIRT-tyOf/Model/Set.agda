open import Prelude

module Theory.SC+El+Pi+B.QIIRT-tyOf.Model.Set where

open import Theory.SC+El+Pi+B.QIIRT-tyOf.Model

open import Theory.SC+El+Pi+B.QIIRT-tyOf.Syntax
open import Theory.SC+El+Pi+B.QIIRT-tyOf.Model
open import Theory.SC+Pi+B.QIIRT-tyOf.Model.Set
open Var

opaque
  unfolding _∙_
  unfolding stdModel𝓑
  unfolding stdModelPi
  
  stdModelUniv : Univ stdModel
  stdModelUniv .Univ.El  (A , u) pu γ =
      T (subst (λ A → A γ) pu (u γ))
  stdModelUniv .Univ.El[] {Γ} {Δ} σ (A , u) pu = funExt λ γ →
    cong T (cong (transport (λ i → pu i (σ γ))) (sym $ transportRefl³ (u (σ γ))))

  stdModelUnivPi : UnivPi stdModel stdModelUniv stdModelPi
  stdModelUnivPi .UnivPi.El[]₂ {Γ} {Δ} {σ = σ} (A , u) pu pu' = funExt λ (γ , t) →
    cong T (cong (λ p → transport p (u (σ γ))) (UIP (λ i → pu' i γ) λ i → pu i (σ γ)))

  stdModelUnivPi .UnivPi.π     (A , a) pa (B , b) pb =
    (λ _ → UU) , λ γ → pi
      (transport (λ i → pa i γ) (a γ)) λ x → transport (λ i → pb i (γ , x)) (b (γ , x)) 
  stdModelUnivPi .UnivPi.π[] {σ = σ} (A , a) pa b pb pa' pb' =
    ΣPathP (refl , (funExt (λ γ → cong₂ pi
      (cong (λ p → transport p (a (σ γ))) (UIP (λ i → pa i (σ γ)) λ i → pa' i γ))
      λ i x → {!!})))
  stdModelUnivPi .UnivPi.tyOfπ (A , a) pa b pb = refl
  stdModelUnivPi .UnivPi.Elπ   (A , a) pa b pb = refl

  stdModelUniv𝓑 : Univ𝓑 stdModel stdModelUniv stdModel𝓑
  stdModelUniv𝓑 .Univ𝓑.𝕓     = (λ _ → UU) , λ _ → bool
  stdModelUniv𝓑 .Univ𝓑.𝕓[] σ = refl
  stdModelUniv𝓑 .Univ𝓑.tyOf𝕓 = refl
  stdModelUniv𝓑 .Univ𝓑.El𝕓 γ = refl

-- ⟦ π[] {σ = σ} a pa b pb pa' pb' i ⟧t γ =
--   pi (transp (λ k → foo₁ i k) i0 (⟦ a ⟧t (⟦ σ ⟧S γ))) {!!}
--  where
--   foo₁ : (λ i₁ → ⟦ pa i₁ ⟧T (⟦ σ ⟧S γ)) ≡ (λ i₁ → ⟦ pa' i₁ ⟧T γ)
--   foo₁ = UIP (λ i₁ → ⟦ pa i₁ ⟧T (⟦ σ ⟧S γ)) (λ i₁ → ⟦ pa' i₁ ⟧T γ)
-- --  foo₂ : ∀ z → (λ i₁ → ⟦ pb i₁ ⟧T (⟦ σ ⟧S γ , z)) ≡ (λ i₁ → ⟦ pb' i₁ ⟧T (γ , z))
-- --  foo₂ z = UIP _ _

