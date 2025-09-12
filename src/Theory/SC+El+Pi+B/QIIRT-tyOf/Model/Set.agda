{-# OPTIONS --lossy-unification #-}
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
  unfolding Univ.El[]₂
  
  stdModelUniv : Univ stdModel
  stdModelUniv .Univ.El {Γ} (A , u) pu γ = T (subst (λ A → A γ) pu (u γ))
  stdModelUniv .Univ.El[] {Γ} {Δ} σ (A , a) pa i = λ γ →
    T (transport (λ i → pa i (σ γ)) (transportRefl³ (a (σ γ)) (~ i))) 

  stdModelUnivPi : UnivPi stdModel stdModelUniv stdModelPi
-- --  stdModelUnivPi .UnivPi.El[]₂ {Γ} {Δ} {σ = σ} (A , u) pu pu' = funExt λ (γ , t) →
-- --    cong T (cong (λ p → transport p (u (σ γ))) (UIP (λ i → pu' i γ) λ i → pu i (σ γ)))
  stdModelUnivPi .UnivPi.π     (A , a) pa (B , b) pb = (λ _ → UU) , λ γ → pi
    (transport (λ i → pa i γ) (a γ)) λ x → transport (λ i → pb i (γ , x)) (b (γ , x))
  stdModelUnivPi .UnivPi.π[] {Δ} {Γ} {σ} (A , a) pa (B , b) pb i = (λ _ → UU) , λ γ →
    pi (transport (λ i → pa i (σ γ)) (transportRefl³ (a (σ γ)) (~ i))) (lem γ i)
--       -- If we could use J to make pa = refl and A = UU, the above would be constant, which would make the below much easier...
    where
     lem : ∀ γ
       → PathP (λ i → T (transport (λ j → pa j (σ γ)) (transportRefl³ (a (σ γ)) (~ i))) → UU)
           (λ x → transport (λ i → pb i (σ γ , x)) (b (σ γ , x)))
           (λ x → transport (λ i → pb i (σ γ , transport (λ j → Univ.El[]₂ stdModelUniv {σ = σ} (A , a) pa j (γ , x)) x))
                     (transport refl (transport refl (transport refl (b (σ γ , transport (λ j → Univ.El[]₂ stdModelUniv {σ = σ} (A , a) pa j (γ , x)) x))))))
     lem γ i x = transport (λ j → pb j (σ γ , {!transport-filler!})) {!!}

-- El[]₂ : ∀ (γ , t) → T (transport (λ i → pu' i γ) (u (σ γ))) ≡ T (transport (λ i → pu i (σ γ)) (u (σ γ)))
{-{!(λ γ → cong₂ pi
      cong (λ p → transport p (a (σ γ))) (UIP (λ i → pa i (σ γ)) (λ i → pa' i γ))!}
      λ i x → let x' = subst T (cong (λ p → transport p (a (σ γ))) (UIP (UIP (λ i₂ → pa i₂ (σ γ)) (λ i₂ → pa' i₂ γ) i) (λ i₁ → pa i₁ (σ γ)))) x
                  x'' = subst T (cong (λ p → transport p (a (σ γ))) (UIP (UIP (λ i₂ → pa i₂ (σ γ)) (λ i₂ → pa' i₂ γ) i) (λ i₁ → pa' i₁ γ))) x
      -- (UIP (UIP (λ i₂ → pa i₂ (σ γ)) (λ i₂ → pa' i₂ γ) i) (λ i₁ → pa i₁ (σ γ)))) x
              in transport (UIP (λ j → pb j (σ γ , {!x'!})) (λ j → pb' j (γ , x'')) i) (b .snd (σ γ , x')))!}))-}
  stdModelUnivPi .UnivPi.tyOfπ (A , a) pa b pb = refl
  stdModelUnivPi .UnivPi.Elπ   (A , a) pa b pb = refl

  stdModelUniv𝓑 : Univ𝓑 stdModel stdModelUniv stdModel𝓑
  stdModelUniv𝓑 .Univ𝓑.𝕓     = (λ _ → UU) , λ _ → bool
  stdModelUniv𝓑 .Univ𝓑.𝕓[] σ = refl
  stdModelUniv𝓑 .Univ𝓑.tyOf𝕓 = refl
  stdModelUniv𝓑 .Univ𝓑.El𝕓 γ = refl

-- ⟦ π[] {σ = σ} a pa b pb pa' pb' i ⟧t γ =
--   pi (transp (λ k → foo₁ i k) i0 (⟦ a ⟧t (⟦ σ ⟧S γ))) {!!}
