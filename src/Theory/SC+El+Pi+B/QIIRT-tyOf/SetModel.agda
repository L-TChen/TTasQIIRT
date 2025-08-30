open import Prelude

module Theory.SC+El+Pi+B.QIIRT-tyOf.SetModel where

open import Theory.SC+El+Pi+B.QIIRT-tyOf.Model

open import Theory.SC+El+Pi+B.QIIRT-tyOf.Syntax
open import Theory.SC+El+Pi+B.QIIRT-tyOf.Model
open import Theory.SC+Pi+B.QIIRT-tyOf.Model.Set
open Var

stdModelUniv : Univ stdModel
stdModelUniv .Univ.El  (A , u) p γ =
    T (subst (λ A → A γ) p (u γ))
stdModelUniv .Univ.El[] = {! a ?  !}

stdModelUnivPi : UnivPi stdModel stdModelUniv stdModelPi
stdModelUnivPi = {!   !}

stdModelUniv𝓑 : Univ𝓑 stdModel stdModelUniv stdModel𝓑
stdModelUniv𝓑 = {!   !}

-- ⟦_⟧S : (σ : Sub Γ Δ) → ⟦ Γ ⟧C → ⟦ Δ ⟧C

-- ⟦_,_⟧p : {Γ : Ctx}(t : Tm Γ){A : Ty Γ} → tyOf t ≡ A → {γ : ⟦ Γ ⟧C} → ⟦ tyOf t ⟧T γ → ⟦ A ⟧T γ
-- ⟦ t , p ⟧p {γ = γ} = subst (λ z → ⟦ z ⟧T γ) p

-- ⟦ El u p ⟧T γ = T (⟦ u , p ⟧p (⟦ u ⟧t γ))
-- ⟦ El[] τ u p q i ⟧T γ = T (transp (λ j → foo i j) i0 (⟦ u ⟧t (⟦ τ ⟧S γ)))
--   where
--     foo : cong (λ z → ⟦ z ⟧T (⟦ τ ⟧S γ)) p ≡ cong (λ z → ⟦ z ⟧T γ) q
--     foo = UIP (cong (λ z → ⟦ z ⟧T (⟦ τ ⟧S γ)) p) (cong (λ z → ⟦ z ⟧T γ) q)
-- ⟦ El[]₂ {σ = σ} u pu pu' i ⟧T (γ , x) = T (transp (λ k → foo i k) i0 (⟦ u ⟧t (⟦ σ ⟧S γ)))
--   where
--     foo : (λ i₁ → ⟦ pu' i₁ ⟧T γ) ≡ (λ i₁ → ⟦ pu i₁ ⟧T (⟦ σ ⟧S γ))
--     foo = UIP _ _
-- ⟦ 𝔹[]₂ i ⟧T γ = Bool
-- ⟦ El𝕓 σ i ⟧T γ  = Bool
-- ⟦ tyOfπ a pa b pb i ⟧T γ = UU
-- ⟦ Elπ a pa b pb i ⟧T γ = (x : T (transp (λ i₁ → ⟦ pa i₁ ⟧T γ) i0 (⟦ a ⟧t γ))) → T (transp (λ i₁ → ⟦ pb i₁ ⟧T (γ , x)) i0 (⟦ b ⟧t (γ , x)))
-- -- ⟦ Ty-is-set A B x y i j ⟧T γ = -- Following directly from the assumption UIP
-- --   isSet→SquareP (λ _ _ → λ X Y → UIP)
-- --     (λ i → ⟦ x i ⟧T γ)
-- --     (λ i → ⟦ y i ⟧T γ)
-- --     refl
-- --     refl
-- --     i j

-- ⟦ 𝕓 ⟧t γ = bool
-- ⟦ 𝕓[] σ i ⟧t γ = bool
-- ⟦ π a pa b pb ⟧t γ = pi (⟦ a , pa ⟧p (⟦ a ⟧t γ)) λ x → ⟦ b , pb ⟧p (⟦ b ⟧t (γ , x))
-- ⟦ π[] {σ = σ} a pa b pb pa' pb' i ⟧t γ =
--   pi (transp (λ k → foo₁ i k) i0 (⟦ a ⟧t (⟦ σ ⟧S γ))) {!!}
--  where
--   foo₁ : (λ i₁ → ⟦ pa i₁ ⟧T (⟦ σ ⟧S γ)) ≡ (λ i₁ → ⟦ pa' i₁ ⟧T γ)
--   foo₁ = UIP (λ i₁ → ⟦ pa i₁ ⟧T (⟦ σ ⟧S γ)) (λ i₁ → ⟦ pa' i₁ ⟧T γ)
-- --  foo₂ : ∀ z → (λ i₁ → ⟦ pb i₁ ⟧T (⟦ σ ⟧S γ , z)) ≡ (λ i₁ → ⟦ pb' i₁ ⟧T (γ , z))
-- --  foo₂ z = UIP _ _

