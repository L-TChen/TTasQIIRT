{-# OPTIONS --lossy-unification #-}

open import Prelude

open import Theory.SC+El+Pi+B.QIIRT-tyOf.Model
open import Theory.SC.QIIRT-tyOf.DisplayedModel
open import Theory.SC+Pi+B.QIIRT-tyOf.DisplayedModel

module Theory.SC+El+Pi+B.QIIRT-tyOf.DisplayedModel
  (M : SC+El+Pi+B ℓ₁' ℓ₂' ℓ₃' ℓ₄') where

private
  module S = SC+El+Pi+B M

open S hiding (module Var)
open S.Var hiding (C)

module _ (𝒞∙ : SC∙ 𝒞 ℓ₁ ℓ₂ ℓ₃ ℓ₄) where
  open SC∙ 𝒞∙
  open Var

  record Univ∙ : Set (ℓ-suc (ℓ₁' ⊔ ℓ₂' ⊔ ℓ₃' ⊔ ℓ₄' ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)) where
    field
      El∙
        : (u∙ : Tm∙ Γ∙ u) (pt∙ : tyOf∙ u∙ ≡Ty[ pt ] U∙)
        → Ty∙ Γ∙ (El u pt)

      El[]∙
        : (τ∙ : Sub∙ Γ∙ Δ∙ τ) (u∙ : Tm∙ Δ∙ u) (pt∙ : tyOf∙ u∙ ≡Ty[ pt ] U∙)
        → (El∙ u∙ pt∙) [ τ∙ ]T∙ ≡Ty[ El[] τ u pt ]
          El∙ (u∙ [ τ∙ ]t∙) (tyOf[]≡U∙ {Γ} {Γ∙} {Δ} {Δ∙} {_} {_} {u∙} {pt} {τ∙} pt∙)

    opaque
      El[]₂∙
        : {Δ∙ : Ctx∙ Δ} (u∙ : Tm∙ Δ∙ u) {σ : Sub Γ Δ} {σ∙ : Sub∙ Γ∙ Δ∙ σ}
        → {pu : tyOf u ≡ U} (pu∙ : tyOf∙ u∙ ≡Ty[ pu ] U∙)
        → tyOf∙ (π₂∙ {_} {Γ∙ ,∙ El∙ (u∙ [ σ∙ ]t∙) (tyOf[]≡U∙ pu∙)} idS∙)
        ≡Ty[ El[]₂ u pu ]
          El∙ u∙ pu∙ [ σ∙ ∘∙ π₁∙ idS∙ ]T∙
      El[]₂∙ {Δ} {u} {Γ} {Γ∙} {Δ∙} u∙ {σ} {σ∙} {pu} pu∙ = beginTy
        tyOf∙ (π₂∙ idS∙)
          ≡Ty[ tyOfπ₂ idS ]⟨ tyOfπ₂∙ idS∙ ⟩
        El∙ (u∙ [ σ∙ ]t∙) (tyOf[]≡U∙ pu∙) [ π₁∙ idS∙ ]T∙
          ≡Ty[ El[] (π₁ idS) (u [ σ ]t) (tyOf[]≡U pu) ∙ cong₂ El ([∘]t u (π₁ idS) σ) (tyOftyOf[]≡U pu) ]⟨ (El[]∙ (π₁∙ idS∙) (u∙ [ σ∙ ]t∙) (tyOf[]≡U∙ pu∙) ∙P
            (λ i → El∙ ([∘]t∙ u∙ (π₁∙ {{!!}} {{!!}} idS∙) σ∙ i) {!!})) ⟩
        -- similar to El[]₂
        El∙ (u∙ [ σ∙ ∘∙ π₁∙ idS∙ ]t∙) (tyOf[]≡U∙ pu∙)
          ≡Ty[ sym (El[] (σ ∘ π₁ idS) u pu) ]⟨ symP (El[]∙ (σ∙ ∘∙ π₁∙ idS∙) u∙ pu∙) ⟩
        (El∙ u∙ pu∙ [ σ∙ ∘∙ π₁∙ idS∙ ]T∙)
          ∎

  record Univ𝓑∙ (𝒰∙ : Univ∙) (ℬ : Bool∙
    (record { 𝒞 = 𝒞 ; 𝒫i = 𝒫i ; ℬ = ℬ }) 𝒞∙) : Set (ℓ-suc (ℓ₁' ⊔ ℓ₂' ⊔ ℓ₃' ⊔ ℓ₄' ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)) where
    open Univ∙ 𝒰∙
    open Bool∙ ℬ

    field
      𝕓∙
        : Tm∙ Γ∙ 𝕓
      𝕓[]∙
        : (σ∙ : Sub∙ Γ∙ Δ∙ σ)
        → 𝕓∙ [ σ∙ ]t∙ ≡Tm[ 𝕓[] σ ] 𝕓∙
      tyOf𝕓∙
        : tyOf∙ {Γ∙ = Γ∙} 𝕓∙ ≡Ty[ tyOf𝕓 ] U∙
      El𝕓
        : (Γ∙ : Ctx∙ Γ)
        → El∙ {Γ∙ = Γ∙} 𝕓∙ tyOf𝕓∙ ≡Ty[ El𝕓 Γ ] 𝔹∙


  record UnivPi∙ (𝒰∙ : Univ∙) (𝒫i∙ : Pi∙
    (record { 𝒞 = 𝒞 ; 𝒫i = 𝒫i ; ℬ = ℬ }) 𝒞∙) : Set (ℓ-suc (ℓ₁' ⊔ ℓ₂' ⊔ ℓ₃' ⊔ ℓ₄' ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)) where
    open Univ∙ 𝒰∙
    open Pi∙ 𝒫i∙
    
    _↑El∙
      : {Δ∙ : Ctx∙ Δ} (σ∙ : Sub∙ Γ∙ Δ∙ σ)
      → {u∙ : Tm∙ Δ∙ u} {pu∙ : tyOf∙ u∙ ≡Ty[ pu ] U∙}
      → Sub∙ (Γ∙ ,∙ El∙ (u∙ [ σ∙ ]t∙) (tyOf[]≡U∙ pu∙)) (Δ∙ ,∙ El∙ u∙ pu∙)
        (σ ↑El)
    _↑El∙ {Γ∙} {Δ∙} {σ} {_} {u} {pu} σ∙ {u∙} {pu∙} =
      (σ∙ ∘∙ π₁∙ idS∙) , π₂∙ idS∙ ∶[ El[]₂ u pu , El[]₂∙ u∙ pu∙ ]∙

    field
      π∙
        : {a : Tm Γ} (a∙ : Tm∙ Γ∙ a)
          {pa : tyOf a ≡ U} (pa∙ : tyOf∙ a∙ ≡Ty[ pa ] U∙)
        → {b : Tm (Γ ,C El a pa)} (b∙ : Tm∙ (Γ∙ ,∙ El∙ a∙ pa∙) b)
          {pb : tyOf b ≡ U} (pb∙ : tyOf∙ b∙ ≡Ty[ pb ] U∙)
        → Tm∙ Γ∙ (π a pa b pb)
      π[]∙
        : {σ : Sub Δ Γ} (σ∙ : Sub∙ Δ∙ Γ∙ σ)
        → {a : Tm Γ} (a∙ : Tm∙ Γ∙ a)
        → {pa : tyOf a ≡ U} (pa∙ : tyOf∙ a∙ ≡Ty[ pa ] U∙)
        → {b : Tm (Γ ,C El a pa)} (b∙ : Tm∙ (Γ∙ ,∙ El∙ a∙ pa∙) b)
        → {pb : tyOf b ≡ U} (pb∙ : tyOf∙ b∙ ≡Ty[ pb ] U∙)
        → (π∙ a∙ pa∙ b∙ pb∙ [ σ∙ ]t∙)
            ≡Tm[ π[] a pa b pb ]
          π∙ (a∙ [ σ∙ ]t∙) (tyOf[]≡U∙ pa∙) (b∙ [ σ∙ ↑El∙ ]t∙)
            (tyOf[]≡U∙ {Δ ,C El (a [ σ ]t) (tyOf[]≡U pa)} pb∙)
      tyOfπ∙
        : {a : Tm Γ} (a∙ : Tm∙ Γ∙ a)
        → {pa : tyOf a ≡ U} (pa∙ : tyOf∙ a∙ ≡Ty[ pa ] U∙)
        → {b : Tm (Γ ,C El a pa)} (b∙ : Tm∙ (Γ∙ ,∙ El∙ a∙ pa∙) b)
        → {pb : tyOf b ≡ U} (pb∙ : tyOf∙ b∙ ≡Ty[ pb ] U∙)
        → tyOf∙ (π∙ a∙ pa∙ b∙ pb∙) ≡Ty[ tyOfπ a pa b pb ] U∙
      Elπ∙
        : {a : Tm Γ} (a∙ : Tm∙ Γ∙ a)
        → {pa : tyOf a ≡ U} (pa∙ : tyOf∙ a∙ ≡Ty[ pa ] U∙)
        → {b : Tm (Γ ,C El a pa)} (b∙ : Tm∙ (Γ∙ ,∙ El∙ a∙ pa∙) b)
        → {pb : tyOf b ≡ U} (pb∙ : tyOf∙ b∙ ≡Ty[ pb ] U∙)
        → El∙ (π∙ a∙ pa∙ b∙ pb∙) (tyOfπ∙ a∙ pa∙ b∙ pb∙)
          ≡Ty[ Elπ a pa b pb ]
          Π∙ (El∙ a∙ pa∙) (El∙ b∙ pb∙)
