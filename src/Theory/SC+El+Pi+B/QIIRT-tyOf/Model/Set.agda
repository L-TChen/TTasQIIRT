{-# OPTIONS --lossy-unification #-}
open import Prelude

module Theory.SC+El+Pi+B.QIIRT-tyOf.Model.Set where

open import Theory.SC+El+Pi+B.QIIRT-tyOf.Model

open import Theory.SC+El+Pi+B.QIIRT-tyOf.Syntax
open import Theory.SC+El+Pi+B.QIIRT-tyOf.Model
open import Theory.SC+Pi+B.QIIRT-tyOf.Model.Set
open Var

opaque
  unfolding stdModelPi

  stdModelUniv : Univ stdModel
  stdModelUniv .Univ.El {Γ} (A , u) pu γ = T (subst (λ A → A γ) pu (u γ))
  stdModelUniv .Univ.El[] {Γ} {Δ} σ (A , a) pa = refl
  stdModelUniv . Univ.El[]₂ u pu = refl
  stdModelUniv . Univ._↑El σ (γ , x) = (σ γ) , x
  stdModelUniv . Univ.↑El-≡  {σ = σ} {A , t} {pu} i (γ , x) = σ γ , transportRefl x (~ i)
  stdModelUnivPi : UnivPi stdModel stdModelUniv stdModelPi
  stdModelUnivPi .UnivPi.π     (A , a) pa Bb@(B , b) pb = (λ _ → UU) , λ γ → pi
    (transport (λ i → pa i γ) (a γ)) (λ x → transport (λ i → pb i (γ , x)) (b (γ , x)))
  stdModelUnivPi .UnivPi.π[] {Δ} {Γ} {σ} (A , a) pa Bb pb = refl
  stdModelUnivPi .UnivPi.tyOfπ (A , a) pa b pb = refl
  stdModelUnivPi .UnivPi.Elπ   (A , a) pa b pb = refl

  stdModelUniv𝓑 : Univ𝓑 stdModel stdModelUniv stdModel𝓑
  stdModelUniv𝓑 .Univ𝓑.𝕓     = (λ _ → UU) , λ _ → bool
  stdModelUniv𝓑 .Univ𝓑.𝕓[] σ = refl
  stdModelUniv𝓑 .Univ𝓑.tyOf𝕓 = refl
  stdModelUniv𝓑 .Univ𝓑.El𝕓 γ = refl
