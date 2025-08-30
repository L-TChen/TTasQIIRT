open import Prelude
  hiding (Bool)

module Theory.SC+El+Pi+B.QIIRT-tyOf.Model where

open import Theory.SC.QIIRT-tyOf.Model
open import Theory.SC+Pi+B.QIIRT-tyOf.Model

module _ (𝒞 : SC ℓ₁ ℓ₂ ℓ₃ ℓ₄) where
  open SC 𝒞
  open Var

  record Univ : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
    field
      El
        : (u : Tm Γ) (p : tyOf u ≡ U)
        → Ty Γ
      El[]
        : (τ : Sub Γ Δ) (u : Tm Δ) (p : tyOf u ≡ U)
        → (El u p) [ τ ]T ≡ El (u [ τ ]t) (tyOf[]≡U p)

    opaque
      El[]₂
        : (u : Tm Δ) (pu : tyOf u ≡ U)
        → tyOf (π₂ {Γ ,C El (u [ σ ]t) (tyOf[]≡U pu)} idS)
        ≡ El u pu [ σ ∘ π₁ idS ]T
      El[]₂ {σ = σ} u pu = tyOfπ₂ idS ∙ (El[] (π₁ idS) (u [ σ ]t) (tyOf[]≡U pu) ∙ cong₂ El ([∘]t u (π₁ idS) σ) (tyOftyOf[]≡U pu)) ∙ sym (El[] (σ ∘ π₁ idS) u pu)

  record Univ𝓑 (𝒰 : Univ) (ℬ : 𝓑 𝒞) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
    open Univ 𝒰
    open 𝓑 ℬ

    field
      𝕓
        : Tm Γ
      𝕓[]
        : (σ : Sub Γ Δ)
        → 𝕓 [ σ ]t ≡ 𝕓
      tyOf𝕓
        : tyOf {Γ} 𝕓 ≡ U  -- tyOf {Γ} 𝕓 ≡ U
      El𝕓
        : (Γ : Ctx)
        → El {Γ} 𝕓 tyOf𝕓 ≡ 𝔹
  
  record UnivPi (𝒰 : Univ) (𝒫i : Pi 𝒞) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
    open Univ 𝒰
    open Pi   𝒫i

{-
    field
      El[]₂
        : (u : Tm Δ) (pu : tyOf u ≡ U)(pu' : tyOf (u [ σ ]t) ≡ U)
        → tyOf (π₂ {Γ ,C El (u [ σ ]t) pu'} idS)
        ≡ El u pu [ σ ∘ π₁ idS ]T
-}

    _↑El
      : (σ : Sub Γ Δ) {u : Tm Δ} {pu : tyOf u ≡ U}
      → Sub (Γ ,C El (u [ σ ]t) (tyOf[]≡U pu)) (Δ ,C El u pu)
    (σ ↑El) {u} {pu} = (σ ∘ π₁ idS) , π₂ idS ∶[ El[]₂ u pu ]

    field
      π
        : (a : Tm Γ) (pa : tyOf a ≡ U)
        → (b : Tm (Γ ,C El a pa)) (pb : tyOf b ≡ U)
        → Tm Γ
      π[]
        : {σ : Sub Δ Γ}
        → (a : Tm Γ) (pa : tyOf a ≡ U)
        → (b : Tm (Γ ,C El a pa)) (pb : tyOf b ≡ U)
{-
        → (pa' : tyOf (a [ σ ]t) ≡ U)
        → (pb' : tyOf (b [ σ ↑El ]t) ≡ U)
-}
        → (π a pa b pb) [ σ ]t ≡ π (a [ σ ]t) (tyOf[]≡U pa) (b [ σ ↑El ]t) (tyOf[]≡U pb)
      tyOfπ
        : (a : Tm Γ) (pa : tyOf a ≡ U) (b : Tm (Γ ,C El a pa)) (pb : tyOf b ≡ U)
        → tyOf (π a pa b pb) ≡ U
      Elπ
        : (a : Tm Γ) (pa : tyOf a ≡ U)
        → (b : Tm (Γ ,C El a pa)) (pb : tyOf b ≡ U)
        → El (π a pa b pb) (tyOfπ a pa b pb) ≡ Π (El a pa) (El b pb)

record SC+El+Pi+B (ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level)
  : Set ((ℓ-suc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄))) where

  field
    𝒞  : SC ℓ₁ ℓ₂ ℓ₃ ℓ₄
    𝒰  : Univ 𝒞
    𝒫i : Pi 𝒞
    ℬ  : 𝓑 𝒞
    𝒰𝒫i : UnivPi 𝒞 𝒰 𝒫i
    𝒰ℬ  : Univ𝓑 𝒞 𝒰 ℬ

  open SC 𝒞    public
  open Univ 𝒰  public
  open Pi 𝒫i   public
  open 𝓑 ℬ  public
  open UnivPi   𝒰𝒫i public 
  open Univ𝓑 𝒰ℬ  public

  open Var
