open import Prelude
  hiding (Bool)

module Theory.SC+El+Pi+B.QIIRT-tyOf.Model where

open import Theory.SC.QIIRT-tyOf.Model

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

  record Pi : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
    field
      Π
        : (A : Ty Γ) (B : Ty (Γ  ,C A ))
        → Ty Γ
      app
        : (t : Tm Γ) → tyOf t ≡ Π A B
        → Tm (Γ  ,C A)
      tyOfapp
        : (p : _)
        → tyOf (app {B = B} t p) ≡ B
      abs
        : (t : Tm (Γ  ,C A ))
        → Tm Γ 
      tyOfabs
        : tyOf (abs t) ≡ Π A  (tyOf t)
      Π[]
        : (Π A B) [ σ ]T ≡ Π (A [ σ ]T) (B [ σ ↑ A ]T)
      abs[]
        : (t : Tm (Γ  ,C A))
        → abs t [ σ ]t ≡ abs (t [ σ ↑ A  ]t)
      Πβ
        : (t : Tm (Γ ,C A)) 
        → app (abs t) tyOfabs ≡ t
      Πη
        : (t : Tm Γ ) (p : tyOf t ≡ Π A B)
        → abs (app t p) ≡ t

  record Bool : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
    field
      𝔹
        : Ty Γ
      𝔹[]
        : 𝔹 [ σ ]T ≡ 𝔹
      tt ff
        : Tm Γ 
      tyOftt
        : tyOf {Γ} tt ≡ 𝔹 [ idS ]T
      tyOfff
        : tyOf {Γ} ff ≡ 𝔹 [ idS ]T
      tt[]
        : tt [ σ ]t  ≡ tt 
      ff[]
        : ff [ σ ]t  ≡ ff

    𝔹[]₂
      : tyOf (π₂ {Γ ,C 𝔹} idS ) ≡ 𝔹 [ τ ]T
    𝔹[]₂ {Γ = Γ} {τ = τ} =
      tyOf (π₂ {Γ ,C 𝔹} idS )
        ≡⟨ tyOfπ₂ idS ⟩
      𝔹 [ π₁ idS ]T
        ≡⟨ 𝔹[] ⟩
      𝔹
        ≡⟨ sym 𝔹[] ⟩
      𝔹 [ τ ]T
        ∎

    _↑𝔹
      : (σ : Sub Γ Δ)
      → Sub (Γ ,C 𝔹) (Δ ,C 𝔹)
    σ ↑𝔹 = (σ ∘ π₁ idS) , π₂ idS ∶[ 𝔹[]₂ {τ = σ ∘ π₁ idS} ]

    field
      elim𝔹
        : (P : Ty (Γ ,C 𝔹)) (t u : Tm Γ)
        → tyOf t ≡ (P [ idS , tt ∶[ tyOftt ] ]T)
        → tyOf u ≡ (P [ idS , ff ∶[ tyOfff ] ]T)
        → (b : Tm Γ) → tyOf b ≡ 𝔹 [ idS ]T
        → Tm Γ
      elim𝔹[]
        : (P : Ty (Γ ,C 𝔹)) (t u : Tm Γ) (pt : tyOf t ≡ _) (pu : tyOf u ≡ _) → (b : Tm Γ) (pb : tyOf b ≡ 𝔹 [ idS ]T)
        → (pt₂ : tyOf (t [ σ ]t) ≡ P [ σ ↑𝔹 ]T [ idS , tt ∶[ tyOftt ] ]T)
        → (pu₂ : tyOf (u [ σ ]t) ≡ P [ σ ↑𝔹 ]T [ idS , ff ∶[ tyOfff ] ]T)
        → (pb₂ : tyOf (b [ σ ]t) ≡ 𝔹 [ idS ]T)
        → (P [ idS , b ∶[ pb ] ]T [ σ ]T) ≡ (P [ (σ ∘ π₁ idS) , π₂ idS ∶[ 𝔹[]₂ ] ]T [ idS , b [ σ ]t ∶[ pb₂ ] ]T)
        → (elim𝔹 P t u pt pu b pb) [ σ ]t
        ≡ elim𝔹 (P [ σ ↑𝔹 ]T) (t [ σ ]t) (u [ σ ]t) pt₂ pu₂ (b [ σ ]t) pb₂

  record UnivBool (𝒰 : Univ) (ℬ : Bool) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
    open Univ 𝒰
    open Bool ℬ

    field
      𝕓
        : Tm Γ
      𝕓[]
        : 𝕓 [ σ ]t ≡ 𝕓
      tyOf𝕓
        : tyOf {Γ} 𝕓 ≡ U  -- tyOf {Γ} 𝕓 ≡ U
      El𝕓
        : El {Γ} 𝕓 tyOf𝕓 ≡ 𝔹
  
  record UnivPi (𝒰 : Univ) (𝒫i : Pi) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
    open Univ 𝒰
    open Pi   𝒫i

    field
      El[]₂
        : (u : Tm Δ) (pu : tyOf u ≡ U)(pu' : tyOf (u [ σ ]t) ≡ U)
        → tyOf (π₂ {Γ ,C El (u [ σ ]t) pu'} idS)
        ≡ El u pu [ σ ∘ π₁ idS ]T

    _↑El
      : (σ : Sub Γ Δ) {u : Tm Δ} {pu : tyOf u ≡ U} {pu' : tyOf (u [ σ ]t) ≡ U}
      → Sub (Γ ,C El (u [ σ ]t) pu') (Δ ,C El u pu)
    (σ ↑El) {u} {pu} {pu'} = (σ ∘ π₁ idS) , π₂ idS ∶[ El[]₂ u pu pu' ]

    field
      π
        : (a : Tm Γ) (pa : tyOf a ≡ U)
        → (b : Tm (Γ ,C El a pa)) (pb : tyOf b ≡ U)
        → Tm Γ
      π[]
        : (a : Tm Γ) (pa : tyOf a ≡ U)
        → (b : Tm (Γ ,C El a pa)) (pb : tyOf b ≡ U)
        → (pa' : tyOf (a [ σ ]t) ≡ U)
        → (pb' : tyOf (b [ σ ↑El ]t) ≡ U)
        → (π a pa b pb) [ σ ]t ≡ π (a [ σ ]t) pa' (b [ σ ↑El ]t) pb'
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
    ℬ  : Bool 𝒞
    𝒰𝒫i : UnivPi 𝒞 𝒰 𝒫i
    𝒰ℬ  : UnivBool 𝒞 𝒰 ℬ

  open SC 𝒞    public
  open Univ 𝒰  public
  open Pi 𝒫i   public
  open Bool ℬ  public
  open UnivPi   𝒰𝒫i public 
  open UnivBool 𝒰ℬ  public

  open Var
