open import Prelude

module Theory.SC+Pi+B.QIIRT-tyOf.Model where

open import Theory.SC.QIIRT-tyOf.Model

module _ (𝒞 : SC ℓ₁ ℓ₂ ℓ₃ ℓ₄) where
  open SC 𝒞
  open Var

  record Pi : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
    field
      Π
        : (A : Ty Γ) (B : Ty (Γ  ,C A ))
        → Ty Γ
      app
        : (t : Tm Γ) (B : Ty (Γ ,C A)) (pt : tyOf t ≡ Π A B)
        → Tm (Γ  ,C A)
      tyOfapp
        : (p : tyOf t ≡ Π A B)
        → tyOf (app t B p) ≡ B
      abs
        : (t : Tm (Γ  ,C A ))
        → Tm Γ 
      tyOfabs
        : tyOf (abs t) ≡ Π A  (tyOf t)
      Π[]
        : (σ : Sub Γ Δ) (B : Ty (Δ ,C A))
        → (Π A B) [ σ ]T ≡ Π (A [ σ ]T) (B [ σ ↑ A ]T)
      abs[]
        : (σ : Sub Γ Δ) (t : Tm (Δ ,C A))
        → abs t [ σ ]t ≡ abs (t [ σ ↑ A  ]t)
      Πβ
        : (t : Tm (Γ ,C A)) (pt : tyOf (abs t) ≡ Π A (tyOf t))
        → app (abs t) _ pt ≡ t
      Πη
        : (t : Tm Γ ) (p : tyOf t ≡ Π A B)
        → abs (app t B p) ≡ t

  record 𝓑 : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
    field
      𝔹
        : Ty Γ
      𝔹[]
        : (σ : Sub Γ Δ)
        → 𝔹 [ σ ]T ≡ 𝔹
      tt ff
        : Tm Γ 
      tyOftt
        : tyOf {Γ} tt ≡ 𝔹 [ idS ]T
      tyOfff
        : tyOf {Γ} ff ≡ 𝔹 [ idS ]T
      tt[]
        : (σ : Sub Γ Δ)
        → tt [ σ ]t  ≡ tt 
      ff[]
        : (σ : Sub Γ Δ)
        → ff [ σ ]t  ≡ ff

    𝔹[]₂
      : tyOf (π₂ {Γ ,C 𝔹} idS ) ≡ 𝔹 [ τ ]T
    𝔹[]₂ {Γ = Γ} {τ = τ} =
      tyOf (π₂ {Γ ,C 𝔹} idS )
        ≡⟨ tyOfπ₂ idS ⟩
      𝔹 [ π₁ idS ]T
        ≡⟨ 𝔹[] _ ⟩
      𝔹
        ≡⟨ sym (𝔹[] _) ⟩
      𝔹 [ τ ]T
        ∎

    _↑𝔹
      : (σ : Sub Γ Δ)
      → Sub (Γ ,C 𝔹) (Δ ,C 𝔹)
    σ ↑𝔹 = (σ ∘ π₁ idS) , π₂ idS ∶[ 𝔹[]₂ {τ = σ ∘ π₁ idS} ]

    field
      elim𝔹
        : (P : Ty (Γ ,C 𝔹))
        → (t : Tm Γ) (pt : tyOf t ≡ P [ idS , tt ∶[ tyOftt ] ]T)
        → (u : Tm Γ) (pu : tyOf u ≡ P [ idS , ff ∶[ tyOfff ] ]T)
        → (b : Tm Γ) (pb : tyOf b ≡ 𝔹 [ idS ]T)
        → Tm Γ
      tyOfelim𝔹
        : (P : Ty (Γ ,C 𝔹)) 
        → (t : Tm Γ) (pt : tyOf t ≡ P [ idS , tt ∶[ tyOftt ] ]T)
        → (u : Tm Γ) (pu : tyOf u ≡ P [ idS , ff ∶[ tyOfff ] ]T)
        → (b : Tm Γ) (pb : tyOf b ≡ 𝔹 [ idS ]T)
        → tyOf (elim𝔹 P t pt u pu b pb) ≡ (P [ idS , b ∶[ pb ] ]T)
      elim𝔹[]
        : (P : Ty (Γ ,C 𝔹))
          (t : Tm Γ) (pt : tyOf t ≡ P [ idS , tt ∶[ tyOftt ] ]T)
          (u : Tm Γ) (pu : tyOf u ≡ P [ idS , ff ∶[ tyOfff ] ]T)
          (b : Tm Γ) (pb : tyOf b ≡ 𝔹 [ idS ]T)
        → (pt₂ : tyOf (t [ σ ]t) ≡ P [ σ ↑𝔹 ]T [ idS , tt ∶[ tyOftt ] ]T)
        → (pu₂ : tyOf (u [ σ ]t) ≡ P [ σ ↑𝔹 ]T [ idS , ff ∶[ tyOfff ] ]T)
        → (pb₂ : tyOf (b [ σ ]t) ≡ 𝔹 [ idS ]T)
        → (p : (P [ idS , b ∶[ pb ] ]T [ σ ]T) ≡ (P [ (σ ∘ π₁ idS) , π₂ idS ∶[ 𝔹[]₂ ] ]T [ idS , b [ σ ]t ∶[ pb₂ ] ]T))
        → (elim𝔹 P t pt u pu b pb) [ σ ]t
        ≡ elim𝔹 (P [ σ ↑𝔹 ]T) (t [ σ ]t) pt₂ (u [ σ ]t) pu₂ (b [ σ ]t) pb₂

record SC+Pi+B (ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level)
  : Set ((ℓ-suc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄))) where

  field
    𝒞  : SC ℓ₁ ℓ₂ ℓ₃ ℓ₄
    𝒫i : Pi 𝒞
    ℬ  : 𝓑 𝒞

  open SC 𝒞    public
  open Pi 𝒫i   public
  open 𝓑 ℬ  public

  open Var
