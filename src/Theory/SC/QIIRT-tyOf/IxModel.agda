module Theory.SC.QIIRT-tyOf.IxModel where

open import Prelude

open import Theory.SC.QIIRT-tyOf.Syntax

record Motive (ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level) : Set (ℓ-suc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)) where
  field
    Ctxᴬ
      : (Γ : Ctx)
      → Set ℓ₁
    Tyᴬ
      : Ctxᴬ Γ → Ty Γ
      → Set ℓ₂
    Subᴬ
      : (Γᴹ : Ctxᴬ Γ) (Δᴹ : Ctxᴬ Δ) → Sub Γ Δ
      → Set ℓ₃
    Tmᴬ
      : Ctxᴬ Γ → Tm Γ
      → Set ℓ₄
    tyOfᴬ
      : {Γᴹ : Ctxᴬ Γ} → Tmᴬ Γᴹ t
      → Tyᴬ Γᴹ (tyOf t)

  variable
    Γᴹ Δᴹ Θᴹ Ξᴹ : Ctxᴬ Γ
    Aᴹ Bᴹ Cᴹ Dᴹ : Tyᴬ  Γᴹ A
    σᴹ τᴹ γᴹ    : Subᴬ Γᴹ Δᴹ σ
    tᴹ uᴹ vᴹ    : Tmᴬ  Γᴹ t

module _ (mot : Motive ℓ₁ ℓ₂ ℓ₃ ℓ₄) where
  open Motive mot

  record SCᴹ : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
    field
      ∅ᴹ
        : Ctxᴬ ∅
      _,ᴹ_
        : (Γᴹ : Ctxᴬ Γ)(Aᴹ : Tyᴬ Γᴹ A)
        → Ctxᴬ (Γ , A)
      _[_]Tᴹ
        : (Aᴹ : Tyᴬ Δᴹ A)(σᴹ : Subᴬ Γᴹ Δᴹ σ)
        → Tyᴬ Γᴹ (A [ σ ])
      _[_]tᴹ
        : (tᴹ : Tmᴬ Δᴹ t)(σᴹ : Subᴬ Γᴹ Δᴹ σ)
        → Tmᴬ Γᴹ (t [ σ ])
      tyOf[]ᴹ
        : tyOfᴬ (tᴹ [ σᴹ ]tᴹ) ≡ (tyOfᴬ tᴹ) [ σᴹ ]Tᴹ
      ∅Sᴹ
        : Subᴬ Γᴹ ∅ᴹ ∅
      _,ᴹ_∶[_,_]
        : (σᴹ : Subᴬ Γᴹ Δᴹ σ) {Aᴹ : Tyᴬ Δᴹ A} (tᴹ : Tmᴬ Γᴹ t)
        → (p : tyOf t ≡ A [ σ ])
        → tyOfᴬ tᴹ ≡[ i ⊢ Tyᴬ Γᴹ (p i) ] (Aᴹ [ σᴹ ]Tᴹ)
        → Subᴬ Γᴹ (Δᴹ ,ᴹ Aᴹ) (σ , t ∶[ p ])
      idSᴹ
        : Subᴬ Γᴹ Γᴹ idS
      _∘ᴹ_
        : Subᴬ Δᴹ Θᴹ τ → Subᴬ Γᴹ Δᴹ σ
        → Subᴬ Γᴹ Θᴹ (τ ∘ σ)
      π₁ᴹ
        : Subᴬ Γᴹ (Δᴹ ,ᴹ Aᴹ) σ
        → Subᴬ Γᴹ Δᴹ (π₁ σ)
      π₂ᴹ
        : Subᴬ Γᴹ (Δᴹ ,ᴹ Aᴹ) σ
        → Tmᴬ Γᴹ (π₂ σ)
      tyOfπ₂ᴹ
        : tyOfᴬ (π₂ᴹ σᴹ) ≡ Aᴹ [ π₁ᴹ σᴹ ]Tᴹ
      idS∘ᴹ_
        : (σᴹ : Subᴬ Γᴹ Δᴹ σ)
        → idSᴹ ∘ᴹ σᴹ
        ≡[ i ⊢ Subᴬ Γᴹ Δᴹ ((idS∘ σ) i) ] σᴹ
        -- [TODO] Justify the usage of transport in the eliminator
      _∘idSᴹ
        : (σᴹ : Subᴬ Γᴹ Δᴹ σ)
        → σᴹ ∘ᴹ idSᴹ
        ≡[ i ⊢ Subᴬ Γᴹ Δᴹ ((σ ∘idS) i) ] σᴹ
      assocSᴹ
        : (σᴹ : Subᴬ Γᴹ Δᴹ σ) (τᴹ : Subᴬ Δᴹ Θᴹ τ) (γᴹ : Subᴬ Θᴹ Ξᴹ γ)
        → (γᴹ ∘ᴹ τᴹ) ∘ᴹ σᴹ
        ≡[ i ⊢ Subᴬ Γᴹ Ξᴹ (assocS σ τ γ i) ]
           γᴹ ∘ᴹ (τᴹ ∘ᴹ σᴹ)
      ,∘ᴹ
        : (σᴹ : Subᴬ Δᴹ Θᴹ σ) (tᴹ : Tmᴬ Δᴹ t) (τᴹ : Subᴬ Γᴹ Δᴹ τ)
          (p : tyOf t ≡ A [ σ ]) (pᴹ : tyOfᴬ tᴹ ≡[ i ⊢ Tyᴬ Δᴹ (p i) ] Aᴹ [ σᴹ ]Tᴹ)
          (q : tyOf (t [ τ ]) ≡ A [ σ ∘ τ ]) (qᴹ : tyOfᴬ (tᴹ [ τᴹ ]tᴹ) ≡[ i ⊢ Tyᴬ Γᴹ (q i) ] (Aᴹ [ σᴹ ∘ᴹ τᴹ ]Tᴹ))
        → (σᴹ ,ᴹ tᴹ ∶[ p , pᴹ ]) ∘ᴹ τᴹ
        ≡[ i ⊢ Subᴬ Γᴹ (Θᴹ ,ᴹ Aᴹ) (,∘ σ t τ p q i) ]
          ((σᴹ ∘ᴹ τᴹ) ,ᴹ tᴹ [ τᴹ ]tᴹ ∶[ q , qᴹ ])
      ηπᴹ
        : (σᴹ : Subᴬ Γᴹ (Δᴹ ,ᴹ Aᴹ) σ)
        → σᴹ
        ≡[ i ⊢ Subᴬ Γᴹ (Δᴹ ,ᴹ Aᴹ) (ηπ σ i) ]
          (π₁ᴹ σᴹ ,ᴹ π₂ᴹ σᴹ ∶[ refl , tyOfπ₂ᴹ ])
      η∅ᴹ
        : (σᴹ : Subᴬ Γᴹ ∅ᴹ σ)
        → σᴹ ≡[ i ⊢ Subᴬ Γᴹ ∅ᴹ (η∅ σ i) ] ∅Sᴹ
      βπ₁ᴹ
        : (σᴹ : Subᴬ Γᴹ Δᴹ σ) (tᴹ : Tmᴬ Γᴹ t)
        → (p : tyOf t ≡ A [ σ ]) (pᴹ : tyOfᴬ tᴹ ≡[ i ⊢ Tyᴬ Γᴹ (p i) ] Aᴹ [ σᴹ ]Tᴹ)
        → π₁ᴹ (σᴹ ,ᴹ tᴹ ∶[ p , pᴹ ])
        ≡[ i ⊢ Subᴬ Γᴹ Δᴹ (βπ₁ σ t p i) ]
          σᴹ
      βπ₂ᴹ
        : (σᴹ : Subᴬ Γᴹ Δᴹ σ) (tᴹ : Tmᴬ Γᴹ t)
        → (p : tyOf t ≡ A [ σ ]) (pᴹ : tyOfᴬ tᴹ ≡[ i ⊢ Tyᴬ Γᴹ (p i) ] Aᴹ [ σᴹ ]Tᴹ)
        → (q : A [ π₁ (σ , t ∶[ p ]) ] ≡ tyOf t)
          (qᴹ : Aᴹ [ π₁ᴹ (σᴹ ,ᴹ tᴹ ∶[ p , pᴹ ]) ]Tᴹ ≡[ i ⊢ Tyᴬ Γᴹ (q i) ] tyOfᴬ tᴹ)
        → π₂ᴹ (σᴹ ,ᴹ tᴹ ∶[ p , pᴹ ])
        ≡[ i ⊢ Tmᴬ Γᴹ (βπ₂ σ t p q i) ]
          tᴹ
      [idS]Tᴹ
        : (Aᴹ : Tyᴬ Γᴹ A)
        → Aᴹ
        ≡[ i ⊢ Tyᴬ Γᴹ ([idS]T {Γ} {A} i) ]
          Aᴹ [ idSᴹ ]Tᴹ
      [∘]Tᴹ
        : (Aᴹ : Tyᴬ Θᴹ A) (σᴹ : Subᴬ Γᴹ Δᴹ σ) (τᴹ : Subᴬ Δᴹ Θᴹ τ)
        → Aᴹ [ τᴹ ]Tᴹ [ σᴹ ]Tᴹ
        ≡[ i ⊢ Tyᴬ Γᴹ ([∘]T A σ τ i) ]
          Aᴹ [ τᴹ ∘ᴹ σᴹ ]Tᴹ
      [idS]tᴹ
        : (tᴹ : Tmᴬ Γᴹ t)
        → tᴹ
        ≡[ i ⊢ Tmᴬ Γᴹ ([idS]t t i) ]
          tᴹ [ idSᴹ ]tᴹ
      [∘]tᴹ
        : (tᴹ : Tmᴬ Θᴹ t) (σᴹ : Subᴬ Γᴹ Δᴹ σ) (τᴹ : Subᴬ Δᴹ Θᴹ τ)
        → tᴹ [ τᴹ ]tᴹ [ σᴹ ]tᴹ
        ≡[ i ⊢ Tmᴬ Γᴹ ([∘]t t σ τ i) ]
          tᴹ [ τᴹ ∘ᴹ σᴹ ]tᴹ
      Uᴹ
        : Tyᴬ Γᴹ A
      U[]ᴹ
        : {Γᴹ : Ctxᴬ Γ} {Δᴹ : Ctxᴬ Δ} {σᴹ : Subᴬ Γᴹ Δᴹ σ}
        → Uᴹ [ σᴹ ]Tᴹ
        ≡[ i ⊢ Tyᴬ Γᴹ (U[] {σ = σ} i) ]
          Uᴹ
