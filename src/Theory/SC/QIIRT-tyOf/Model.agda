open import Prelude

module Theory.SC.QIIRT-tyOf.Model where

record Motive (ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level) : Set (ℓ-suc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)) where
  field
    Ctxᴬ  : Set ℓ₁
    Tyᴬ   : Ctxᴬ → Set ℓ₂
    Subᴬ  : Ctxᴬ → Ctxᴬ → Set ℓ₃
    Tmᴬ   : Ctxᴬ → Set ℓ₄
    tyOfᴬ : {Γᴹ : Ctxᴬ} → Tmᴬ Γᴹ → Tyᴬ Γᴹ

    Tyᴬ-is-set : {Γᴹ : Ctxᴬ} → isSet (Tyᴬ Γᴹ)

  variable
    Γᴹ Δᴹ Θᴹ Ξᴹ : Ctxᴬ
    Aᴹ Bᴹ Cᴹ Dᴹ : Tyᴬ Γᴹ
    σᴹ τᴹ γᴹ    : Subᴬ Γᴹ Δᴹ
    tᴹ uᴹ vᴹ    : Tmᴬ Γᴹ

module _ (mot : Motive ℓ₁ ℓ₂ ℓ₃ ℓ₄) where
  open Motive mot

  record SCᴹ : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
    field
      ∅ᴹ
        : Ctxᴬ
      _,ᴹ_
        : (Γᴹ : Ctxᴬ)(Aᴹ : Tyᴬ Γᴹ)
        → Ctxᴬ
      _[_]Tᴹ
        : (Aᴹ : Tyᴬ Δᴹ)(σᴹ : Subᴬ Γᴹ Δᴹ)
        → Tyᴬ Γᴹ
      _[_]tᴹ
        : (tᴹ : Tmᴬ Δᴹ)(σᴹ : Subᴬ Γᴹ Δᴹ)
        → Tmᴬ Γᴹ
      tyOf[]ᴹ
        : tyOfᴬ (tᴹ [ σᴹ ]tᴹ) ≡ (tyOfᴬ tᴹ) [ σᴹ ]Tᴹ
      ∅Sᴹ
        : Subᴬ Γᴹ ∅ᴹ
      _,ᴹ_∶[_]
        : (σᴹ : Subᴬ Γᴹ Δᴹ) (tᴹ : Tmᴬ Γᴹ) → tyOfᴬ tᴹ ≡ Aᴹ [ σᴹ ]Tᴹ
        → Subᴬ Γᴹ (Δᴹ ,ᴹ Aᴹ)
      idSᴹ
        : Subᴬ Γᴹ Γᴹ
      _∘ᴹ_
        : Subᴬ Δᴹ Θᴹ → Subᴬ Γᴹ Δᴹ
        → Subᴬ Γᴹ Θᴹ
      π₁ᴹ
        : Subᴬ Γᴹ (Δᴹ ,ᴹ Aᴹ)
        → Subᴬ Γᴹ Δᴹ
      π₂ᴹ
        : Subᴬ Γᴹ (Δᴹ ,ᴹ Aᴹ)
        → Tmᴬ Γᴹ
      tyOfπ₂ᴹ
        : (Aᴹ : Tyᴬ Δᴹ) (σᴹ : Subᴬ Γᴹ (Δᴹ ,ᴹ Aᴹ))
        → tyOfᴬ (π₂ᴹ {Aᴹ = Aᴹ} σᴹ) ≡ Aᴹ [ π₁ᴹ σᴹ ]Tᴹ
      idS∘ᴹ_
        : (σᴹ : Subᴬ Γᴹ Δᴹ)
        → idSᴹ ∘ᴹ σᴹ ≡ σᴹ
      _∘idSᴹ
        : (σᴹ : Subᴬ Γᴹ Δᴹ)
        → σᴹ ∘ᴹ idSᴹ ≡ σᴹ
      assocSᴹ
        : (σᴹ : Subᴬ Γᴹ Δᴹ) (τᴹ : Subᴬ Δᴹ Θᴹ) (γᴹ : Subᴬ Θᴹ Ξᴹ)
        → (γᴹ ∘ᴹ τᴹ) ∘ᴹ σᴹ ≡ γᴹ ∘ᴹ (τᴹ ∘ᴹ σᴹ)
      [idS]Tᴹ
        : Aᴹ ≡ Aᴹ [ idSᴹ ]Tᴹ
      [∘]Tᴹ
        : (Aᴹ : Tyᴬ Θᴹ) (σᴹ : Subᴬ Γᴹ Δᴹ) (τᴹ : Subᴬ Δᴹ Θᴹ)
        → Aᴹ [ τᴹ ]Tᴹ [ σᴹ ]Tᴹ ≡ Aᴹ [ τᴹ ∘ᴹ σᴹ ]Tᴹ
      ,∘ᴹ
        : (σᴹ : Subᴬ Δᴹ Θᴹ) (tᴹ : Tmᴬ Δᴹ) (τᴹ : Subᴬ Γᴹ Δᴹ)
        → (p : tyOfᴬ tᴹ ≡ Aᴹ [ σᴹ ]Tᴹ) (q : tyOfᴬ (tᴹ [ τᴹ ]tᴹ) ≡ Aᴹ [ σᴹ ∘ᴹ τᴹ ]Tᴹ)
--        → let q = tyOfᴬ (tᴹ [ τᴹ ]tᴹ)
--                    ≡⟨ tyOf[]ᴹ ⟩
--                  (tyOfᴬ tᴹ) [ τᴹ ]Tᴹ
--                    ≡[ i ]⟨ p i [ τᴹ ]Tᴹ ⟩
--                  Aᴹ [ σᴹ ]Tᴹ [ τᴹ ]Tᴹ
--                    ≡⟨ [∘]Tᴹ _ _ _ ⟩
--                  Aᴹ [ σᴹ ∘ᴹ τᴹ ]Tᴹ
--                    ∎
--        in
        → (σᴹ ,ᴹ tᴹ ∶[ p ]) ∘ᴹ τᴹ ≡ ((σᴹ ∘ᴹ τᴹ) ,ᴹ tᴹ [ τᴹ ]tᴹ ∶[ q ])
      ηπᴹ
        : (σᴹ : Subᴬ Γᴹ (Δᴹ ,ᴹ Aᴹ))
        → σᴹ ≡ (π₁ᴹ σᴹ ,ᴹ π₂ᴹ σᴹ ∶[ tyOfπ₂ᴹ _ _ ])
      η∅ᴹ
        : (σᴹ : Subᴬ Γᴹ ∅ᴹ)
        → σᴹ ≡ ∅Sᴹ
      βπ₁ᴹ
        : (σᴹ : Subᴬ Γᴹ Δᴹ) (tᴹ : Tmᴬ Γᴹ) (p : tyOfᴬ tᴹ ≡ Aᴹ [ σᴹ ]Tᴹ)
        → π₁ᴹ (σᴹ ,ᴹ tᴹ ∶[ p ]) ≡ σᴹ
      βπ₂ᴹ
        : (σᴹ : Subᴬ Γᴹ Δᴹ) (tᴹ : Tmᴬ Γᴹ) (p : tyOfᴬ tᴹ ≡ Aᴹ [ σᴹ ]Tᴹ)
--        → (q : Aᴹ [ π₁ᴹ (σᴹ ,ᴹ tᴹ ∶[ p ]) ]Tᴹ ≡  tyOfᴬ tᴹ)
        → π₂ᴹ (σᴹ ,ᴹ tᴹ ∶[ p ]) ≡ tᴹ
      [idS]tᴹ
        : (tᴹ : Tmᴬ Γᴹ)
        → tᴹ ≡ tᴹ [ idSᴹ ]tᴹ
      [∘]tᴹ
        : (tᴹ : Tmᴬ Θᴹ) (σᴹ : Subᴬ Γᴹ Δᴹ) (τᴹ : Subᴬ Δᴹ Θᴹ)
        → tᴹ [ τᴹ ]tᴹ [ σᴹ ]tᴹ ≡ tᴹ [ τᴹ ∘ᴹ σᴹ ]tᴹ
      Uᴹ
        : Tyᴬ Γᴹ
      U[]ᴹ
        : Uᴹ [ σᴹ ]Tᴹ ≡ Uᴹ
