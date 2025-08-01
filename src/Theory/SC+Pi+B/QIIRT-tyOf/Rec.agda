module Theory.SC+Pi+B.QIIRT-tyOf.Rec where

open import Prelude

open import Theory.SC+Pi+B.QIIRT-tyOf.Syntax

record Motive (ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level) : Set (ℓ-suc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)) where
  field
    Ctxᴬ : Set ℓ₁
    Tyᴬ : Ctxᴬ → Set ℓ₂
    Subᴬ : Ctxᴬ → Ctxᴬ → Set ℓ₃
    Tmᴬ : Ctxᴬ → Set ℓ₄
    tyOfᴬ : {Γᴹ : Ctxᴬ} → Tmᴬ Γᴹ → Tyᴬ Γᴹ

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
        : tyOfᴬ (π₂ᴹ σᴹ) ≡ Aᴹ [ π₁ᴹ σᴹ ]Tᴹ
      idS∘ᴹ_
        : (σᴹ : Subᴬ Γᴹ Δᴹ)
        → idSᴹ ∘ᴹ σᴹ ≡ σᴹ
      _∘idSᴹ
        : (σᴹ : Subᴬ Γᴹ Δᴹ)
        → σᴹ ∘ᴹ idSᴹ ≡ σᴹ
      assocSᴹ
        : (σᴹ : Subᴬ Γᴹ Δᴹ) (τᴹ : Subᴬ Δᴹ Θᴹ) (γᴹ : Subᴬ Θᴹ Ξᴹ)
        → (γᴹ ∘ᴹ τᴹ) ∘ᴹ σᴹ ≡ γᴹ ∘ᴹ (τᴹ ∘ᴹ σᴹ)
      ,∘ᴹ
        : (σᴹ : Subᴬ Δᴹ Θᴹ) (tᴹ : Tmᴬ Δᴹ) (τᴹ : Subᴬ Γᴹ Δᴹ) (p : tyOfᴬ tᴹ ≡ Aᴹ [ σᴹ ]Tᴹ)
          (q : tyOfᴬ (tᴹ [ τᴹ ]tᴹ) ≡ Aᴹ [ σᴹ ∘ᴹ τᴹ ]Tᴹ)
        → (σᴹ ,ᴹ tᴹ ∶[ p ]) ∘ᴹ τᴹ ≡ ((σᴹ ∘ᴹ τᴹ) ,ᴹ tᴹ [ τᴹ ]tᴹ ∶[ q ])
      ηπᴹ
        : (σᴹ : Subᴬ Γᴹ (Δᴹ ,ᴹ Aᴹ))
        → σᴹ ≡ (π₁ᴹ σᴹ ,ᴹ π₂ᴹ σᴹ ∶[ tyOfπ₂ᴹ ])
      η∅ᴹ
        : (σᴹ : Subᴬ Γᴹ ∅ᴹ)
        → σᴹ ≡ ∅Sᴹ
      βπ₁ᴹ
        : (σᴹ : Subᴬ Γᴹ Δᴹ) (tᴹ : Tmᴬ Γᴹ) (p : tyOfᴬ tᴹ ≡ Aᴹ [ σᴹ ]Tᴹ)
        → π₁ᴹ (σᴹ ,ᴹ tᴹ ∶[ p ]) ≡ σᴹ
      βπ₂ᴹ
        : (σᴹ : Subᴬ Γᴹ Δᴹ) (tᴹ : Tmᴬ Γᴹ) (p : tyOfᴬ tᴹ ≡ Aᴹ [ σᴹ ]Tᴹ)
        → (q : Aᴹ [ π₁ᴹ (σᴹ ,ᴹ tᴹ ∶[ p ]) ]Tᴹ ≡  tyOfᴬ tᴹ)
        → π₂ᴹ (σᴹ ,ᴹ tᴹ ∶[ p ]) ≡ tᴹ
      [idS]Tᴹ
        : Aᴹ ≡ Aᴹ [ idSᴹ ]Tᴹ
      [∘]Tᴹ
        : (Aᴹ : Tyᴬ Θᴹ) (σᴹ : Subᴬ Γᴹ Δᴹ) (τᴹ : Subᴬ Δᴹ Θᴹ)
        → Aᴹ [ τᴹ ]Tᴹ [ σᴹ ]Tᴹ ≡ Aᴹ [ τᴹ ∘ᴹ σᴹ ]Tᴹ
      [idS]tᴹ
        : (tᴹ : Tmᴬ Γᴹ)
        → tᴹ ≡ tᴹ [ idSᴹ ]tᴹ
      [∘]tᴹ
        : (tᴹ : Tmᴬ Θᴹ) (σᴹ : Subᴬ Γᴹ Δᴹ) (τᴹ : Subᴬ Δᴹ Θᴹ)
        → tᴹ [ τᴹ ]tᴹ [ σᴹ ]tᴹ ≡ tᴹ [ τᴹ ∘ᴹ σᴹ ]tᴹ

    --  tyOfπ₂idSᴹ
    --    : tyOfᴬ (π₂ᴹ {Aᴹ = Aᴹ [ σᴹ ]Tᴹ} idSᴹ) ≡ Aᴹ [ σᴹ ∘ᴹ π₁ᴹ idSᴹ ]Tᴹ
    -- [TODO] Do we need derived equations in recursor/eliminator?
    -- Derived equations are used to make the definition strictly positivie, not an issue for records.
    -- So, delete this for now to see if need it in an recorsor

    tyOfπ₂idSᴹ
      : tyOfᴬ (π₂ᴹ idSᴹ) ≡ Aᴹ [ σᴹ ∘ᴹ π₁ᴹ idSᴹ ]Tᴹ
    tyOfπ₂idSᴹ {Aᴹ = Aᴹ} {σᴹ = σᴹ} = 
      tyOfᴬ (π₂ᴹ idSᴹ)
        ≡⟨ tyOfπ₂ᴹ ⟩
      (Aᴹ [ σᴹ ]Tᴹ) [ π₁ᴹ idSᴹ ]Tᴹ
        ≡⟨ [∘]Tᴹ _ _ _ ⟩
      Aᴹ [ σᴹ ∘ᴹ π₁ᴹ idSᴹ ]Tᴹ
        ∎

    _↑ᴹ_
      : (σᴹ : Subᴬ Γᴹ Δᴹ) (Aᴹ : Tyᴬ Δᴹ)
      → Subᴬ (Γᴹ ,ᴹ (Aᴹ [ σᴹ ]Tᴹ)) (Δᴹ ,ᴹ Aᴹ)
    σᴹ ↑ᴹ Aᴹ = (σᴹ ∘ᴹ π₁ᴹ idSᴹ) ,ᴹ π₂ᴹ idSᴹ ∶[ tyOfπ₂idSᴹ ]

  record Piᴹ (C : SCᴹ): Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
    open SCᴹ C

    field
      Πᴹ
        : (Aᴹ : Tyᴬ Γᴹ) (Bᴹ : Tyᴬ (Γᴹ  ,ᴹ Aᴹ ))
        → Tyᴬ Γᴹ
      appᴹ
        : (tᴹ : Tmᴬ Γᴹ) → tyOfᴬ tᴹ ≡ Πᴹ Aᴹ Bᴹ
        → Tmᴬ (Γᴹ  ,ᴹ Aᴹ)
      tyOfappᴹ
        : (p : _)
        → tyOfᴬ (appᴹ {Bᴹ = Bᴹ} tᴹ p) ≡ Bᴹ
      absᴹ
        : (tᴹ : Tmᴬ (Γᴹ  ,ᴹ Aᴹ ))
        → Tmᴬ Γᴹ 
      tyOfabsᴹ
        : tyOfᴬ (absᴹ tᴹ) ≡ Πᴹ Aᴹ  (tyOfᴬ tᴹ)
      Π[]ᴹ
        : (Πᴹ Aᴹ Bᴹ) [ σᴹ ]Tᴹ ≡ Πᴹ (Aᴹ [ σᴹ ]Tᴹ) (Bᴹ [ σᴹ ↑ᴹ Aᴹ  ]Tᴹ)
      abs[]ᴹ
        : (tᴹ : Tmᴬ (Γᴹ  ,ᴹ Aᴹ))
        → absᴹ tᴹ [ σᴹ ]tᴹ ≡ absᴹ (tᴹ [ σᴹ ↑ᴹ Aᴹ  ]tᴹ)
      Πβᴹ
        : (tᴹ : Tmᴬ (Γᴹ  ,ᴹ Aᴹ )) 
        → appᴹ (absᴹ tᴹ) tyOfabsᴹ ≡ tᴹ
      Πηᴹ
        : (tᴹ : Tmᴬ Γᴹ ) (p : tyOfᴬ tᴹ ≡ Πᴹ Aᴹ Bᴹ)
        → absᴹ (appᴹ tᴹ p) ≡ tᴹ

  record Boolᴹ (C : SCᴹ): Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
    open SCᴹ C
    field
      𝔹ᴹ
        : Tyᴬ Γᴹ
      𝔹[]ᴹ
        : 𝔹ᴹ [ σᴹ ]Tᴹ ≡ 𝔹ᴹ
      ttᴹ ffᴹ
        : Tmᴬ Γᴹ 
      tyOfttᴹ
        : tyOfᴬ {Γᴹ} ttᴹ ≡ 𝔹ᴹ [ idSᴹ ]Tᴹ
      tyOfffᴹ
        : tyOfᴬ {Γᴹ} ffᴹ ≡ 𝔹ᴹ [ idSᴹ ]Tᴹ
      tt[]ᴹ
        : ttᴹ [ σᴹ ]tᴹ  ≡ ttᴹ 
      ff[]ᴹ
        : ffᴹ [ σᴹ ]tᴹ  ≡ ffᴹ
      elim𝔹ᴹ
        : (P : Tyᴬ (Γᴹ ,ᴹ 𝔹ᴹ)) (tᴹ uᴹ : Tmᴬ Γᴹ)
        → tyOfᴬ tᴹ ≡ (P [ idSᴹ ,ᴹ ttᴹ ∶[ tyOfttᴹ ] ]Tᴹ)
        → tyOfᴬ uᴹ ≡ (P [ idSᴹ ,ᴹ ffᴹ ∶[ tyOfffᴹ ] ]Tᴹ)
        → (bᴹ : Tmᴬ Γᴹ) → tyOfᴬ bᴹ ≡ 𝔹ᴹ [ idSᴹ ]Tᴹ
        → Tmᴬ Γᴹ

    𝔹[]₂ᴹ
      : tyOfᴬ (π₂ᴹ {Γᴹ ,ᴹ 𝔹ᴹ} idSᴹ ) ≡ 𝔹ᴹ [ τᴹ ]Tᴹ
    𝔹[]₂ᴹ {Γᴹ = Γᴹ} {τᴹ = τᴹ} =
      tyOfᴬ (π₂ᴹ {Γᴹ ,ᴹ 𝔹ᴹ} idSᴹ )
        ≡⟨ tyOfπ₂ᴹ ⟩
      𝔹ᴹ [ π₁ᴹ idSᴹ ]Tᴹ
        ≡⟨ 𝔹[]ᴹ ⟩
      𝔹ᴹ
        ≡⟨ sym 𝔹[]ᴹ ⟩
      𝔹ᴹ [ τᴹ ]Tᴹ
        ∎

    _↑𝔹ᴹ
      : (σᴹ : Subᴬ Γᴹ Δᴹ)
      → Subᴬ (Γᴹ ,ᴹ 𝔹ᴹ) (Δᴹ ,ᴹ 𝔹ᴹ)
    σᴹ ↑𝔹ᴹ = (σᴹ ∘ᴹ π₁ᴹ idSᴹ) ,ᴹ π₂ᴹ idSᴹ ∶[ 𝔹[]₂ᴹ {τᴹ = σᴹ ∘ᴹ π₁ᴹ idSᴹ} ]

    -- open SCᴹ C
    -- field
    --   elim𝔹[]ᴹ
    --     : (P : Tyᴬ (Γᴹ ,ᴹ 𝔹ᴹ)) (tᴹ uᴹ : Tmᴬ Γᴹ) (pt : tyOfᴬ tᴹ ≡ _) (pu : tyOfᴬ uᴹ ≡ _) → (bᴹ : Tmᴬ Γᴹ) (pb : tyOfᴬ bᴹ ≡ 𝔹ᴹ [ idSᴹ ]Tᴹ)
    --     → (pt₂ : tyOfᴬ (tᴹ [ σᴹ ]tᴹ) ≡ P [ σᴹ ↑𝔹ᴹ ]Tᴹ [ idSᴹ ,ᴹ ttᴹ ∶[ tyOfttᴹ ] ]Tᴹ)
    --     → (pu₂ : tyOfᴬ (uᴹ [ σᴹ ]tᴹ) ≡ P [ σᴹ ↑𝔹ᴹ ]Tᴹ [ idSᴹ ,ᴹ ffᴹ ∶[ tyOfffᴹ ] ]Tᴹ)
    --     → (pb₂ : tyOfᴬ (bᴹ [ σᴹ ]tᴹ) ≡ 𝔹ᴹ [ idSᴹ ]Tᴹ)
    --     → (P [ idSᴹ ,ᴹ bᴹ ∶[ pb ] ]Tᴹ [ σᴹ ]Tᴹ) ≡ (P [ (σᴹ ∘ᴹ π₁ᴹ idSᴹ) ,ᴹ π₂ᴹ idSᴹ ∶[ 𝔹[]₂ᴹ ] ]Tᴹ [ idSᴹ ,ᴹ bᴹ [ σᴹ ]tᴹ ∶[ pb₂ ] ]Tᴹ)
    --     → (elim𝔹ᴹ P tᴹ uᴹ pt pu bᴹ pb) [ σᴹ ]tᴹ ≡ elim𝔹ᴹ (P [ σᴹ ↑𝔹ᴹ ]Tᴹ) (tᴹ [ σᴹ ]tᴹ) (uᴹ [ σᴹ ]tᴹ) pt₂ pu₂ (bᴹ [ σᴹ ]tᴹ) pb₂
