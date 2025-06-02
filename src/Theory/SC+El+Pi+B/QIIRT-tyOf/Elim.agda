module Theory.SC+El+Pi+B.QIIRT-tyOf.Elim where

open import Prelude

open import Theory.SC+El+Pi+B.QIIRT-tyOf.Syntax

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

-- Recursor

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
        → tyOfᴬ tᴹ ≡ {!Aᴹ [ σᴹ ]Tᴹ!} -- Aᴹ [ σᴹ ]Tᴹ
        → Subᴬ Γᴹ (Δᴹ ,ᴹ Aᴹ) (σ , t ∶[ {!p!} ])
--       idSᴹ
--         : Subᴬ Γᴹ Γᴹ
--       _∘ᴹ_
--         : Subᴬ Δᴹ Θᴹ → Subᴬ Γᴹ Δᴹ
--         → Subᴬ Γᴹ Θᴹ
--       π₁ᴹ
--         : Subᴬ Γᴹ (Δᴹ ,ᴹ Aᴹ)
--         → Subᴬ Γᴹ Δᴹ
--       π₂ᴹ
--         : Subᴬ Γᴹ (Δᴹ ,ᴹ Aᴹ)
--         → Tmᴬ Γᴹ
--       tyOfπ₂ᴹ
--         : tyOfᴬ (π₂ᴹ σᴹ) ≡ Aᴹ [ π₁ᴹ σᴹ ]Tᴹ
--       idS∘ᴹ_
--         : (σᴹ : Subᴬ Γᴹ Δᴹ)
--         → idSᴹ ∘ᴹ σᴹ ≡ σᴹ
--       _∘idSᴹ
--         : (σᴹ : Subᴬ Γᴹ Δᴹ)
--         → σᴹ ∘ᴹ idSᴹ ≡ σᴹ
--       assocSᴹ
--         : (σᴹ : Subᴬ Γᴹ Δᴹ) (τᴹ : Subᴬ Δᴹ Θᴹ) (γᴹ : Subᴬ Θᴹ Ξᴹ)
--         → (γᴹ ∘ᴹ τᴹ) ∘ᴹ σᴹ ≡ γᴹ ∘ᴹ (τᴹ ∘ᴹ σᴹ)
--       ,∘ᴹ
--         : (σᴹ : Subᴬ Δᴹ Θᴹ) (tᴹ : Tmᴬ Δᴹ) (τᴹ : Subᴬ Γᴹ Δᴹ) (p : tyOfᴬ tᴹ ≡ Aᴹ [ σᴹ ]Tᴹ)
--           (q : tyOfᴬ (tᴹ [ τᴹ ]tᴹ) ≡ Aᴹ [ σᴹ ∘ᴹ τᴹ ]Tᴹ)
--         → (σᴹ ,ᴹ tᴹ ∶[ p ]) ∘ᴹ τᴹ ≡ ((σᴹ ∘ᴹ τᴹ) ,ᴹ tᴹ [ τᴹ ]tᴹ ∶[ q ])
--       ηπᴹ
--         : (σᴹ : Subᴬ Γᴹ (Δᴹ ,ᴹ Aᴹ))
--         → σᴹ ≡ (π₁ᴹ σᴹ ,ᴹ π₂ᴹ σᴹ ∶[ tyOfπ₂ᴹ ])
--       η∅ᴹ
--         : (σᴹ : Subᴬ Γᴹ ∅ᴹ)
--         → σᴹ ≡ ∅Sᴹ
--       βπ₁ᴹ
--         : (σᴹ : Subᴬ Γᴹ Δᴹ) (tᴹ : Tmᴬ Γᴹ) (p : tyOfᴬ tᴹ ≡ Aᴹ [ σᴹ ]Tᴹ)
--         → π₁ᴹ (σᴹ ,ᴹ tᴹ ∶[ p ]) ≡ σᴹ
--       βπ₂ᴹ
--         : (σᴹ : Subᴬ Γᴹ Δᴹ) (tᴹ : Tmᴬ Γᴹ) (p : tyOfᴬ tᴹ ≡ Aᴹ [ σᴹ ]Tᴹ)
--         → (q : Aᴹ [ π₁ᴹ (σᴹ ,ᴹ tᴹ ∶[ p ]) ]Tᴹ ≡  tyOfᴬ tᴹ)
--         → π₂ᴹ (σᴹ ,ᴹ tᴹ ∶[ p ]) ≡ tᴹ
--       [idS]Tᴹ
--         : Aᴹ ≡ Aᴹ [ idSᴹ ]Tᴹ
--       [∘]Tᴹ
--         : (Aᴹ : Tyᴬ Θᴹ) (σᴹ : Subᴬ Γᴹ Δᴹ) (τᴹ : Subᴬ Δᴹ Θᴹ)
--         → Aᴹ [ τᴹ ]Tᴹ [ σᴹ ]Tᴹ ≡ Aᴹ [ τᴹ ∘ᴹ σᴹ ]Tᴹ
--       [idS]tᴹ
--         : (tᴹ : Tmᴬ Γᴹ)
--         → tᴹ ≡ tᴹ [ idSᴹ ]tᴹ
--       [∘]tᴹ
--         : (tᴹ : Tmᴬ Θᴹ) (σᴹ : Subᴬ Γᴹ Δᴹ) (τᴹ : Subᴬ Δᴹ Θᴹ)
--         → tᴹ [ τᴹ ]tᴹ [ σᴹ ]tᴹ ≡ tᴹ [ τᴹ ∘ᴹ σᴹ ]tᴹ
--       Uᴹ
--         : Tyᴬ Γᴹ
--       U[]ᴹ
--         : Uᴹ [ σᴹ ]Tᴹ ≡ Uᴹ

--     --  tyOfπ₂idSᴹ
--     --    : tyOfᴬ (π₂ᴹ {Aᴹ = Aᴹ [ σᴹ ]Tᴹ} idSᴹ) ≡ Aᴹ [ σᴹ ∘ᴹ π₁ᴹ idSᴹ ]Tᴹ
--     -- [TODO] Do we need derived equations in recursor/eliminator?
--     -- Derived equations are used to make the definition strictly positivie, not an issue for records.
--     -- So, delete this for now to see if need it in an recorsor

--     tyOfπ₂idSᴹ
--       : tyOfᴬ (π₂ᴹ idSᴹ) ≡ Aᴹ [ σᴹ ∘ᴹ π₁ᴹ idSᴹ ]Tᴹ
--     tyOfπ₂idSᴹ {Aᴹ = Aᴹ} {σᴹ = σᴹ} = 
--       tyOfᴬ (π₂ᴹ idSᴹ)
--         ≡⟨ tyOfπ₂ᴹ ⟩
--       (Aᴹ [ σᴹ ]Tᴹ) [ π₁ᴹ idSᴹ ]Tᴹ
--         ≡⟨ [∘]Tᴹ _ _ _ ⟩
--       Aᴹ [ σᴹ ∘ᴹ π₁ᴹ idSᴹ ]Tᴹ
--         ∎

--     _↑ᴹ_
--       : (σᴹ : Subᴬ Γᴹ Δᴹ) (A : Tyᴬ Δᴹ)
--       → Subᴬ (Γᴹ ,ᴹ (Aᴹ [ σᴹ ]Tᴹ)) (Δᴹ ,ᴹ Aᴹ)
--     σᴹ ↑ᴹ Aᴹ = (σᴹ ∘ᴹ π₁ᴹ idSᴹ) ,ᴹ π₂ᴹ idSᴹ ∶[ tyOfπ₂idSᴹ ]

--   record Univᴹ (C : SCᴹ): Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
--     open SCᴹ C

--     tyOf[]≡Uᴹ
--       : (p : tyOfᴬ uᴹ ≡ Uᴹ)
--       → tyOfᴬ (uᴹ [ σᴹ ]tᴹ) ≡ Uᴹ
--     tyOf[]≡Uᴹ {σᴹ = σᴹ} p = tyOf[]ᴹ ∙ cong (λ A → A [ σᴹ ]Tᴹ) p ∙ U[]ᴹ {σᴹ = σᴹ}

--     field
--       Elᴹ
--         : (uᴹ : Tmᴬ Γᴹ) (p : tyOfᴬ uᴹ ≡ Uᴹ)
--         → Tyᴬ Γᴹ
--       El[]ᴹ
--         : (τᴹ : Subᴬ Γᴹ Δᴹ) (uᴹ : Tmᴬ Δᴹ) (p : tyOfᴬ uᴹ ≡ Uᴹ)
--         → (Elᴹ uᴹ p) [ τᴹ ]Tᴹ ≡ Elᴹ (uᴹ [ τᴹ ]tᴹ) (tyOf[]≡Uᴹ p)

--   record Piᴹ (C : SCᴹ): Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
--     open SCᴹ C

--     field
--       Πᴹ
--         : (Aᴹ : Tyᴬ Γᴹ) (Bᴹ : Tyᴬ (Γᴹ  ,ᴹ Aᴹ ))
--         → Tyᴬ Γᴹ
--       appᴹ
--         : (tᴹ : Tmᴬ Γᴹ) → tyOfᴬ tᴹ ≡ Πᴹ Aᴹ Bᴹ
--         → Tmᴬ (Γᴹ  ,ᴹ Aᴹ)
--       tyOfappᴹ
--         : (p : _)
--         → tyOfᴬ (appᴹ {Bᴹ = Bᴹ} tᴹ p) ≡ Bᴹ
--       absᴹ
--         : (tᴹ : Tmᴬ (Γᴹ  ,ᴹ Aᴹ ))
--         → Tmᴬ Γᴹ 
--       tyOfabsᴹ
--         : tyOfᴬ (absᴹ tᴹ) ≡ Πᴹ Aᴹ  (tyOfᴬ tᴹ)
--       Π[]ᴹ
--         : (Πᴹ Aᴹ Bᴹ) [ σᴹ ]Tᴹ ≡ Πᴹ (Aᴹ [ σᴹ ]Tᴹ) (Bᴹ [ σᴹ ↑ᴹ Aᴹ  ]Tᴹ)
--       abs[]ᴹ
--         : (tᴹ : Tmᴬ (Γᴹ  ,ᴹ Aᴹ))
--         → absᴹ tᴹ [ σᴹ ]tᴹ ≡ absᴹ (tᴹ [ σᴹ ↑ᴹ Aᴹ  ]tᴹ)
--       Πβᴹ
--         : (tᴹ : Tmᴬ (Γᴹ  ,ᴹ Aᴹ )) 
--         → appᴹ (absᴹ tᴹ) tyOfabsᴹ ≡ tᴹ
--       Πηᴹ
--         : (tᴹ : Tmᴬ Γᴹ ) (p : tyOfᴬ tᴹ ≡ Πᴹ Aᴹ Bᴹ)
--         → absᴹ (appᴹ tᴹ p) ≡ tᴹ

--   record Boolᴹ (C : SCᴹ): Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
--     open SCᴹ C

--     field
--       𝔹ᴹ
--         : Tyᴬ Γᴹ
--       𝔹[]ᴹ
--         : 𝔹ᴹ [ σᴹ ]Tᴹ ≡ 𝔹ᴹ
--       ttᴹ ffᴹ
--         : Tmᴬ Γᴹ 
--       tyOfttᴹ
--         : tyOfᴬ {Γᴹ} ttᴹ ≡ 𝔹ᴹ [ idSᴹ ]Tᴹ
--       tyOfffᴹ
--         : tyOfᴬ {Γᴹ} ffᴹ ≡ 𝔹ᴹ [ idSᴹ ]Tᴹ
--       tt[]ᴹ
--         : ttᴹ [ σᴹ ]tᴹ  ≡ ttᴹ 
--       ff[]ᴹ
--         : ffᴹ [ σᴹ ]tᴹ  ≡ ffᴹ

--     𝔹[]₂ᴹ
--       : tyOfᴬ (π₂ᴹ {Γᴹ ,ᴹ 𝔹ᴹ} idSᴹ ) ≡ 𝔹ᴹ [ τᴹ ]Tᴹ
--     𝔹[]₂ᴹ {Γᴹ = Γᴹ} {τᴹ = τᴹ} =
--       tyOfᴬ (π₂ᴹ {Γᴹ ,ᴹ 𝔹ᴹ} idSᴹ )
--         ≡⟨ tyOfπ₂ᴹ ⟩
--       𝔹ᴹ [ π₁ᴹ idSᴹ ]Tᴹ
--         ≡⟨ 𝔹[]ᴹ ⟩
--       𝔹ᴹ
--         ≡⟨ sym 𝔹[]ᴹ ⟩
--       𝔹ᴹ [ τᴹ ]Tᴹ
--         ∎

--     _↑𝔹ᴹ
--       : (σᴹ : Subᴬ Γᴹ Δᴹ)
--       → Subᴬ (Γᴹ ,ᴹ 𝔹ᴹ) (Δᴹ ,ᴹ 𝔹ᴹ)
--     σᴹ ↑𝔹ᴹ = (σᴹ ∘ᴹ π₁ᴹ idSᴹ) ,ᴹ π₂ᴹ idSᴹ ∶[ 𝔹[]₂ᴹ {τᴹ = σᴹ ∘ᴹ π₁ᴹ idSᴹ} ]

--     field
--       elim𝔹ᴹ
--         : (P : Tyᴬ (Γᴹ ,ᴹ 𝔹ᴹ)) (tᴹ uᴹ : Tmᴬ Γᴹ)
--         → tyOfᴬ tᴹ ≡ (P [ idSᴹ ,ᴹ ttᴹ ∶[ tyOfttᴹ ] ]Tᴹ)
--         → tyOfᴬ uᴹ ≡ (P [ idSᴹ ,ᴹ ffᴹ ∶[ tyOfffᴹ ] ]Tᴹ)
--         → (bᴹ : Tmᴬ Γᴹ) → tyOfᴬ bᴹ ≡ 𝔹ᴹ [ idSᴹ ]Tᴹ
--         → Tmᴬ Γᴹ
--       elim𝔹[]ᴹ
--         : (P : Tyᴬ (Γᴹ ,ᴹ 𝔹ᴹ)) (tᴹ uᴹ : Tmᴬ Γᴹ) (pt : tyOfᴬ tᴹ ≡ _) (pu : tyOfᴬ uᴹ ≡ _) → (bᴹ : Tmᴬ Γᴹ) (pb : tyOfᴬ bᴹ ≡ 𝔹ᴹ [ idSᴹ ]Tᴹ)
--         → (pt₂ : tyOfᴬ (tᴹ [ σᴹ ]tᴹ) ≡ P [ σᴹ ↑𝔹ᴹ ]Tᴹ [ idSᴹ ,ᴹ ttᴹ ∶[ tyOfttᴹ ] ]Tᴹ)
--         → (pu₂ : tyOfᴬ (uᴹ [ σᴹ ]tᴹ) ≡ P [ σᴹ ↑𝔹ᴹ ]Tᴹ [ idSᴹ ,ᴹ ffᴹ ∶[ tyOfffᴹ ] ]Tᴹ)
--         → (pb₂ : tyOfᴬ (bᴹ [ σᴹ ]tᴹ) ≡ 𝔹ᴹ [ idSᴹ ]Tᴹ)
--         → (P [ idSᴹ ,ᴹ bᴹ ∶[ pb ] ]Tᴹ [ σᴹ ]Tᴹ) ≡ (P [ (σᴹ ∘ᴹ π₁ᴹ idSᴹ) ,ᴹ π₂ᴹ idSᴹ ∶[ 𝔹[]₂ᴹ ] ]Tᴹ [ idSᴹ ,ᴹ bᴹ [ σᴹ ]tᴹ ∶[ pb₂ ] ]Tᴹ)
--         → (elim𝔹ᴹ P tᴹ uᴹ pt pu bᴹ pb) [ σᴹ ]tᴹ
--         ≡ elim𝔹ᴹ (P [ σᴹ ↑𝔹ᴹ ]Tᴹ) (tᴹ [ σᴹ ]tᴹ) (uᴹ [ σᴹ ]tᴹ) pt₂ pu₂ (bᴹ [ σᴹ ]tᴹ) pb₂

--   record UnivBoolᴹ (C : SCᴹ) (Univᵐ : Univᴹ C) (Boolᵐ : Boolᴹ C) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
--     open SCᴹ C
--     open Univᴹ Univᵐ
--     open Boolᴹ Boolᵐ

--     field
--       𝕓ᴹ
--         : Tmᴬ Γᴹ
--       tyOfᴹ
--         : tyOfᴬ {Γᴹ = Γᴹ} 𝕓ᴹ ≡ Uᴹ
--       𝕓[]ᴹ
--         : 𝕓ᴹ [ σᴹ ]tᴹ ≡ 𝕓ᴹ
--       tyOf𝕓ᴹ
--         : tyOfᴬ {Γᴹ} 𝕓ᴹ ≡ Uᴹ
--       Elᴹ𝕓ᴹ
--         : Elᴹ {Γᴹ} 𝕓ᴹ tyOf𝕓ᴹ ≡ 𝔹ᴹ
  
--   record UnivPiᴹ (C : SCᴹ) (Univᵐ : Univᴹ C) (Boolᵐ : Boolᴹ C) (Piᵐ : Piᴹ C) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
--     open SCᴹ C
--     open Univᴹ Univᵐ
--     open Piᴹ   Piᵐ

--     field
--       El[]₂ᴹ
--         : (uᴹ : Tmᴬ Δᴹ) (pu : tyOfᴬ uᴹ ≡ Uᴹ)(pu' : tyOfᴬ (uᴹ [ σᴹ ]tᴹ) ≡ Uᴹ)
--         → tyOfᴬ (π₂ᴹ {Γᴹ ,ᴹ Elᴹ (uᴹ [ σᴹ ]tᴹ) pu'} idSᴹ) ≡ Elᴹ uᴹ pu [ σᴹ ∘ᴹ π₁ᴹ idSᴹ ]Tᴹ

--     _↑Elᴹ
--       : (σᴹ : Subᴬ Γᴹ Δᴹ) {uᴹ : Tmᴬ Δᴹ} {pu : tyOfᴬ uᴹ ≡ Uᴹ} {pu' : tyOfᴬ (uᴹ [ σᴹ ]tᴹ) ≡ Uᴹ}
--       → Subᴬ (Γᴹ ,ᴹ Elᴹ (uᴹ [ σᴹ ]tᴹ) pu') (Δᴹ ,ᴹ Elᴹ uᴹ pu)
--     (σᴹ ↑Elᴹ) {uᴹ} {pu} {pu'} = (σᴹ ∘ᴹ π₁ᴹ idSᴹ) ,ᴹ π₂ᴹ idSᴹ ∶[ El[]₂ᴹ uᴹ pu pu' ]

--     field
--       πᴹ
--         : (a : Tmᴬ Γᴹ) (pa : tyOfᴬ a ≡ Uᴹ)
--         → (bᴹ : Tmᴬ (Γᴹ ,ᴹ Elᴹ a pa)) (pb : tyOfᴬ bᴹ ≡ Uᴹ)
--         → Tmᴬ Γᴹ
--       π[]ᴹ
--         : (aᴹ : Tmᴬ Γᴹ) (pa : tyOfᴬ aᴹ ≡ Uᴹ)
--         → (bᴹ : Tmᴬ (Γᴹ ,ᴹ Elᴹ aᴹ pa)) (pb : tyOfᴬ bᴹ ≡ Uᴹ)
--         → (pa' : tyOfᴬ (aᴹ [ σᴹ ]tᴹ) ≡ Uᴹ)
--         → (pb' : tyOfᴬ (bᴹ [ σᴹ ↑Elᴹ ]tᴹ) ≡ Uᴹ)
--         → (πᴹ aᴹ pa bᴹ pb) [ σᴹ ]tᴹ ≡ πᴹ (aᴹ [ σᴹ ]tᴹ) pa' (bᴹ [ σᴹ ↑Elᴹ ]tᴹ) pb'
--       tyOfπᴹ
--         : (a : Tmᴬ Γᴹ) (pa : tyOfᴬ a ≡ Uᴹ) (bᴹ : Tmᴬ (Γᴹ ,ᴹ Elᴹ a pa)) (pb : tyOfᴬ bᴹ ≡ Uᴹ)
--         → tyOfᴬ (πᴹ a pa bᴹ pb) ≡ Uᴹ
--       Elπᴹ
--         : (aᴹ : Tmᴬ Γᴹ) (pa : tyOfᴬ aᴹ ≡ Uᴹ)
--         → (bᴹ : Tmᴬ (Γᴹ ,ᴹ Elᴹ aᴹ pa)) (pb : tyOfᴬ bᴹ ≡ Uᴹ)
--         → Elᴹ (πᴹ aᴹ pa bᴹ pb) (tyOfπᴹ aᴹ pa bᴹ pb) ≡ Πᴹ (Elᴹ aᴹ pa) (Elᴹ bᴹ pb)

-- module _
--   (mot : Motive ℓ₁ ℓ₂ ℓ₃ ℓ₄) (SCᵐ : SCᴹ mot) (Boolᵐ : Boolᴹ mot SCᵐ) (Univᵐ : Univᴹ mot SCᵐ) (Piᵐ : Piᴹ mot SCᵐ) where

--   open Motive mot
--   open SCᴹ SCᵐ
--   open Boolᴹ Boolᵐ
--   open Univᴹ Univᵐ
--   open Piᴹ Piᵐ

--   recCtx  : Ctx → Ctxᴬ
--   recTy   : {Γ : Ctx} → Ty Γ → Tyᴬ (recCtx Γ)
--   recTm   : {Γ : Ctx} → Tm Γ → Tmᴬ (recCtx Γ)
--   recSub  : {Γ Δ : Ctx} → Sub Γ Δ → Subᴬ (recCtx Γ) (recCtx Δ)
--   recTyOf : {Γ : Ctx}{A : Ty Γ} → (t : Tm Γ) → tyOf t ≡ A → tyOfᴬ (recTm t) ≡ recTy A

--   recCtx ∅ = ∅ᴹ
--   recCtx (Γ , A) = recCtx Γ ,ᴹ recTy A

--   recTm⟨π₂idS⟩≡π₂ᴹidSᴹ : recTm (π₂ {A = A} idS) ≡ π₂ᴹ idSᴹ
--   recTm⟨t[σ]⟩=recTmt[recSubσ]tᴹ : recTm (t [ σ ]) ≡ recTm t [ recSub σ ]tᴹ

--   recTy (A [ σ ]) = recTy A [ recSub σ ]Tᴹ
--   recTy 𝔹 = 𝔹ᴹ
--   recTy U = Uᴹ
--   recTy (El u p) = Elᴹ (recTm u) (recTyOf u p)
--   recTy (Π A B) = Πᴹ (recTy A) (recTy B)
--   recTy ([idS]T {A = A} i) = [idS]Tᴹ {Aᴹ = recTy A} i
--   recTy ([∘]T A σ τ i) = [∘]Tᴹ (recTy A) (recSub σ) (recSub τ) i
--   recTy (U[] {σ = σ} i) = U[]ᴹ {σᴹ = recSub σ} i
--   recTy (El[] τ u p q i) = {!El[]ᴹ (recSub τ) (recTm u) (recTyOf u p) i!}
--    where
--     foo : (tyOf[]ᴹ ∙ cong (λ z → z [ recSub τ ]Tᴹ) (recTyOf u p) ∙ U[]ᴹ) ≡ {!recTyOf (u Foo.[ τ ]t) q!}
--     foo = {!!}
--   -- (El[]ᴹ (recSub τ) (recTm u) (recTyOf u p) {!(cong tyOfᴬ (recTm⟨t[σ]⟩=recTmt[recSubσ]tᴹ {t = u} {σ = τ})) ∙ recTyOf (u [ τ ]) q!}) i
--   recTy (El[]₂ u pu pu' i) = {!!}
--   recTy (Π[] i) = {!!}
--   recTy (𝔹[] {σ = σ} i) = 𝔹[]ᴹ {σᴹ = recSub σ} i
--   recTy (𝔹[]₂ {Γ = Γ} {Δ} {τ = τ} i) = {!!} -- ({!cong tyOfᴬ (recTm⟨π₂idS⟩≡π₂ᴹidSᴹ {{!Γ!}} {A = 𝔹})!} ∙ 𝔹[]₂ᴹ {τᴹ = recSub τ}) i
--   recTy (El𝕓 i) = {!!}
--   recTy (tyOfπ a pa b pb i) = {!!}
--   recTy (Elπ a pa b pb i) = {!!}
--   recTy (Ty-is-set A A₁ x y i i₁) = {!!}

--   recSub ∅S             = ∅Sᴹ
--   recSub (σ , t ∶[ p ]) = recSub σ ,ᴹ recTm t ∶[ recTyOf t p ]
--   recSub idS            = idSᴹ
--   recSub (τ ∘ σ)        = recSub τ ∘ᴹ recSub σ
--   recSub (π₁ σ)         = π₁ᴹ (recSub σ)
--   recSub (βπ₁ σ t p i)  = {!!}
--   recSub ((idS∘ σ) i)   = {!!}
--   recSub ((σ ∘idS) i)   = {!!}
--   recSub (assocS σ σ₁ σ₂ i) = {!!}
--   recSub (,∘ σ t σ₁ p q i)  = {!!}
--   recSub (η∅ σ i) = {!!}
--   recSub (ηπ σ i) = {!!}


--   recTm (t [ σ ]) = recTm t [ recSub σ ]tᴹ
--   recTm (π₂ σ)    = π₂ᴹ (recSub σ)
--   recTm (app t x) = {!!}
--   recTm (abs t)   = {!!}
--   recTm tt        = {!!}
--   recTm ff        = {!!}
--   recTm (elim𝔹 P t t₁ x x₁ t₂ x₂) = {!!}
--   recTm 𝕓 = {!!}
--   recTm (π t pa t₁ pb) = {!!}
--   recTm (βπ₂ σ t p q i) = {!!}
--   recTm ([idS]t t i) = {!!}
--   recTm ([∘]t t σ τ i) = {!!}
--   recTm (abs[] t i) = {!!}
--   recTm (Πβ t i) = {!!}
--   recTm (Πη t p i) = {!!}
--   recTm (tt[] i) = {!!}
--   recTm (ff[] i) = {!!}
--   recTm (elim𝔹[] P t t₁ pt pu t₂ pb pt₂ pu₂ pb₂ x i) = {!!}
--   recTm (𝕓[] i) = {!!}
--   recTm (π[] t pa t₁ pb pa' pb' i) = {!!}

--   recTm⟨π₂idS⟩≡π₂ᴹidSᴹ = refl
--   recTm⟨t[σ]⟩=recTmt[recSubσ]tᴹ = refl

--   recTyOf t p = {!!}
