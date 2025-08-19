open import Prelude

module Theory.SC.QIIRT-tyOf.Model where

record Motive (ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level) : Set (ℓ-suc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)) where
  field
    Ctx  : Set ℓ₁
    Ty   : Ctx → Set ℓ₂
    Sub  : Ctx → Ctx → Set ℓ₃
    Tm   : Ctx → Set ℓ₄
    tyOf : {Γ : Ctx} → Tm Γ → Ty Γ

--    Ty-is-set : {Γ : Ctx} → isSet (Ty Γ)
--    Sub-is-set : {Γ Δ : Ctx} → isSet (Sub Γ Δ)
--    Tm-is-set : {Γ : Ctx} → isSet (Tm Γ)

  module GVars where
    variable
      Γ Δ Θ Ξ : Ctx
      A B C D : Ty Γ
      σ τ γ    : Sub Γ Δ
      t u v    : Tm Γ

module _ (mot : Motive ℓ₁ ℓ₂ ℓ₃ ℓ₄) where
  open Motive mot
  open GVars

  record SC : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
    field
      ∅
        : Ctx
      _,C_
        : (Γ : Ctx)(A : Ty Γ)
        → Ctx
      _[_]T
        : (A : Ty Δ)(σ : Sub Γ Δ)
        → Ty Γ
      _[_]t
        : (t : Tm Δ)(σ : Sub Γ Δ)
        → Tm Γ
      tyOf[]
        : tyOf (t [ σ ]t) ≡ (tyOf t) [ σ ]T
      ∅S
        : Sub Γ ∅
      _,_∶[_]
        : (σ : Sub Γ Δ) (t : Tm Γ) → tyOf t ≡ A [ σ ]T
        → Sub Γ (Δ ,C A)
      idS
        : Sub Γ Γ
      _∘_
        : Sub Δ Θ → Sub Γ Δ
        → Sub Γ Θ
      π₁
        : Sub Γ (Δ ,C A)
        → Sub Γ Δ
      π₂
        : Sub Γ (Δ ,C A)
        → Tm Γ
      tyOfπ₂
        : {A : Ty Δ} (σ : Sub Γ (Δ ,C A))
        → tyOf (π₂ {A = A} σ) ≡ A [ π₁ σ ]T
      idS∘_
        : (σ : Sub Γ Δ)
        → idS ∘ σ ≡ σ
      _∘idS
        : (σ : Sub Γ Δ)
        → σ ∘ idS ≡ σ
      assocS
        : (σ : Sub Γ Δ) (τ : Sub Δ Θ) (γ : Sub Θ Ξ)
        → (γ ∘ τ) ∘ σ ≡ γ ∘ (τ ∘ σ)
      [idS]T
        : A ≡ A [ idS ]T
      [∘]T
        : (A : Ty Θ) (σ : Sub Γ Δ) (τ : Sub Δ Θ)
        → A [ τ ]T [ σ ]T ≡ A [ τ ∘ σ ]T
      ,∘
        : (σ : Sub Δ Θ) (t : Tm Δ) (τ : Sub Γ Δ)
        → (p : tyOf t ≡ A [ σ ]T) (q : tyOf (t [ τ ]t) ≡ A [ σ ∘ τ ]T)
--        → let q = tyOf (t [ τ ]t)
--                    ≡⟨ tyOf[] ⟩
--                  (tyOf t) [ τ ]T
--                    ≡[ i ]⟨ p i [ τ ]T ⟩
--                  A [ σ ]T [ τ ]T
--                    ≡⟨ [∘]T _ _ _ ⟩
--                  A [ σ ∘ τ ]T
--                    ∎
--        in
        → (σ , t ∶[ p ]) ∘ τ ≡ ((σ ∘ τ) , t [ τ ]t ∶[ q ])
      ηπ
        : (σ : Sub Γ (Δ ,C A))
        → σ ≡ (π₁ σ , π₂ σ ∶[ tyOfπ₂ _ ])
      η∅
        : (σ : Sub Γ ∅)
        → σ ≡ ∅S
      βπ₁
        : (σ : Sub Γ Δ) (t : Tm Γ) (p : tyOf t ≡ A [ σ ]T)
        → π₁ (σ , t ∶[ p ]) ≡ σ
      βπ₂
        : (σ : Sub Γ Δ) (t : Tm Γ) (p : tyOf t ≡ A [ σ ]T)
--        → (q : A [ π₁ (σ , t ∶[ p ]) ]T ≡  tyOf t)
        → π₂ (σ , t ∶[ p ]) ≡ t
      [idS]t
        : (t : Tm Γ)
        → t ≡ t [ idS ]t
      [∘]t
        : (t : Tm Θ) (σ : Sub Γ Δ) (τ : Sub Δ Θ)
        → t [ τ ]t [ σ ]t ≡ t [ τ ∘ σ ]t
      U
        : Ty Γ
      U[]
        : U [ σ ]T ≡ U

    
    tyOfπ₂[]
      : (τ : Sub Δ (Θ ,C A))
      → (σ : Sub Γ Δ)
      → tyOf (π₂ τ [ σ ]t) ≡ A [ π₁ τ ∘ σ ]T
    tyOfπ₂[] {Δ} {Θ} {A} {_} τ σ = tyOf[] ∙ (λ i → tyOfπ₂ τ i [ σ ]T) ∙ [∘]T A σ (π₁ τ)
--      tyOf (π₂ τ [ σ ]t)
--        ≡⟨ tyOf[] ⟩
--      tyOf (π₂ τ) [ σ ]T
--        ≡[ i ]⟨ tyOfπ₂ τ i [ σ ]T ⟩
--      A [ π₁ τ ]T [ σ ]T
--        ≡⟨ [∘]T A σ (π₁ τ) ⟩
--      A [ π₁ τ ∘ σ ]T
--        ∎
        
    π₁∘
      : (τ : Sub Δ (Θ ,C A)) (σ : Sub Γ Δ)
      → π₁ (τ ∘ σ) ≡ π₁ τ ∘ σ
    π₁∘ {A = A} τ σ =
      π₁ (τ ∘ σ)
        ≡⟨ cong π₁ (cong (_∘ σ) (ηπ τ)) ⟩
      π₁ ((π₁ τ , π₂ τ ∶[ tyOfπ₂ τ ]) ∘ σ)
        ≡⟨ cong π₁ (,∘ (π₁ τ) (π₂ τ) σ (tyOfπ₂ τ) (tyOfπ₂[] τ σ)) ⟩
      π₁ ((π₁ τ ∘ σ) , (π₂ τ [ σ ]t) ∶[ _ ])
        ≡⟨  βπ₁ (π₁ τ ∘ σ) (π₂ τ [ σ ]t)
          (tyOf[] ∙ cong _[ σ ]T (tyOfπ₂ τ) ∙ [∘]T _ _ _)  ⟩
      π₁ τ ∘ σ
        ∎

    π₂∘
      : (τ : Sub Δ (Θ ,C A)) (σ : Sub Γ Δ)
      → π₂ (τ ∘ σ) ≡ π₂ τ [ σ ]t
    π₂∘ τ σ =
      π₂ (τ ∘ σ)
        ≡[ i ]⟨ π₂ (ηπ τ i ∘ σ) ⟩
      π₂ ((π₁ τ , π₂ τ ∶[ _ ]) ∘ σ)
        ≡[ i ]⟨ π₂ (,∘ (π₁ τ) (π₂ τ) σ (tyOfπ₂ τ) (tyOfπ₂[] τ σ) i) ⟩
      π₂ ((π₁ τ ∘ σ) , (π₂ τ [ σ ]t) ∶[ _ ])
        ≡⟨ βπ₂ _ _ _ ⟩
      π₂ τ [ σ ]t
        ∎

    π₁σ=π₁idS∘σ
      : (σ : Sub Γ (Δ ,C A))
      → π₁ σ ≡ π₁ idS ∘ σ
    π₁σ=π₁idS∘σ σ =
      π₁ σ
        ≡[ i ]⟨ π₁ ((idS∘ σ) (~ i)) ⟩
      π₁ (idS ∘ σ)
        ≡⟨ π₁∘ idS σ ⟩
      π₁ idS ∘ σ
        ∎
    
    π₂σ=π₂id[σ]
      : (σ : Sub Γ (Δ ,C A))
      → π₂ σ ≡ π₂ idS [ σ ]t
    π₂σ=π₂id[σ] σ =
      π₂ σ
        ≡[ i ]⟨ π₂ ((idS∘ σ) (~ i)) ⟩
      π₂ (idS ∘ σ)
        ≡⟨ π₂∘ idS σ ⟩
      π₂ idS [ σ ]t
        ∎
    
    cong,∶[]
      : {Γ Δ : Ctx} {A : Ty Δ}
      {σ  : Sub Γ Δ} {t : Tm Γ}
      (p : tyOf t ≡ A [ σ ]T)
      {σ' : Sub Γ Δ} {t' : Tm Γ}
      (p' : tyOf t' ≡ A [ σ' ]T)
      → σ ≡ σ' → t ≡ t'
      → (σ , t ∶[ p ]) ≡ (σ' , t' ∶[ p' ])
    cong,∶[] {A = A} p p' eqσ eqt =
      cong₃ _,_∶[_] eqσ eqt (isSet→SquareP (λ _ _ _ _ → UIP) p p' (cong tyOf eqt) (cong (A [_]T) eqσ))
--      cong₃ _,_∶[_] eqσ eqt (isSet→SquareP (λ _ _ → Ty-is-set) p p' (cong tyOf eqt) (cong (A [_]T) eqσ))
