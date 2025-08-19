module Theory.SC.QIIRT-tyOf.IxModel where

open import Prelude

open import Theory.SC.QIIRT-tyOf.Syntax
open GVars

record Motive (ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level) : Set (ℓ-suc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)) where
  field
    Ctx∙
      : (Γ : Ctx)
      → Set ℓ₁
    Ty∙
      : Ctx∙ Γ → Ty Γ
      → Set ℓ₂
    Sub∙
      : (Γ∙ : Ctx∙ Γ) (Δ∙ : Ctx∙ Δ) → Sub Γ Δ
      → Set ℓ₃
    Tm∙
      : Ctx∙ Γ → Tm Γ
      → Set ℓ₄
    tyOf∙
      : {Γ∙ : Ctx∙ Γ} → Tm∙ Γ∙ t
      → Ty∙ Γ∙ (tyOf t)

  -- SC∙ is defined separately from Motive in order to declare
  -- generalizable variables.

  variable
    Γ∙ Δ∙ Θ∙ Ξ∙ : Ctx∙ Γ
    A∙ B∙ C∙ D∙ : Ty∙  Γ∙ A
    σ∙ τ∙ γ∙    : Sub∙ Γ∙ Δ∙ σ
    t∙ u∙ v∙    : Tm∙  Γ∙ t

  infix 4 _≡Ty[_]_ _≡Tm[_]_ _≡Sub[_]_

  _≡Ty[_]_ : Ty∙ Γ∙ A → A ≡ B → Ty∙ Γ∙ B → Type ℓ₂
  _≡Ty[_]_ {Γ} {Γ∙} A∙ e B∙ = PathP (λ i → Ty∙ Γ∙ (e i)) A∙ B∙

  _≡Tm[_]_ : Tm∙ Γ∙ t → t ≡ u → Tm∙ Γ∙ u → Type ℓ₄
  _≡Tm[_]_ {Γ} {Γ∙} t∙ e u∙ = PathP (λ i → Tm∙ Γ∙ (e i)) t∙ u∙

  _≡Sub[_]_ : Sub∙ Γ∙ Δ∙ σ → σ ≡ τ → Sub∙ Γ∙ Δ∙ τ → Type ℓ₃
  _≡Sub[_]_ {Γ} {Γ∙} {Δ} {Δ∙} σ∙ e τ∙ = PathP (λ i → Sub∙ Γ∙ Δ∙ (e i)) σ∙ τ∙

module _ (mot : Motive ℓ₁ ℓ₂ ℓ₃ ℓ₄) where
  open Motive mot

  record SC∙ : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
    field
      ∅∙
        : Ctx∙ ∅
      _,∙_
        : (Γ∙ : Ctx∙ Γ)(A∙ : Ty∙ Γ∙ A)
        → Ctx∙ (Γ , A)
      _[_]T∙
        : (A∙ : Ty∙ Δ∙ A)(σ∙ : Sub∙ Γ∙ Δ∙ σ)
        → Ty∙ Γ∙ (A [ σ ])
      _[_]t∙
        : (t∙ : Tm∙ Δ∙ t)(σ∙ : Sub∙ Γ∙ Δ∙ σ)
        → Tm∙ Γ∙ (t [ σ ])
      tyOf[]∙
        : tyOf∙ (t∙ [ σ∙ ]t∙) ≡ (tyOf∙ t∙) [ σ∙ ]T∙
      ∅S∙
        : Sub∙ Γ∙ ∅∙ ∅
      _,∙_∶[_,_]
        : (σ∙ : Sub∙ Γ∙ Δ∙ σ) {A∙ : Ty∙ Δ∙ A} (t∙ : Tm∙ Γ∙ t)
        → (p : tyOf t ≡ A [ σ ])
        → tyOf∙ t∙ ≡Ty[ p ] (A∙ [ σ∙ ]T∙)
        → Sub∙ Γ∙ (Δ∙ ,∙ A∙) (σ , t ∶[ p ])
      idS∙
        : Sub∙ Γ∙ Γ∙ idS
      _∘∙_
        : Sub∙ Δ∙ Θ∙ τ → Sub∙ Γ∙ Δ∙ σ
        → Sub∙ Γ∙ Θ∙ (τ ∘ σ)
      π₁∙
        : Sub∙ Γ∙ (Δ∙ ,∙ A∙) σ
        → Sub∙ Γ∙ Δ∙ (π₁ σ)
      π₂∙
        : Sub∙ Γ∙ (Δ∙ ,∙ A∙) σ
        → Tm∙ Γ∙ (π₂ σ)
      tyOfπ₂∙
        : tyOf∙ (π₂∙ σ∙) ≡ A∙ [ π₁∙ σ∙ ]T∙
      idS∘∙_
        : (σ∙ : Sub∙ Γ∙ Δ∙ σ)
        → idS∙ ∘∙ σ∙
        ≡Sub[ idS∘ σ ] σ∙
        -- [TODO] Justify the usage of transport in the eliminator
      _∘idS∙
        : (σ∙ : Sub∙ Γ∙ Δ∙ σ)
        → σ∙ ∘∙ idS∙
        ≡Sub[ σ ∘idS ] σ∙
      assocS∙
        : (σ∙ : Sub∙ Γ∙ Δ∙ σ) (τ∙ : Sub∙ Δ∙ Θ∙ τ) (γ∙ : Sub∙ Θ∙ Ξ∙ γ)
        → (γ∙ ∘∙ τ∙) ∘∙ σ∙
        ≡Sub[ assocS σ τ γ ]
           γ∙ ∘∙ (τ∙ ∘∙ σ∙)
      ,∘∙
        : (σ∙ : Sub∙ Δ∙ Θ∙ σ) (t∙ : Tm∙ Δ∙ t) (τ∙ : Sub∙ Γ∙ Δ∙ τ)
          (p : tyOf t ≡ A [ σ ]) (p∙ : tyOf∙ t∙ ≡Ty[ p ] A∙ [ σ∙ ]T∙)
          (q : tyOf (t [ τ ]) ≡ A [ σ ∘ τ ]) (q∙ : tyOf∙ (t∙ [ τ∙ ]t∙) ≡Ty[ q ] (A∙ [ σ∙ ∘∙ τ∙ ]T∙))
        → (σ∙ ,∙ t∙ ∶[ p , p∙ ]) ∘∙ τ∙
        ≡Sub[ ,∘ σ t τ p q ]
          (σ∙ ∘∙ τ∙) ,∙ t∙ [ τ∙ ]t∙ ∶[ q , q∙ ]
      ηπ∙
        : (σ∙ : Sub∙ Γ∙ (Δ∙ ,∙ A∙) σ)
        → σ∙ ≡Sub[ ηπ σ ] (π₁∙ σ∙ ,∙ π₂∙ σ∙ ∶[ refl , tyOfπ₂∙ ])
      η∅∙
        : (σ∙ : Sub∙ Γ∙ ∅∙ σ)
        → σ∙ ≡Sub[ η∅ σ ] ∅S∙
      βπ₁∙
        : (σ∙ : Sub∙ Γ∙ Δ∙ σ) (t∙ : Tm∙ Γ∙ t)
        → (p : tyOf t ≡ A [ σ ]) (p∙ : tyOf∙ t∙ ≡Ty[ p ] A∙ [ σ∙ ]T∙)
        → π₁∙ (σ∙ ,∙ t∙ ∶[ p , p∙ ]) ≡Sub[ βπ₁ σ t p ] σ∙
      βπ₂∙
        : (σ∙ : Sub∙ Γ∙ Δ∙ σ) (t∙ : Tm∙ Γ∙ t)
        → (p : tyOf t ≡ A [ σ ]) (p∙ : tyOf∙ t∙ ≡Ty[ p ] A∙ [ σ∙ ]T∙)
        → (q : A [ π₁ (σ , t ∶[ p ]) ] ≡ tyOf t)
          (q∙ : A∙ [ π₁∙ (σ∙ ,∙ t∙ ∶[ p , p∙ ]) ]T∙ ≡Ty[ q ] tyOf∙ t∙)
        → π₂∙ (σ∙ ,∙ t∙ ∶[ p , p∙ ])
        ≡[ i ⊢ Tm∙ Γ∙ (βπ₂ σ t p q i) ]
          t∙
      [idS]T∙
        : (A∙ : Ty∙ Γ∙ A)
        → A∙ ≡Ty[ [idS]T {Γ} {A} ] (A∙ [ idS∙ ]T∙)
      [∘]T∙
        : (A∙ : Ty∙ Θ∙ A) (σ∙ : Sub∙ Γ∙ Δ∙ σ) (τ∙ : Sub∙ Δ∙ Θ∙ τ)
        → A∙ [ τ∙ ]T∙ [ σ∙ ]T∙
        ≡Ty[ [∘]T A σ τ ]
          A∙ [ τ∙ ∘∙ σ∙ ]T∙
      [idS]t∙
        : (t∙ : Tm∙ Γ∙ t)
        → t∙
        ≡Tm[ [idS]t t ]
          t∙ [ idS∙ ]t∙
      [∘]t∙
        : (t∙ : Tm∙ Θ∙ t) (σ∙ : Sub∙ Γ∙ Δ∙ σ) (τ∙ : Sub∙ Δ∙ Θ∙ τ)
        → t∙ [ τ∙ ]t∙ [ σ∙ ]t∙
        ≡Tm[ [∘]t t σ τ ]
          t∙ [ τ∙ ∘∙ σ∙ ]t∙
      U∙
        : Ty∙ Γ∙ A
      U[]∙
        : {Γ∙ : Ctx∙ Γ} {Δ∙ : Ctx∙ Δ} {σ∙ : Sub∙ Γ∙ Δ∙ σ}
        → U∙ [ σ∙ ]T∙
        ≡Ty[ U[] {σ = σ} ]
          U∙
