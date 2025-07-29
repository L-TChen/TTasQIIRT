module Theory.SC+Pi+B.QIIRT-tyOf.Canonicity where

open import Prelude
open import Theory.SC+Pi+B.QIIRT-tyOf.Syntax
open import Theory.SC+Pi+B.QIIRT-tyOf.Model

record ⊤ : Set where constructor tt

Ctxᴳ : Ctx → Set₁
Ctxᴳ Γ = Sub ∅ Γ → Set

Subᴳ : Ctxᴳ Γ → Ctxᴳ Δ → Sub Γ Δ → Set
Subᴳ {Γ} {Δ} Γᴳ Δᴳ σ = (γ : Sub ∅ Γ) → Γᴳ γ → Δᴳ (σ ∘ γ)

Tyᴳ : Ctxᴳ Γ → Ty Γ → Set₁
Tyᴳ {Γ} Γᴳ A = (γ : Sub ∅ Γ) → Γᴳ γ → (t : Tm ∅) → . (tyOf t ≡ A [ γ ]) → Set

Tmᴳ : Ctxᴳ Γ → Tm Γ → Set₁
Tmᴳ {Γ} Γᴳ t = (γ : Sub ∅ Γ)(γᴳ : Γᴳ γ)
  → Σ[ A ∈ Ty Γ ] Σ[ Aᴳ ∈ Tyᴳ Γᴳ A ] Σ[ p ∈ tyOf t ≡ A ] Aᴳ γ γᴳ (t [ γ ]) (cong (_[ γ ]) p)

tyOfᴳ : {Γᴳ : Ctxᴳ Γ} → Tmᴳ Γᴳ t → Tyᴳ Γᴳ (tyOf t)
tyOfᴳ {Γ} {t} {Γᴳ} tᴳ γ γᴳ t' p' = let (A , Aᴳ , p , aᴳ) = tᴳ γ γᴳ in Aᴳ γ γᴳ t' (p' ∙ λ i → p i [ γ ])
{-
  (tyOfᴳ tᴳ [ σᴳ ]Tᴳ) γ γᴳ (t [ σ ] [ γ ]) (λ _ → tyOf t [ σ ] [ γ ])
    ≡⟨⟩
  tyOfᴳ tᴳ (σ ∘ γ) (σᴳ γ γᴳ) (t [ σ ] [ γ ]) (refl ∙ [∘]T _ _ _)
  ≟
  let (A , Aᴳ , p , aᴳ) = tᴳ (σ ∘ γ) (σᴳ γ γᴳ)
  in Aᴳ (σ ∘ γ) (σᴳ γ γᴳ) (t [ σ ∘ γ ]) (λ i → p i [ σ ∘ γ ])
-}

∅ᴳ : Ctxᴳ ∅
∅ᴳ _ = ⊤

_,ᴳ_ : (Γᴳ : Ctxᴳ Γ) → Tyᴳ Γᴳ A → Ctxᴳ (Γ , A)
Γᴳ ,ᴳ Aᴳ = λ γ → Σ[ γᴳ ∈ Γᴳ (π₁ γ) ] Aᴳ (π₁ γ) γᴳ (π₂ γ) refl

_[_]Tᴳ
  : {Γᴳ : Ctxᴳ Γ}{Δᴳ : Ctxᴳ Δ}
  → Tyᴳ Δᴳ A → Subᴳ Γᴳ Δᴳ σ → Tyᴳ Γᴳ (A [ σ ])
_[_]Tᴳ {σ = σ} Aᴳ σᴳ = λ γ γᴳ t p → Aᴳ (σ ∘ γ) (σᴳ γ γᴳ) t (p ∙ [∘]T _ _ _)

_[_]tᴳ
  : {Γᴳ : Ctxᴳ Γ}{Δᴳ : Ctxᴳ Δ}
  → Tmᴳ Δᴳ t → Subᴳ Γᴳ Δᴳ σ → Tmᴳ Γᴳ (t [ σ ])
_[_]tᴳ {t = t} {σ} tᴳ σᴳ = λ γ γᴳ
  → tyOf t [ σ ] , (tyOfᴳ tᴳ [ σᴳ ]Tᴳ) , refl ,
    let (A , Aᴳ , p , aᴳ) = tᴳ (σ ∘ γ) (σᴳ γ γᴳ)
    in transport (λ i → Aᴳ (σ ∘ γ) (σᴳ γ γᴳ) ([∘]t t γ σ (~ i)) {!   !}) aᴳ

∅Sᴳ : {Γᴳ : Ctxᴳ Γ} → Subᴳ Γᴳ ∅ᴳ ∅
∅Sᴳ _ _ = tt

_∘ᴳ_
  : {Γᴳ : Ctxᴳ Γ}{Δᴳ : Ctxᴳ Δ}{Θᴳ : Ctxᴳ Θ}
  → Subᴳ Δᴳ Θᴳ σ → Subᴳ Γᴳ Δᴳ τ
  → Subᴳ Γᴳ Θᴳ (σ ∘ τ)
_∘ᴳ_ {σ = σ} {τ} {Θᴳ = Θᴳ} σᴳ τᴳ γ γᴳ = transport (λ i → Θᴳ (assocS γ τ σ (~ i))) (σᴳ (τ ∘ γ) (τᴳ γ γᴳ))

idSᴳ : {Γᴳ : Ctxᴳ Γ} → Subᴳ Γᴳ Γᴳ idS
idSᴳ {Γᴳ = Γᴳ} γ γᴳ = transport (λ i → Γᴳ ((idS∘ γ) (~ i))) γᴳ

π₁ᴳ
  : {Γᴳ : Ctxᴳ Γ}{Δᴳ : Ctxᴳ Δ}{Aᴳ : Tyᴳ Δᴳ A}
  → Subᴳ Γᴳ (Δᴳ ,ᴳ Aᴳ) σ
  → Subᴳ Γᴳ Δᴳ (π₁ σ)
π₁ᴳ {σ = σ} {Δᴳ = Δᴳ} σᴳ γ γᴳ = let (δᴳ , _) = σᴳ γ γᴳ in transport (λ i → Δᴳ (π₁∘ σ γ i)) δᴳ

π₂ᴳ
  : {Γᴳ : Ctxᴳ Γ}{Δᴳ : Ctxᴳ Δ}{Aᴳ : Tyᴳ Δᴳ A}
  → Subᴳ Γᴳ (Δᴳ ,ᴳ Aᴳ) σ
  → Tmᴳ Γᴳ (π₂ σ)
π₂ᴳ {A = A} {σ = σ} {Δᴳ = Δᴳ} {Aᴳ} σᴳ γ γᴳ =
  A [ π₁ σ ] , Aᴳ [ π₁ᴳ {Aᴳ = Aᴳ} σᴳ ]Tᴳ , refl , let (_ , aᵍ) = σᴳ γ γᴳ in {!   !}