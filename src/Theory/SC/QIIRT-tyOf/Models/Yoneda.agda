open import Prelude
open import Theory.SC.QIIRT-tyOf.Model

module Theory.SC.QIIRT-tyOf.Models.Yoneda
  (A : Motive ℓ₁ ℓ₂ ℓ₃ ℓ₄) (SCᵐ : SCᴹ A) where

open Motive A
open SCᴹ SCᵐ

cong,∶[]
  : {σᴹ σ'ᴹ : Subᴬ Γᴹ Δᴹ}{tᴹ t'ᴹ : Tmᴬ Γᴹ}
  → (pᴹ : tyOfᴬ tᴹ ≡ Aᴹ [ σᴹ ]Tᴹ) (p'ᴹ : tyOfᴬ t'ᴹ ≡ Aᴹ [ σ'ᴹ ]Tᴹ)
  → σᴹ ≡ σ'ᴹ → tᴹ ≡ t'ᴹ
  → (σᴹ ,ᴹ tᴹ ∶[ pᴹ ]) ≡ (σ'ᴹ ,ᴹ t'ᴹ ∶[ p'ᴹ ])
cong,∶[] {Aᴹ = Aᴹ} p p' eqσ eqt =
  cong₃ _,ᴹ_∶[_] eqσ eqt (isSet→SquareP (λ _ _ → Tyᴬ-is-set) p p' (cong tyOfᴬ eqt) (cong (Aᴹ [_]Tᴹ) eqσ))

--open Motive

{-
Subʸ : (Γ Δ : Ctxᴬ) → Set (ℓ-max ℓ₁ ℓ₃)
Subʸ Γ Δ = Σ[ θ ∈ (∀ {Θ} → Subᴬ Θ Γ → Subᴬ Θ Δ) ]
  ({Ξ Θ : Ctxᴬ} (τ : Subᴬ Ξ Θ) (δ : Subᴬ Θ Γ) → θ δ ∘ᴹ τ ≡ θ (δ ∘ᴹ τ))

Subʸ-τidS∘ : ((τ , pτ) : Subʸ Γᴹ Δᴹ)
  → (γᴹ : Subᴬ Ξᴹ Γᴹ)
  → τ idSᴹ ∘ᴹ γᴹ ≡ τ γᴹ
Subʸ-τidS∘ (τ , pτ) γᴹ = pτ γᴹ idSᴹ ∙ cong τ (idS∘ᴹ γᴹ)
-}

record Subʸ (Γ Δ : Ctxᴬ) : Set (ℓ-max ℓ₁ ℓ₃) where
  constructor _,_
  field
    y : ∀{Θ} → Subᴬ Θ Γ → Subᴬ Θ Δ
    natʸ : {Ξ Θ : Ctxᴬ} (τ : Subᴬ Ξ Θ) (δ : Subᴬ Θ Γ) → y δ ∘ᴹ τ ≡ y (δ ∘ᴹ τ)

open Subʸ ⦃...⦄

Subʸ-τidS∘
  : ⦃ _ : Subʸ Γᴹ Δᴹ ⦄ → (γᴹ : Subᴬ Ξᴹ Γᴹ)
  → y idSᴹ ∘ᴹ γᴹ ≡ y γᴹ
Subʸ-τidS∘ γᴹ = natʸ γᴹ idSᴹ ∙ cong y (idS∘ᴹ γᴹ)

_≡ʸ_ : ∀ {Γ Δ} → Subʸ Γ Δ → Subʸ Γ Δ → Set (ℓ-max ℓ₁ ℓ₃)
(σ , pσ) ≡ʸ (σ' , pσ') = ∀{Θ} {γ : Subᴬ Θ _} → σ γ ≡ σ' γ

≡ʸ→≡ : ∀{Γ Δ} {σʸ σ'ʸ : Subʸ Γ Δ} → σʸ ≡ʸ σ'ʸ → σʸ ≡ σ'ʸ
≡ʸ→≡  {σʸ = σʸ} {σ'ʸ} eqʸ i = record
  { y = λ γ → eqʸ {γ = γ} i
  ; natʸ = λ τ δ j → isSet→SquareP (λ _ _ → Subᴬ-is-set) (cong (_∘ᴹ τ) eqʸ) eqʸ (natʸ ⦃ σʸ ⦄ τ δ) (natʸ ⦃ σ'ʸ ⦄ τ δ) j i
  }

よᵃ : Motive _ _ _ _
よᵃ .Motive.Ctxᴬ       = Ctxᴬ
よᵃ .Motive.Tyᴬ        = Tyᴬ
よᵃ .Motive.Subᴬ       = Subʸ
よᵃ .Motive.Tmᴬ        = Tmᴬ
よᵃ .Motive.tyOfᴬ      = tyOfᴬ
よᵃ .Motive.Tyᴬ-is-set = Tyᴬ-is-set
よᵃ .Motive.Subᴬ-is-set (σ , pσ) (τ , pτ) p q = {! !}

-- open SCᴹ
よᵐ : SCᴹ よᵃ
よᵐ .SCᴹ.∅ᴹ          = ∅ᴹ
よᵐ .SCᴹ._,ᴹ_        = _,ᴹ_
よᵐ .SCᴹ._[_]Tᴹ A (σ , _) = A [ σ idSᴹ ]Tᴹ
よᵐ .SCᴹ._[_]tᴹ t (σ , _) = t [ σ idSᴹ ]tᴹ
よᵐ .SCᴹ.tyOf[]ᴹ     = tyOf[]ᴹ
よᵐ .SCᴹ.∅Sᴹ         = (λ _ → ∅Sᴹ) , λ τ δ → η∅ᴹ _
よᵐ .SCᴹ._,ᴹ_∶[_] {Aᴹ = A} (σ , pσ) t p =
  (λ γ → σ γ ,ᴹ t [ γ ]tᴹ ∶[ tyOf[]ᴹ ∙ (λ i → p i [ γ ]Tᴹ) ∙ [∘]Tᴹ A γ (σ idSᴹ) ∙ (λ i → A [ (pσ γ idSᴹ ∙ cong σ (idS∘ᴹ γ)) i ]Tᴹ)  ])
  , λ τ δ → let q = tyOf[]ᴹ ∙ cong _[ τ ]Tᴹ (tyOf[]ᴹ ∙ (λ i → p i [ δ ]Tᴹ) ∙ [∘]Tᴹ A δ (σ idSᴹ) ∙ cong (A [_]Tᴹ) (Subʸ-τidS∘ ⦃ σ , pσ ⦄ δ)) ∙ [∘]Tᴹ A τ (σ δ) in 
  ,∘ᴹ (σ δ) (t [ δ ]tᴹ) τ
    (tyOf[]ᴹ ∙ (λ i → p i [ δ ]Tᴹ) ∙ [∘]Tᴹ A δ (σ idSᴹ) ∙ cong (A [_]Tᴹ) (Subʸ-τidS∘ ⦃ σ , pσ ⦄ δ)) q
    ∙ cong,∶[] q (tyOf[]ᴹ ∙ cong _[ δ ∘ᴹ τ ]Tᴹ p ∙ [∘]Tᴹ A (δ ∘ᴹ τ) (σ idSᴹ) ∙ cong (A [_]Tᴹ) (pσ (δ ∘ᴹ τ) idSᴹ ∙ cong σ (idS∘ᴹ _)))
        (pσ τ δ) ([∘]tᴹ t τ δ)
よᵐ .SCᴹ.idSᴹ        = (λ γ → γ) , λ τ δ → refl
よᵐ .SCᴹ._∘ᴹ_ (σ , pσ) (τ , pτ) = (λ γ → σ (τ γ)) ,
   λ τ δ → pσ τ _ ∙ cong σ (pτ _ _)
よᵐ .π₁ᴹ (σ , pσ) = (λ γ → π₁ᴹ (σ γ)) ,
   λ τ δ → sym (π₁∘ᴹ (σ δ) τ) ∙ cong π₁ᴹ (pσ _ _)
よᵐ .SCᴹ.π₂ᴹ (σ , pσ) = π₂ᴹ (σ idSᴹ)   
よᵐ .SCᴹ.tyOfπ₂ᴹ (σ , pσ) = tyOfπ₂ᴹ (σ idSᴹ)
よᵐ .SCᴹ.idS∘ᴹ_ (σ , pσ) = ≡ʸ→≡ refl
よᵐ .SCᴹ._∘idSᴹ (σ , pσ) = ≡ʸ→≡ refl
よᵐ .SCᴹ.assocSᴹ (σ , pσ) (τ , pτ) (θ , pθ) = ≡ʸ→≡ refl
よᵐ .SCᴹ.[idS]Tᴹ = [idS]Tᴹ
よᵐ .SCᴹ.[∘]Tᴹ A (σ , pσ) (τ , pτ) = [∘]Tᴹ A (σ idSᴹ) (τ idSᴹ) ∙ cong (A [_]Tᴹ) (Subʸ-τidS∘ ⦃ τ , pτ ⦄ (σ idSᴹ))
よᵐ .SCᴹ.,∘ᴹ (σ , pσ) t τʸ p q = ≡ʸ→≡ λ {_} {γ} → cong,∶[] _ _ refl (cong (t [_]tᴹ) (sym (Subʸ-τidS∘ ⦃ τʸ ⦄ γ)) ∙ sym ([∘]tᴹ _ _ _))
よᵐ .SCᴹ.ηπᴹ (σ , pσ) = ≡ʸ→≡ λ {_} {γ} → ηπᴹ (σ γ) ∙ cong,∶[] _ _ refl (sym (cong π₂ᴹ (Subʸ-τidS∘ ⦃ σ , pσ ⦄ γ)) ∙ π₂∘ᴹ (σ idSᴹ) γ)
よᵐ .SCᴹ.η∅ᴹ (σ , pσ) = ≡ʸ→≡ (η∅ᴹ _)
よᵐ .SCᴹ.βπ₁ᴹ {Aᴹ = Aᴹ} (σ , pσ) t p = ≡ʸ→≡ (βπ₁ᴹ _ _ _)
よᵐ .SCᴹ.βπ₂ᴹ (σ , pσ) t p = βπ₂ᴹ (σ idSᴹ) _ _ ∙ sym ([idS]tᴹ t)
よᵐ .SCᴹ.[idS]tᴹ t = [idS]tᴹ t
よᵐ .SCᴹ.[∘]tᴹ   t (σ , _) (τ , pτ) = [∘]tᴹ t (σ idSᴹ) (τ idSᴹ) ∙ cong (t [_]tᴹ) (pτ (σ idSᴹ) idSᴹ ∙ cong τ (idS∘ᴹ _))
よᵐ .SCᴹ.Uᴹ   = Uᴹ
よᵐ .SCᴹ.U[]ᴹ = U[]ᴹ
