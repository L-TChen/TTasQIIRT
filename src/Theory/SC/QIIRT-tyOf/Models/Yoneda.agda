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

record Subʸ (Γ Δ : Ctxᴬ) : Set (ℓ-max ℓ₁ ℓ₃) where
  constructor _,_
  field
    y : ∀{Θ} → Subᴬ Θ Γ → Subᴬ Θ Δ
    natʸ : {Ξ Θ : Ctxᴬ} (τ : Subᴬ Ξ Θ) (δ : Subᴬ Θ Γ) → y δ ∘ᴹ τ ≡ y (δ ∘ᴹ τ)
  Subʸ-τidS∘
    : ∀{Ξ} (γᴹ : Subᴬ Ξ Γ)
    → y idSᴹ ∘ᴹ γᴹ ≡ y γᴹ
  Subʸ-τidS∘ γᴹ = natʸ γᴹ idSᴹ ∙ cong y (idS∘ᴹ γᴹ)
open Subʸ

Subʸ-is-set : ∀{Γ Δ} → isSet (Subʸ Γ Δ)
Subʸ-is-set {Γ} {Δ} (σ , pσ) (σ' , pσ') p q i j = record
  { y = λ γᴹ → isSet→SquareP (λ _ _ → Subᴬ-is-set) refl refl (λ k → y (p k) γᴹ) (λ k → y (q k) γᴹ) j i
  ; natʸ = λ {Ξ} {Θ} τ δ k →
    isGroupoid→CubeP (λ _ _ _ → Subᴬ Ξ Δ)
      (λ j i → isSet→SquareP (λ _ _ → Subᴬ-is-set) refl refl (λ k → y (p k) δ) (λ k → y (q k) δ) j i ∘ᴹ τ)
      (λ j i → isSet→SquareP (λ _ _ → Subᴬ-is-set) refl refl (λ k → y (p k) (δ ∘ᴹ τ)) (λ k → y (q k) (δ ∘ᴹ τ)) j i)
      (λ k _ → pσ τ δ k)
      (λ k _ → pσ' τ δ k)
      (λ k j → natʸ (p j) τ δ k)
      (λ k j → natʸ (q j) τ δ k)
      (isSet→isGroupoid Subᴬ-is-set) k j i
  }

_≡ʸ_ : ∀{Γ Δ} → Subʸ Γ Δ → Subʸ Γ Δ → Set (ℓ-max ℓ₁ ℓ₃)
_≡ʸ_ {Γ} {Δ} (σ , pσ) (σ' , pσ') = _≡_ {A = {Θ : Ctxᴬ} → Subᴬ Θ Γ → Subᴬ Θ Δ} σ σ' -- ∀{Θ} {γᴹ : Subᴬ Θ _} → σ γᴹ ≡ σ' γᴹ

≡ʸ→≡ : ∀{Γ Δ} {σʸ σ'ʸ : Subʸ Γ Δ} → σʸ ≡ʸ σ'ʸ → σʸ ≡ σ'ʸ
≡ʸ→≡  {σʸ = σʸ} {σ'ʸ} eqʸ i = record
  { y = eqʸ i
  ; natʸ = λ τ δ j →
      isSet→SquareP (λ _ _ → Subᴬ-is-set)
        (λ i → eqʸ i δ ∘ᴹ τ)
        (λ i → eqʸ i (δ ∘ᴹ τ))
        (natʸ σʸ τ δ)
        (natʸ σ'ʸ τ δ)
        j i
  }

infixr 2 step-≡ʸ

step-≡ʸ : ∀{Γ Δ σ'ʸ σ''ʸ}(σʸ : Subʸ Γ Δ) → σ'ʸ ≡ σ''ʸ → σʸ ≡ʸ σ'ʸ → σʸ ≡ σ''ʸ
step-≡ʸ σʸ p pʸ = ≡ʸ→≡ pʸ ∙ p

syntax step-≡ʸ σʸ p pʸ = σʸ ≡ʸ⟨ pʸ ⟩ p

_∘ʸ_ : ∀{Γ Δ Θ} → Subʸ Δ Θ → Subʸ Γ Δ → Subʸ Γ Θ
(σ , pσ) ∘ʸ (σ' , pσ') = (λ γ → σ (σ' γ)) , λ τ δ → pσ τ _ ∙ cong σ (pσ' _ _)

[∘]Tʸ
  : ∀{Γ Δ Θ}(A : Tyᴬ Θ)(σʸ : Subʸ Γ Δ)(τʸ : Subʸ Δ Θ)
  → A [ y τʸ idSᴹ ]Tᴹ [ y σʸ idSᴹ ]Tᴹ ≡ A [ y (τʸ ∘ʸ σʸ) idSᴹ ]Tᴹ
[∘]Tʸ A σʸ τʸ = [∘]Tᴹ A (y σʸ idSᴹ) (y τʸ idSᴹ) ∙ cong (A [_]Tᴹ) (Subʸ-τidS∘ τʸ (y σʸ idSᴹ))

よᵃ : Motive _ _ _ _
よᵃ .Motive.Ctxᴬ        = Ctxᴬ
よᵃ .Motive.Tyᴬ         = Tyᴬ
よᵃ .Motive.Subᴬ        = Subʸ
よᵃ .Motive.Tmᴬ         = Tmᴬ
よᵃ .Motive.tyOfᴬ       = tyOfᴬ
よᵃ .Motive.Tyᴬ-is-set  = Tyᴬ-is-set
よᵃ .Motive.Subᴬ-is-set = Subʸ-is-set
よᵃ .Motive.Tmᴬ-is-set  = Tmᴬ-is-set

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
  , λ τ δ → let q = tyOf[]ᴹ ∙ cong _[ τ ]Tᴹ (tyOf[]ᴹ ∙ (λ i → p i [ δ ]Tᴹ) ∙ [∘]Tᴹ A δ (σ idSᴹ) ∙ cong (A [_]Tᴹ) (Subʸ-τidS∘ (σ , pσ) δ)) ∙ [∘]Tᴹ A τ (σ δ) in 
  ,∘ᴹ (σ δ) (t [ δ ]tᴹ) τ
    (tyOf[]ᴹ ∙ (λ i → p i [ δ ]Tᴹ) ∙ [∘]Tᴹ A δ (σ idSᴹ) ∙ cong (A [_]Tᴹ) (Subʸ-τidS∘ (σ , pσ) δ)) q
    ∙ cong,∶[] q (tyOf[]ᴹ ∙ cong _[ δ ∘ᴹ τ ]Tᴹ p ∙ [∘]Tᴹ A (δ ∘ᴹ τ) (σ idSᴹ) ∙ cong (A [_]Tᴹ) (pσ (δ ∘ᴹ τ) idSᴹ ∙ cong σ (idS∘ᴹ _)))
        (pσ τ δ) ([∘]tᴹ t τ δ)
よᵐ .SCᴹ.idSᴹ = (λ γ → γ) , λ τ δ → refl
よᵐ .SCᴹ._∘ᴹ_ = _∘ʸ_
よᵐ .π₁ᴹ (σ , pσ) = (λ γ → π₁ᴹ (σ γ)) ,
   λ τ δ → sym (π₁∘ᴹ (σ δ) τ) ∙ cong π₁ᴹ (pσ _ _)
よᵐ .SCᴹ.π₂ᴹ (σ , pσ) = π₂ᴹ (σ idSᴹ)   
よᵐ .SCᴹ.tyOfπ₂ᴹ (σ , pσ) = tyOfπ₂ᴹ (σ idSᴹ)
よᵐ .SCᴹ.idS∘ᴹ_ (σ , pσ) = ≡ʸ→≡ refl
よᵐ .SCᴹ._∘idSᴹ (σ , pσ) = ≡ʸ→≡ refl
よᵐ .SCᴹ.assocSᴹ (σ , pσ) (τ , pτ) (θ , pθ) = ≡ʸ→≡ refl
よᵐ .SCᴹ.[idS]Tᴹ = [idS]Tᴹ
よᵐ .SCᴹ.[∘]Tᴹ = [∘]Tʸ
よᵐ .SCᴹ.,∘ᴹ {Aᴹ = Aᴹ} (σ , pσ) t τʸ p q = ≡ʸ→≡ λ i γ →
  let r = tyOf[]ᴹ ∙ (λ j → p j [ y τʸ γ ]Tᴹ) ∙ [∘]Tᴹ Aᴹ (y τʸ γ) (σ idSᴹ) ∙ (λ j → Aᴹ [ (pσ (y τʸ γ) idSᴹ ∙ (λ k → σ ((idS∘ᴹ (y τʸ γ)) k))) j ]Tᴹ)
      r' = tyOf[]ᴹ ∙ (λ j → q j [ γ ]Tᴹ) ∙ [∘]Tᴹ Aᴹ γ (y ((σ , pσ) ∘ʸ τʸ) idSᴹ) ∙ (λ j → Aᴹ [ (natʸ ((σ , pσ) ∘ʸ τʸ) γ idSᴹ ∙ (λ k → y ((σ , pσ) ∘ʸ τʸ) ((idS∘ᴹ γ) k))) j ]Tᴹ)
  in cong,∶[] r r' refl (cong (t [_]tᴹ) (sym (Subʸ-τidS∘ τʸ γ)) ∙ sym ([∘]tᴹ _ _ _)) i
よᵐ .SCᴹ.ηπᴹ {Aᴹ = Aᴹ} (σ , pσ) = ≡ʸ→≡ λ i γ →
  let p = tyOf[]ᴹ ∙ (λ j → tyOfπ₂ᴹ (σ idSᴹ) j [ γ ]Tᴹ) ∙ [∘]Tᴹ Aᴹ γ (π₁ᴹ (σ idSᴹ)) ∙ (λ j → Aᴹ [ (((λ k → π₁∘ᴹ (σ idSᴹ) γ (~ k)) ∙ (λ k → π₁ᴹ (pσ γ idSᴹ k))) ∙ (λ k → π₁ᴹ (σ ((idS∘ᴹ γ) k)))) j ]Tᴹ)
  in (ηπᴹ (σ γ) ∙ cong,∶[] (tyOfπ₂ᴹ (σ γ)) p refl (sym (cong π₂ᴹ (Subʸ-τidS∘ (σ , pσ) γ)) ∙ π₂∘ᴹ (σ idSᴹ) γ)) i
よᵐ .SCᴹ.η∅ᴹ (σ , pσ) = ≡ʸ→≡ λ i γ → η∅ᴹ (σ γ) i
よᵐ .SCᴹ.βπ₁ᴹ {Aᴹ = Aᴹ} (σ , pσ) t p = ≡ʸ→≡ λ i γ →
  let p = tyOf[]ᴹ ∙ (λ j → p j [ γ ]Tᴹ) ∙ [∘]Tᴹ Aᴹ γ (σ idSᴹ) ∙ (λ j → Aᴹ [ (pσ γ idSᴹ ∙ (λ k → σ ((idS∘ᴹ γ) k))) j ]Tᴹ)
  in βπ₁ᴹ (σ γ) (t [ γ ]tᴹ) p i
よᵐ .SCᴹ.βπ₂ᴹ (σ , pσ) t p = βπ₂ᴹ (σ idSᴹ) _ _ ∙ sym ([idS]tᴹ t)
よᵐ .SCᴹ.[idS]tᴹ t = [idS]tᴹ t
よᵐ .SCᴹ.[∘]tᴹ   t (σ , _) (τ , pτ) = [∘]tᴹ t (σ idSᴹ) (τ idSᴹ) ∙ cong (t [_]tᴹ) (pτ (σ idSᴹ) idSᴹ ∙ cong τ (idS∘ᴹ _))
よᵐ .SCᴹ.Uᴹ   = Uᴹ
よᵐ .SCᴹ.U[]ᴹ = U[]ᴹ
