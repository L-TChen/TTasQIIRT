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

よᵃ : Motive _ _ _ _
よᵃ .Motive.Ctxᴬ       = Ctxᴬ
よᵃ .Motive.Tyᴬ        = Tyᴬ
よᵃ .Motive.Subᴬ       = λ Γ Δ → Σ[ θ ∈ (∀ {Θ} → Subᴬ Θ Γ → Subᴬ Θ Δ) ]
  ({Ξ Θ : Ctxᴬ} (τ : Subᴬ Ξ Θ) (δ : Subᴬ Θ Γ) → θ δ ∘ᴹ τ ≡ θ (δ ∘ᴹ τ))
よᵃ .Motive.Tmᴬ        = Tmᴬ
よᵃ .Motive.tyOfᴬ      = tyOfᴬ
よᵃ .Motive.Tyᴬ-is-set = Tyᴬ-is-set
よᵃ .Motive.Subᴬ-is-set (σ , pσ) (τ , pτ) p q = {!!}

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
  , λ τ δ →
    let q = tyOf[]ᴹ ∙ cong _[ τ ]Tᴹ (tyOf[]ᴹ ∙ (λ i → p i [ δ ]Tᴹ) ∙ [∘]Tᴹ A δ (σ idSᴹ) ∙ cong (A [_]Tᴹ) (pσ δ idSᴹ ∙ cong σ (idS∘ᴹ δ))) ∙ [∘]Tᴹ A τ (σ δ) in 
  ,∘ᴹ (σ δ) (t [ δ ]tᴹ) τ
    (tyOf[]ᴹ ∙ (λ i → p i [ δ ]Tᴹ) ∙ [∘]Tᴹ A δ (σ idSᴹ) ∙ cong (A [_]Tᴹ) (pσ δ idSᴹ ∙ cong σ (idS∘ᴹ δ))) q
    ∙ cong,∶[] q (tyOf[]ᴹ ∙ cong _[ δ ∘ᴹ τ ]Tᴹ p ∙ [∘]Tᴹ A (δ ∘ᴹ τ) (σ idSᴹ) ∙ cong (A [_]Tᴹ) (pσ (δ ∘ᴹ τ) idSᴹ ∙ cong σ (idS∘ᴹ _)))
        (pσ τ δ) ([∘]tᴹ t τ δ)
よᵐ .SCᴹ.idSᴹ        = (λ γ → γ) , λ τ δ → refl
よᵐ .SCᴹ._∘ᴹ_ (σ , pσ) (τ , pτ) = (λ γ → σ (τ γ)) ,
   λ τ δ → pσ τ _ ∙ cong σ (pτ _ _)
よᵐ .π₁ᴹ (σ , pσ) = (λ γ → π₁ᴹ (σ γ)) ,
   λ τ δ → sym (π₁∘ᴹ (σ δ) τ) ∙ cong π₁ᴹ (pσ _ _)
よᵐ .SCᴹ.π₂ᴹ (σ , pσ) = π₂ᴹ (σ idSᴹ)   
よᵐ .SCᴹ.tyOfπ₂ᴹ (σ , pσ) = tyOfπ₂ᴹ (σ idSᴹ)
よᵐ .SCᴹ.idS∘ᴹ_ (σ , pσ) i = σ ,
   λ τ δ → Subᴬ-is-set _ _ (refl ∙ pσ τ δ) (pσ _ _) i 
よᵐ .SCᴹ._∘idSᴹ (σ , pσ) i = σ ,
   λ τ δ → Subᴬ-is-set _ _ (pσ τ δ ∙ refl) (pσ τ δ) i
よᵐ .SCᴹ.assocSᴹ (σ , pσ) (τ , pτ) (θ , pθ) i = (λ γ → θ (τ (σ γ))) , λ where
  τ' δ → let p = (λ j → hcomp
                (doubleComp-faces (λ _ → θ (τ (σ δ)) ∘ᴹ τ')
                (λ i₂ → θ (τ (pσ τ' δ i₂))) j) (hcomp
                (doubleComp-faces (λ _ → θ (τ (σ δ)) ∘ᴹ τ')
                  (λ i₂ → θ (pτ τ' (σ δ) i₂)) j) (pθ τ' (τ (σ δ)) j)))
             q = (λ i₁ → hcomp
                  (doubleComp-faces (λ _ → θ (τ (σ δ)) ∘ᴹ τ')
                  (λ i₂ → θ
                      (hcomp
                      (doubleComp-faces (λ _ → τ (σ δ) ∘ᴹ τ') (λ i₃ → τ (pσ τ' δ i₃)) i₂)
                      (pτ τ' (σ δ) i₂))) i₁) (pθ τ' (τ (σ δ)) i₁))
    in Subᴬ-is-set _ _ p q i 
よᵐ .SCᴹ.[idS]Tᴹ = [idS]Tᴹ
よᵐ .SCᴹ.[∘]Tᴹ A (σ , pσ) (τ , pτ) = [∘]Tᴹ A (σ idSᴹ) (τ idSᴹ) ∙ cong (A [_]Tᴹ)
  (pτ (σ idSᴹ) idSᴹ ∙ cong τ (idS∘ᴹ (σ idSᴹ)))
よᵐ .SCᴹ.,∘ᴹ (σ , pσ) t (τ , pτ) p q = {!!}
よᵐ .SCᴹ.ηπᴹ (σ , pσ) i = (λ γ →  (ηπᴹ (σ γ) ∙ cong,∶[] (tyOfπ₂ᴹ (σ γ)) {!!} {!!} {!!}) i ) , λ τ δ → {!!}
よᵐ .SCᴹ.η∅ᴹ (σ , pσ) i = (λ γ → η∅ᴹ (σ γ) i) , λ τ δ → {!!}
よᵐ .SCᴹ.βπ₁ᴹ {Aᴹ = Aᴹ} (σ , pσ) t p i = (λ γ → βπ₁ᴹ (σ γ) (t [ γ ]tᴹ) (tyOf[]ᴹ ∙ cong _[ γ ]Tᴹ p ∙ [∘]Tᴹ _ γ (σ idSᴹ) ∙ cong (_ [_]Tᴹ) (pσ γ idSᴹ ∙ cong σ (idS∘ᴹ γ))) i) ,
  λ τ δ → Subᴬ-is-set _ _ {!!} {!!} i   
よᵐ .SCᴹ.βπ₂ᴹ (σ , pσ) t p = βπ₂ᴹ (σ idSᴹ) _ _ ∙ sym ([idS]tᴹ t)
よᵐ .SCᴹ.[idS]tᴹ t = [idS]tᴹ t
よᵐ .SCᴹ.[∘]tᴹ   t (σ , _) (τ , pτ) = [∘]tᴹ t (σ idSᴹ) (τ idSᴹ) ∙ cong (t [_]tᴹ) (pτ (σ idSᴹ) idSᴹ ∙ cong τ (idS∘ᴹ _))
よᵐ .SCᴹ.Uᴹ   = Uᴹ
よᵐ .SCᴹ.U[]ᴹ = U[]ᴹ   
