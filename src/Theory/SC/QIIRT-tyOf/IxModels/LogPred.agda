module Theory.SC.QIIRT-tyOf.IxModels.LogPred where

open import Prelude
open import Theory.SC.QIIRT-tyOf.Syntax
open import Theory.SC.QIIRT-tyOf.IxModel

record Ctxᴾ (Γ : Ctx) : Set where
  field
    ctxᴾ : Ctx
    wkᴾ  : Sub ctxᴾ Γ
open Ctxᴾ

Tyᴾ : Ctxᴾ Γ → Ty Γ →  Set
Tyᴾ Γᴾ A = Ty (ctxᴾ Γᴾ , A [ wkᴾ Γᴾ ])

record Subᴾ (Γᴾ : Ctxᴾ Γ)(Δᴾ : Ctxᴾ Δ)(σ : Sub Γ Δ) : Set where
  field
    subᴾ : Sub (ctxᴾ Γᴾ) (ctxᴾ Δᴾ)
    wkᴾnat : wkᴾ Δᴾ ∘ subᴾ ≡ σ ∘ wkᴾ Γᴾ
open Subᴾ

Tmᴾ : (Γᴾ : Ctxᴾ Γ) → (t : Tm Γ) → Set
Tmᴾ Γᴾ t = Σ[ t' ∈ Tm (ctxᴾ Γᴾ) ] tyOf t' ≡ tyOf t [ wkᴾ Γᴾ ]

LogPredᵃ : Motive _ _ _ _
LogPredᵃ = record
  { Ctxᴬ  = Ctxᴾ
  ; Tyᴬ   = Tyᴾ
  ; Subᴬ  = Subᴾ
  ; Tmᴬ   = Tmᴾ
  ; tyOfᴬ = {!!}
  }

open SCᴹ

LogPredᵐ : SCᴹ LogPredᵃ
LogPredᵐ .∅ᴹ                 = record { ctxᴾ = ∅ ; wkᴾ = ∅ }
LogPredᵐ ._,ᴹ_ {A = A} Γᴾ Aᴾ = record
  { ctxᴾ = (ctxᴾ Γᴾ , A [ wkᴾ Γᴾ ]) , Aᴾ
  ; wkᴾ  = (wkᴾ Γᴾ ↑ A) ∘ π₁ idS
  }
LogPredᵐ ._[_]Tᴹ {Δ} {Δᴾ} {A} {Γ} {Γᴾ} {σ} Aᴾ σᴾ = 
  Aᴾ [ transport (λ i → Sub (ctxᴾ Γᴾ , p i) (ctxᴾ Δᴾ , (A [ wkᴾ Δᴾ ]))) (subᴾ σᴾ ↑ (A [ wkᴾ Δᴾ ])) ]
  where
    p : _≡_ {A = Ty (ctxᴾ Γᴾ)} (A [ wkᴾ Δᴾ ] [ subᴾ σᴾ ]) (A [ σ ] [ wkᴾ Γᴾ ])
    p = [∘]T A (subᴾ σᴾ) (wkᴾ Δᴾ)
      ∙ cong (A [_]) (wkᴾnat σᴾ)
      ∙ sym ([∘]T A (wkᴾ Γᴾ) σ)
LogPredᵐ ._[_]tᴹ {Δ} {Δᴾ} {t} {Γ} {Γᴾ} {σ} tᴾ σᴾ =
  t [ wkᴾ Δᴾ ] [ subᴾ σᴾ ] , [∘]T _ _ _ ∙ (λ i → tyOf t [ wkᴾnat σᴾ i ]) ∙ sym ([∘]T _ _ _)
LogPredᵐ .[idS]Tᴹ    = {!!}
LogPredᵐ .tyOf[]ᴹ    = {!!}
LogPredᵐ .∅Sᴹ        = record
  { subᴾ   = ∅
  ; wkᴾnat = η∅ _ ∙ sym (η∅ _)
  }
LogPredᵐ ._,ᴹ_∶[_,_] = {!!}
LogPredᵐ .idSᴹ       = record
  { subᴾ   = idS
  ; wkᴾnat = (_ ∘idS) ∙ sym (idS∘ _)
  }
LogPredᵐ ._∘ᴹ_ {τ = τ} σᴾ τᴾ = record
  { subᴾ   = subᴾ σᴾ ∘ subᴾ τᴾ
  ; wkᴾnat = sym (assocS _ _ _) ∙ cong (_∘ subᴾ τᴾ) (wkᴾnat σᴾ)
    ∙ assocS _ _ _ ∙ cong (τ ∘_) (wkᴾnat τᴾ) ∙ sym (assocS _ _ _)  }
LogPredᵐ .π₁ᴹ {Γ} {Γᴾ} {Δ} {Δᴾ} {A} {Aᴾ} {σ} σᴾ = record
  { subᴾ = π₁ (π₁ (subᴾ σᴾ))
  ; wkᴾnat =
      wkᴾ Δᴾ ∘ π₁ (π₁ (subᴾ σᴾ))
        ≡⟨ cong (wkᴾ Δᴾ ∘_) (π₁idS (π₁ (subᴾ σᴾ))) ⟩
      wkᴾ Δᴾ ∘ (π₁ idS ∘ π₁ (subᴾ σᴾ))
        ≡⟨ sym (assocS _ _ _) ⟩
      (wkᴾ Δᴾ ∘ π₁ idS) ∘ π₁ (subᴾ σᴾ)
        ≡⟨ sym (βπ₁ ((wkᴾ Δᴾ ∘ π₁ idS) ∘ π₁ (subᴾ σᴾ)) (π₂ idS [ π₁ (subᴾ σᴾ) ]) _) ⟩
      π₁ ((wkᴾ Δᴾ ∘ π₁ idS) ∘ π₁ (subᴾ σᴾ) , π₂ idS [ π₁ (subᴾ σᴾ) ] ∶[ _ ])
        ≡⟨ cong π₁
          ((wkᴾ Δᴾ ∘ π₁ idS) ∘ π₁ (subᴾ σᴾ) , π₂ idS [ π₁ (subᴾ σᴾ) ] ∶[ _ ]
            ≡⟨ sym (⟨,∘⟩ (wkᴾ Δᴾ ∘ π₁ idS) (π₂ idS) (π₁ (subᴾ σᴾ)) tyOfπ₂idS) ⟩
          (wkᴾ Δᴾ ↑ A) ∘ π₁ (subᴾ σᴾ)
            ≡⟨ cong ((wkᴾ Δᴾ ↑ A) ∘_) (π₁idS (subᴾ σᴾ)) ⟩
          (wkᴾ Δᴾ ↑ A) ∘ (π₁ idS ∘ subᴾ σᴾ)
            ≡⟨ sym (assocS _ _ _) ⟩
          ((wkᴾ Δᴾ ↑ A) ∘ π₁ idS) ∘ subᴾ σᴾ
            ≡⟨ wkᴾnat σᴾ ⟩
          σ ∘ wkᴾ Γᴾ
            ∎)
        ⟩
      π₁ (σ ∘ wkᴾ Γᴾ)
        ≡⟨ π₁∘ σ (wkᴾ Γᴾ) ⟩
      π₁ σ ∘ wkᴾ Γᴾ
        ∎
  }
LogPredᵐ .π₂ᴹ {Γ} {Γᴾ} {Δ} {Δᴾ} {A} {Aᴾ} {σ} σᴾ =
  π₂ (π₁ (subᴾ σᴾ)) , [∘]T _ _ _ ∙ cong (A [_]) p ∙ sym ([∘]T _ _ _)
  where
    p : wkᴾ Δᴾ ∘ π₁ (π₁ (subᴾ σᴾ)) ≡ π₁ σ ∘ wkᴾ Γᴾ
    p =
      wkᴾ Δᴾ ∘ π₁ (π₁ (subᴾ σᴾ))
        ≡⟨ cong (wkᴾ Δᴾ ∘_) (π₁idS (π₁ (subᴾ σᴾ))) ⟩
      wkᴾ Δᴾ ∘ (π₁ idS ∘ π₁ (subᴾ σᴾ))
        ≡⟨ sym (assocS _ _ _) ⟩
      (wkᴾ Δᴾ ∘ π₁ idS) ∘ π₁ (subᴾ σᴾ)
        ≡⟨ sym (βπ₁ ((wkᴾ Δᴾ ∘ π₁ idS) ∘ π₁ (subᴾ σᴾ)) (π₂ idS [ π₁ (subᴾ σᴾ) ]) _) ⟩
      π₁ ((wkᴾ Δᴾ ∘ π₁ idS) ∘ π₁ (subᴾ σᴾ) , π₂ idS [ π₁ (subᴾ σᴾ) ] ∶[ _ ])
        ≡⟨ cong π₁
          ((wkᴾ Δᴾ ∘ π₁ idS) ∘ π₁ (subᴾ σᴾ) , π₂ idS [ π₁ (subᴾ σᴾ) ] ∶[ _ ]
            ≡⟨ sym (⟨,∘⟩ (wkᴾ Δᴾ ∘ π₁ idS) (π₂ idS) (π₁ (subᴾ σᴾ)) tyOfπ₂idS) ⟩
          (wkᴾ Δᴾ ↑ A) ∘ π₁ (subᴾ σᴾ)
            ≡⟨ cong ((wkᴾ Δᴾ ↑ A) ∘_) (π₁idS (subᴾ σᴾ)) ⟩
          (wkᴾ Δᴾ ↑ A) ∘ (π₁ idS ∘ subᴾ σᴾ)
            ≡⟨ sym (assocS _ _ _) ⟩
          ((wkᴾ Δᴾ ↑ A) ∘ π₁ idS) ∘ subᴾ σᴾ
            ≡⟨ wkᴾnat σᴾ ⟩
          σ ∘ wkᴾ Γᴾ
            ∎)
        ⟩
      π₁ (σ ∘ wkᴾ Γᴾ)
        ≡⟨ π₁∘ σ (wkᴾ Γᴾ) ⟩
      π₁ σ ∘ wkᴾ Γᴾ
        ∎
LogPredᵐ .Uᴹ = U
LogPredᵐ .tyOfπ₂ᴹ = {!!}
LogPredᵐ .idS∘ᴹ_ σᴹ = {!!}
LogPredᵐ ._∘idSᴹ σᴹ = {!!}
LogPredᵐ .assocSᴹ σᴹ τᴹ γᴹ = {!!}
LogPredᵐ .,∘ᴹ σᴹ tᴹ τᴹ p₁ pᴹ q qᴹ = {!!}
LogPredᵐ .ηπᴹ σᴹ = {!!}
LogPredᵐ .η∅ᴹ σᴹ = {!!}
LogPredᵐ .βπ₁ᴹ σᴹ tᴹ p₁ pᴹ = {!!}
LogPredᵐ .βπ₂ᴹ σᴹ tᴹ p₁ pᴹ q qᴹ = {!!}
LogPredᵐ .[∘]Tᴹ Aᴹ σᴹ τᴹ = {!!}
LogPredᵐ .[idS]tᴹ tᴹ = {!!}
LogPredᵐ .[∘]tᴹ tᴹ σᴹ τᴹ = {!!}
LogPredᵐ .U[]ᴹ = {!!}
