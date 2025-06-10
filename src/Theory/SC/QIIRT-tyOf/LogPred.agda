module Theory.SC.QIIRT-tyOf.LogPred where

open import Prelude
open import Theory.SC.QIIRT-tyOf.Syntax


record Ctxᴾ (Γ : Ctx) : Set where
  field
    ctxᴾ : Ctx
    wkᴾ  : Sub ctxᴾ Γ
open Ctxᴾ

Tyᴾ : Ctxᴾ Γ → Ty Γ → Set
Tyᴾ Γᴾ A = Ty (ctxᴾ Γᴾ , A [ wkᴾ Γᴾ ])

record Subᴾ (Γᴾ : Ctxᴾ Γ)(Δᴾ : Ctxᴾ Δ)(σ : Sub Γ Δ) : Set where
  field
    subᴾ : Sub (ctxᴾ Γᴾ) (ctxᴾ Δᴾ)
    wkᴾnat : wkᴾ Δᴾ ∘ subᴾ ≡ σ ∘ wkᴾ Γᴾ
open Subᴾ

Tmᴾ : (Γᴾ : Ctxᴾ Γ) → (t : Tm Γ) → Set
Tmᴾ Γᴾ t = Σ[ t' ∈ Tm (ctxᴾ Γᴾ) ] tyOf t' ≡ tyOf t [ wkᴾ Γᴾ ]

_,ᴾ_ : (Γᴾ : Ctxᴾ Γ)(Aᴾ : Tyᴾ Γᴾ A) → Ctxᴾ (Γ , A)
_,ᴾ_ {A = A} Γᴾ Aᴾ = record
  { ctxᴾ = (ctxᴾ Γᴾ , A [ wkᴾ Γᴾ ]) , Aᴾ
  ; wkᴾ  = (wkᴾ Γᴾ ↑ A) ∘ π₁ idS
  }

_[_]ᴾ : {Γᴾ : Ctxᴾ Γ}{Δᴾ : Ctxᴾ Δ}
      → Tyᴾ Δᴾ A → Subᴾ Γᴾ Δᴾ σ → Tyᴾ Γᴾ (A [ σ ])
_[_]ᴾ {A = A} {σ = σ} {Γᴾ = Γᴾ} {Δᴾ = Δᴾ} Aᴾ σᴾ =
  Aᴾ [ transport (λ i → Sub (ctxᴾ Γᴾ , p i) (ctxᴾ Δᴾ , (A [ wkᴾ Δᴾ ]))) (subᴾ σᴾ ↑ (A [ wkᴾ Δᴾ ])) ]
  where
    p : _≡_ {A = Ty (ctxᴾ Γᴾ)} (A [ wkᴾ Δᴾ ] [ subᴾ σᴾ ]) (A [ σ ] [ wkᴾ Γᴾ ])
    p = [∘]T A (subᴾ σᴾ) (wkᴾ Δᴾ)
      ∙ cong (A [_]) (wkᴾnat σᴾ)
      ∙ sym ([∘]T A (wkᴾ Γᴾ) σ)

_[_]tᴾ : {Γᴾ : Ctxᴾ Γ}{Δᴾ : Ctxᴾ Δ}
       → Tmᴾ Δᴾ t → Subᴾ Γᴾ Δᴾ σ → Tmᴾ Γᴾ (t [ σ ])
_[_]tᴾ {t = t} {Γᴾ = Γᴾ} {Δᴾ = Δᴾ} tᴾ σᴾ = 
  t [ wkᴾ Δᴾ ] [ subᴾ σᴾ ] , [∘]T _ _ _ ∙ cong (tyOf t [_]) (wkᴾnat σᴾ) ∙ sym ([∘]T _ _ _)

π₁ᴾ : {Γᴾ : Ctxᴾ Γ}{Δᴾ : Ctxᴾ Δ}{Aᴾ : Tyᴾ Δᴾ A} 
    → Subᴾ Γᴾ (Δᴾ ,ᴾ Aᴾ) σ
    → Subᴾ Γᴾ Δᴾ (π₁ σ)
π₁ᴾ {A = A} {σ = σ} {Γᴾ = Γᴾ} {Δᴾ} {Aᴾ} σᴾ = record
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

π₂ᴾ : {Γᴾ : Ctxᴾ Γ}{Δᴾ : Ctxᴾ Δ}{Aᴾ : Tyᴾ Δᴾ A} 
    → Subᴾ Γᴾ (Δᴾ ,ᴾ Aᴾ) σ
    → Tmᴾ Γᴾ (π₂ σ)
π₂ᴾ {A = A} {σ} {Γᴾ = Γᴾ} {Δᴾ} {Aᴾ} σᴾ =
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

⟦_⟧c : (Γ : Ctx) → Ctxᴾ Γ
⟦_⟧ty : (A : Ty Γ) → Tyᴾ ⟦ Γ ⟧c A
⟦_⟧s : (σ : Sub Γ Δ) → Subᴾ ⟦ Γ ⟧c ⟦ Δ ⟧c σ
⟦_⟧tm : (t : Tm Γ) → Tmᴾ ⟦ Γ ⟧c t

⟦ ∅ ⟧c = record { ctxᴾ = ∅ ; wkᴾ = ∅S }
⟦ Γ , A ⟧c = ⟦ Γ ⟧c ,ᴾ ⟦ A ⟧ty
⟦ _[_] {Δ} {Γ} A σ ⟧ty = ⟦ A ⟧ty [ ⟦ σ ⟧s ]ᴾ
⟦ [idS]T i ⟧ty = {!   !}
⟦ [∘]T A σ τ i ⟧ty = {!   !}
⟦ U ⟧ty = U
⟦ U[] {Γ} {Δ} {σ = σ} i ⟧ty = {!   !}
⟦ Ty-is-set A A₁ x y i i₁ ⟧ty = {!   !}
⟦ ∅S ⟧s = record
  { subᴾ = ∅S
  ; wkᴾnat = η∅ (∅S ∘ ∅S) ∙ sym (η∅ _)
  }
⟦ _,_∶[_] {A = A} σ t p ⟧s = {!   !}
⟦ idS ⟧s = record
  { subᴾ = idS
  ; wkᴾnat = (_ ∘idS) ∙ sym (idS∘ _)
  }
⟦ σ ∘ τ ⟧s = record
  { subᴾ = subᴾ ⟦ σ ⟧s ∘ subᴾ ⟦ τ ⟧s
  ; wkᴾnat = sym (assocS _ _ _) ∙ cong (_∘ subᴾ ⟦ τ ⟧s) (wkᴾnat ⟦ σ ⟧s)
           ∙ assocS _ _ _ ∙ cong (σ ∘_) (wkᴾnat ⟦ τ ⟧s) ∙ sym (assocS _ _ _)
  }
⟦ π₁ {Γ} {Δ} {A} σ ⟧s = π₁ᴾ ⟦ σ ⟧s
⟦ βπ₁ σ t p i ⟧s = {!   !}
⟦ (idS∘ σ) i ⟧s = {!   !}
⟦ (σ ∘idS) i ⟧s = {!   !}
⟦ assocS σ σ₁ σ₂ i ⟧s = {!   !}
⟦ ,∘ σ t σ₁ p q i ⟧s = {!   !}
⟦ η∅ σ i ⟧s = {!   !}
⟦ ηπ σ i ⟧s = {!   !}
⟦ _[_] {Δ} {Γ} t σ ⟧tm = _[_]tᴾ {t = t} ⟦ t ⟧tm ⟦ σ ⟧s
⟦ π₂ σ ⟧tm = π₂ᴾ ⟦ σ ⟧s
⟦ βπ₂ σ t p q i ⟧tm = {!   !}
⟦ [idS]t t i ⟧tm = {!   !}
⟦ [∘]t t σ τ i ⟧tm = {!   !}
