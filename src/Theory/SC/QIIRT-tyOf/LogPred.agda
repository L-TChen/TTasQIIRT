module Theory.SC.QIIRT-tyOf.LogPred where

open import Prelude
open import Theory.SC.QIIRT-tyOf.Syntax

_↑_
  : (σ : Sub Γ Δ) (A : Ty Δ)
  → Sub (Γ , A [ σ ]) (Δ , A)
σ ↑ A = σ ∘ π₁ idS , π₂ idS ∶[ tyOfπ₂idS ]

record Ctxᴾ (Γ : Ctx) : Set where
  field
    ctxᴾ : Ctx
    wkᴾ  : Sub ctxᴾ Γ
open Ctxᴾ

Tyᴾ : Ctxᴾ Γ → Ty Γ → Set
Tyᴾ Γᴾ A = Ty (ctxᴾ Γᴾ , A [ wkᴾ Γᴾ ])

Tyᴾ-is-set : {Γᴾ : Ctxᴾ Γ} → isSet (Tyᴾ Γᴾ A)
Tyᴾ-is-set = Ty-is-set

record Subᴾ (Γᴾ : Ctxᴾ Γ)(Δᴾ : Ctxᴾ Δ)(σ : Sub Γ Δ) : Set where
  field
    subᴾ : Sub (ctxᴾ Γᴾ) (ctxᴾ Δᴾ)
    wkᴾnat : wkᴾ Δᴾ ∘ subᴾ ≡ σ ∘ wkᴾ Γᴾ
  
  [wkᴾnat] : (A : Ty Δ) → _≡_ {A = Ty (ctxᴾ Γᴾ)} (A [ wkᴾ Δᴾ ] [ subᴾ ]) (A [ σ ] [ wkᴾ Γᴾ ])
  [wkᴾnat] A = [∘]T _ _ _ ∙ cong (A [_]) wkᴾnat ∙ sym ([∘]T _ _ _)

open Subᴾ

Subᴾ-is-set
  : {Γᴾ : Ctxᴾ Γ}{Δᴾ : Ctxᴾ Δ}{σ : Sub Γ Δ}
  → isSet (Subᴾ Γᴾ Δᴾ σ)
Subᴾ-is-set {Δ = Δ} {Γᴾ = Γᴾ} {Δᴾ} {σ} σᴾ σ'ᴾ p q i j = record 
  { subᴾ = Sub-is-set (subᴾ σᴾ) (subᴾ σ'ᴾ) (λ k → subᴾ (p k)) (λ k → subᴾ (q k)) i j
  ; wkᴾnat = λ k → isGroupoid→CubeP (λ _ _ _ → Sub (ctxᴾ Γᴾ) Δ)
      (λ j i → wkᴾ Δᴾ ∘ Sub-is-set (subᴾ σᴾ) (subᴾ σ'ᴾ) (λ k → subᴾ (p k)) (λ k → subᴾ (q k)) i j)
      (λ _ _ → σ ∘ wkᴾ Γᴾ)
      (λ k i → wkᴾnat σᴾ k)
      (λ k i → wkᴾnat σ'ᴾ k)
      (λ k j → wkᴾnat (p j) k)
      (λ k j → wkᴾnat (q j) k)
      (isSet→isGroupoid Sub-is-set)
      k j i
  }

Tmᴾ : (Γᴾ : Ctxᴾ Γ) → (t : Tm Γ) → Set
Tmᴾ Γᴾ t = Σ[ t' ∈ Tm (ctxᴾ Γᴾ) ] tyOf t' ≡ tyOf t [ wkᴾ Γᴾ ]

tyOfᴾ
  : {Γᴾ : Ctxᴾ Γ} → Tmᴾ Γᴾ t
  → Tyᴾ Γᴾ (tyOf t)
tyOfᴾ {t = t} {Γᴾ = Γᴾ} _ = tyOf t [ wkᴾ Γᴾ ] [ π₁ idS ]

_[_]ᴾ : {Γᴾ : Ctxᴾ Γ}{Δᴾ : Ctxᴾ Δ}
      → Tyᴾ Δᴾ A → Subᴾ Γᴾ Δᴾ σ → Tyᴾ Γᴾ (A [ σ ])
_[_]ᴾ {A = A} {σ = σ} {Γᴾ = Γᴾ} {Δᴾ = Δᴾ} Aᴾ σᴾ =
  Aᴾ [ transport (λ i → Sub (ctxᴾ Γᴾ , [wkᴾnat] σᴾ A i) (ctxᴾ Δᴾ , (A [ wkᴾ Δᴾ ]))) (subᴾ σᴾ ↑ (A [ wkᴾ Δᴾ ])) ]

_[_]tᴾ : {Γᴾ : Ctxᴾ Γ}{Δᴾ : Ctxᴾ Δ}
       → Tmᴾ Δᴾ t → Subᴾ Γᴾ Δᴾ σ → Tmᴾ Γᴾ (t [ σ ])
_[_]tᴾ {t = t} {Γᴾ = Γᴾ} {Δᴾ = Δᴾ} tᴾ σᴾ = 
  t [ wkᴾ Δᴾ ] [ subᴾ σᴾ ] , [wkᴾnat] σᴾ (tyOf t)

∅ᴾ : Ctxᴾ ∅
∅ᴾ = record { ctxᴾ = ∅ ; wkᴾ = ∅ }

_,ᴾ_ : (Γᴾ : Ctxᴾ Γ)(Aᴾ : Tyᴾ Γᴾ A) → Ctxᴾ (Γ , A)
_,ᴾ_ {A = A} Γᴾ Aᴾ = record
  { ctxᴾ = (ctxᴾ Γᴾ , A [ wkᴾ Γᴾ ]) , Aᴾ
  ; wkᴾ  = (wkᴾ Γᴾ ↑ A) ∘ π₁ idS
  }

∅Sᴾ : {Γᴾ : Ctxᴾ Γ} → Subᴾ Γᴾ ∅ᴾ ∅
∅Sᴾ = record
  { subᴾ = ∅
  ; wkᴾnat = η∅ (∅ ∘ ∅) ∙ sym (η∅ _)
  }

idSᴾ : {Γᴾ : Ctxᴾ Γ} → Subᴾ Γᴾ Γᴾ idS
idSᴾ = record
  { subᴾ = idS
  ; wkᴾnat = (_ ∘idS) ∙ sym (idS∘ _)
  }

_∘ᴾ_
  : {Γᴾ : Ctxᴾ Γ}{Δᴾ : Ctxᴾ Δ}{Θᴾ : Ctxᴾ Θ}
  → Subᴾ Δᴾ Θᴾ σ → Subᴾ Γᴾ Δᴾ τ
  → Subᴾ Γᴾ Θᴾ (σ ∘ τ)
_∘ᴾ_ {σ = σ} σᴾ τᴾ = record
  { subᴾ = subᴾ σᴾ ∘ subᴾ τᴾ
  ; wkᴾnat =
      sym (assocS _ _ _)
      ∙ cong (_∘ subᴾ τᴾ) (wkᴾnat σᴾ)
      ∙ assocS _ _ _
      ∙ cong (σ ∘_) (wkᴾnat τᴾ)
      ∙ sym (assocS _ _ _)
  }

_,ᴾ_∶[_,_]
  : {Γᴾ : Ctxᴾ Γ}{Δᴾ : Ctxᴾ Δ}
  → (σᴾ : Subᴾ Γᴾ Δᴾ σ) {Aᴾ : Tyᴾ Δᴾ A} (tᴾ : Tmᴾ Γᴾ t)
  → (p : tyOf t ≡ A [ σ ])
  → tyOfᴾ {t = t} tᴾ ≡[ i ⊢ Tyᴾ Γᴾ (p i) ] (Aᴾ [ σᴾ ]ᴾ)
  → Subᴾ Γᴾ (Δᴾ ,ᴾ Aᴾ) (σ , t ∶[ p ])
_,ᴾ_∶[_,_] {A = A} {t} {Γᴾ = Γᴾ} σᴾ {Aᴾ} tᴾ p pᴾ = record
  { subᴾ = subᴾ σᴾ , t [ wkᴾ Γᴾ ] ∶[
        cong (_[ wkᴾ Γᴾ ]) p ∙ sym ([wkᴾnat] σᴾ A)
      ] ,
      fst tᴾ ∶[
        snd tᴾ ∙ {!   !}
      ]
  ; wkᴾnat = {!   !}
  }

wkᴾπ₁nat
  : {Γᴾ : Ctxᴾ Γ}{Δᴾ : Ctxᴾ Δ}{Aᴾ : Tyᴾ Δᴾ A}
  → (σᴾ : Subᴾ Γᴾ (Δᴾ ,ᴾ Aᴾ) σ)
  → wkᴾ Δᴾ ∘ π₁ (π₁ (subᴾ σᴾ)) ≡ π₁ σ ∘ wkᴾ Γᴾ
wkᴾπ₁nat {A = A} {σ = σ} {Γᴾ = Γᴾ} {Δᴾ = Δᴾ} σᴾ =
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

π₁ᴾ : {Γᴾ : Ctxᴾ Γ}{Δᴾ : Ctxᴾ Δ}{Aᴾ : Tyᴾ Δᴾ A} 
    → Subᴾ Γᴾ (Δᴾ ,ᴾ Aᴾ) σ
    → Subᴾ Γᴾ Δᴾ (π₁ σ)
π₁ᴾ {A = A} {σ = σ} {Γᴾ = Γᴾ} {Δᴾ} {Aᴾ} σᴾ = record
  { subᴾ = π₁ (π₁ (subᴾ σᴾ))
  ; wkᴾnat = wkᴾπ₁nat σᴾ
  }

π₂ᴾ : {Γᴾ : Ctxᴾ Γ}{Δᴾ : Ctxᴾ Δ}{Aᴾ : Tyᴾ Δᴾ A} 
    → Subᴾ Γᴾ (Δᴾ ,ᴾ Aᴾ) σ
    → Tmᴾ Γᴾ (π₂ σ)
π₂ᴾ {A = A} {σ} {Γᴾ = Γᴾ} {Δᴾ} {Aᴾ} σᴾ =
  π₂ (π₁ (subᴾ σᴾ)) , [∘]T _ _ _ ∙ cong (A [_]) (wkᴾπ₁nat σᴾ) ∙ sym ([∘]T _ _ _)

{-
⟦_⟧c : (Γ : Ctx) → Ctxᴾ Γ
⟦_⟧s : (σ : Sub Γ Δ) → Subᴾ ⟦ Γ ⟧c ⟦ Δ ⟧c σ
⟦_⟧ty : (A : Ty Γ) → Tyᴾ ⟦ Γ ⟧c A
⟦_⟧tm : (t : Tm Γ) → Tmᴾ ⟦ Γ ⟧c t

⟦ ∅ ⟧c = ∅ᴾ
⟦ Γ , A ⟧c = ⟦ Γ ⟧c ,ᴾ ⟦ A ⟧ty
⟦ ∅ {Γ} ⟧s = ∅Sᴾ
⟦ idS {Γ} ⟧s = idSᴾ
⟦ σ ∘ τ ⟧s = ⟦ σ ⟧s ∘ᴾ ⟦ τ ⟧s
⟦ _,_∶[_] {Γ} {A = A} σ t p ⟧s = ⟦ σ ⟧s ,ᴾ ⟦ t ⟧tm ∶[ p , {!   !} ]
⟦ π₁ {Γ} {Δ} {A} σ ⟧s = π₁ᴾ ⟦ σ ⟧s
⟦ βπ₁ σ t p i ⟧s = {!   !}
⟦ (idS∘ σ) i ⟧s = {!   !}
⟦ (σ ∘idS) i ⟧s = {!   !}
⟦ assocS σ σ₁ σ₂ i ⟧s = {!   !}
⟦ ,∘ σ t σ₁ p q i ⟧s = {!   !}
⟦ η∅ σ i ⟧s = {!   !}
⟦ ηπ σ i ⟧s = {!   !}
⟦ Sub-is-set σ σ' p q i j ⟧s = {!   !}
⟦ _[_] {Δ} {Γ} A σ ⟧ty = ⟦ A ⟧ty [ ⟦ σ ⟧s ]ᴾ
⟦ [idS]T i ⟧ty = {!   !}
⟦ [∘]T A σ τ i ⟧ty = {!   !}
⟦ U ⟧ty = U
⟦ U[] {Γ} {Δ} {σ = σ} i ⟧ty = {!   !}
⟦ Ty-is-set A A' p q i j ⟧ty = {!   !}
⟦ _[_] {Δ} {Γ} t σ ⟧tm = _[_]tᴾ {t = t} ⟦ t ⟧tm ⟦ σ ⟧s
⟦ π₂ σ ⟧tm = π₂ᴾ ⟦ σ ⟧s
⟦ βπ₂ σ t p q i ⟧tm = {!   !}
⟦ [idS]t t i ⟧tm = {!   !}
⟦ [∘]t t σ τ i ⟧tm = {!   !}
-}