module Theory.SC.QIIRT-tyOf.Strict where

open import Prelude
open import Theory.SC.QIIRT-tyOf.Syntax
open import Theory.SC.QIIRT-tyOf.Model

postulate
  UIP : ∀ {ℓ} → {A : Set ℓ} → {x y : A} → isProp (x ≡ y)

cong,∶[]
  : {σ σ' : Sub Γ Δ}{t t' : Tm Γ}
  → (p : tyOf t ≡ A [ σ ])(p' : tyOf t' ≡ A [ σ' ])
  → σ ≡ σ' → t ≡ t'
  → (σ , t ∶[ p ]) ≡ (σ' , t' ∶[ p' ])
cong,∶[] {A = A} p p' eqσ eqt =
  cong₃ _,_∶[_] eqσ eqt (isSet→SquareP (λ _ _ → Ty-is-set) p p' (cong tyOf eqt) (cong (A [_]) eqσ))

-- record Tyˢ (Γ : Ctx) : Set where
--   constructor tyˢ
--   field
--     ΓTyˢ : Ctx
--     ATyˢ : Ty ΓTyˢ
--     σTyˢ : Sub Γ ΓTyˢ
--   ⌜_⌝tyˢ : Ty Γ
--   ⌜_⌝tyˢ = ATyˢ [ σTyˢ ]
-- open Tyˢ

-- infix 5 _≣_
-- _≣_ : Tyˢ Γ → Tyˢ Γ → Set
-- Aˢ ≣ A'ˢ = ⌜ Aˢ ⌝tyˢ ≡ ⌜ A'ˢ ⌝tyˢ

-- _,ˢ_ : (Γ : Ctx) → Tyˢ Γ → Ctx
-- Γ ,ˢ Aˢ = Γ , ⌜ Aˢ ⌝tyˢ

-- record Tmˢ (Γ : Ctx) : Set where
--   constructor tmˢ
--   field
--     ΓTmˢ : Ctx
--     tTmˢ : Tm ΓTmˢ
--     σTmˢ : Sub Γ ΓTmˢ
--   ⌜_⌝tmˢ : Tm Γ
--   ⌜_⌝tmˢ = tTmˢ [ σTmˢ ]
-- open Tmˢ

record Subˢ (Γ Δ : Ctx) : Set where
  constructor subˢ
  field
    y : Sub Θ Γ → Sub Θ Δ
    natˢ : (τ : Sub Ξ Θ)(δ : Sub Θ Γ) → y (δ ∘ τ) ≡ y δ ∘ τ
  ⌜_⌝subˢ : Sub Γ Δ
  ⌜_⌝subˢ = y idS
  natˢ-id : (τ : Sub Θ Γ) → y idS ∘ τ ≡ y τ
  natˢ-id τ = sym (natˢ τ idS) ∙ cong y (idS∘ τ)
open Subˢ

Yoneda : Motive _ _ _ _
Yoneda .Motive.Ctxᴬ = Ctx
Yoneda .Motive.Tyᴬ = Ty
Yoneda .Motive.Subᴬ = Subˢ
Yoneda .Motive.Tmᴬ = Tm
Yoneda .Motive.tyOfᴬ = tyOf
Yoneda .Motive.Tyᴬ-is-set = Ty-is-set

open SCᴹ
Yonedaᵐ : SCᴹ Yoneda
Yonedaᵐ .∅ᴹ = ∅
Yonedaᵐ ._,ᴹ_ = _,_
Yonedaᵐ ._[_]Tᴹ A σˢ = A [ y σˢ idS ]
Yonedaᵐ ._[_]tᴹ t σˢ = t [ y σˢ idS ]
Yonedaᵐ .tyOf[]ᴹ = {!   !}
Yonedaᵐ .∅Sᴹ = {!   !}
Yonedaᵐ ._,ᴹ_∶[_] = {!   !}
Yonedaᵐ .idSᴹ = subˢ (λ γ → γ) λ _ _ → refl
Yonedaᵐ ._∘ᴹ_ σˢ τˢ = subˢ (λ γ → y σˢ (y τˢ γ)) λ τ δ →
  cong (y σˢ) (natˢ τˢ τ δ) ∙ natˢ σˢ τ (y τˢ δ)
Yonedaᵐ .π₁ᴹ = {!   !}
Yonedaᵐ .π₂ᴹ = {!   !}
Yonedaᵐ .tyOfπ₂ᴹ = {!   !}
Yonedaᵐ .idS∘ᴹ_ σˢ i = record
  { y = y σˢ
  ; natˢ = λ τ δ → UIP {!   !} (natˢ σˢ τ δ) i
  }
Yonedaᵐ ._∘idSᴹ σˢ i = record
  { y = y σˢ
  ; natˢ = λ τ δ → UIP {!   !} (natˢ σˢ τ δ) i
  }
Yonedaᵐ .assocSᴹ σˢ τˢ γˢ i .y γ = y γˢ (y τˢ (y σˢ γ))
Yonedaᵐ .assocSᴹ σˢ τˢ γˢ i .natˢ τ δ = {!   !}
Yonedaᵐ .[idS]Tᴹ = {!   !}
Yonedaᵐ .[∘]Tᴹ = {!   !}
Yonedaᵐ .,∘ᴹ = {!   !}
Yonedaᵐ .ηπᴹ = {!   !}
Yonedaᵐ .η∅ᴹ = {!   !}
Yonedaᵐ .βπ₁ᴹ = {!   !}
Yonedaᵐ .βπ₂ᴹ = {!   !}
Yonedaᵐ .[idS]tᴹ = {!   !}
Yonedaᵐ .[∘]tᴹ = {!   !}
Yonedaᵐ .Uᴹ = {!   !}
Yonedaᵐ .U[]ᴹ = {!   !}

{-
_≣S_ : Subˢ Γ Δ → Subˢ Γ Δ → Set
σˢ ≣S τˢ = ∀{Θ} → y σˢ {Θ} ≡ y τˢ

≣S→≡ : {σˢ σ'ˢ : Subˢ Γ Δ} → σˢ ≣S σ'ˢ → σˢ ≡ σ'ˢ
≣S→≡ σˢ≣σ'ˢ i = record
  { y = σˢ≣σ'ˢ i
  ; natˢ = λ τ δ → {! σˢ≣σ'ˢ i  !}
  }

tyOfˢ : Tmˢ Γ → Tyˢ Γ
tyOfˢ (tmˢ _ t τ) = tyˢ _ (tyOf t) τ

Strictᵃ : Motive _ _ _ _
Strictᵃ = record
  { Ctxᴬ = Ctx
  ; Tyᴬ = Tyˢ
  ; Subᴬ = Subˢ
  ; Tmᴬ = Tmˢ
  ; tyOfᴬ = tyOfˢ
  ; Tyᴬ-is-set = λ Aˢ A'ˢ p p' → UIP p p'
  }

variable
  Aˢ Bˢ : Tyˢ Γ
  σˢ τˢ : Subˢ Γ Δ
  tˢ t'ˢ sˢ : Tmˢ Γ

_[_]ˢ : Tyˢ Δ → Subˢ Γ Δ → Tyˢ Γ
(tyˢ _ A τ) [ σˢ ]ˢ = tyˢ _ A (τ ∘ ⌜ σˢ ⌝subˢ)

_[_]tˢ : Tmˢ Δ → Subˢ Γ Δ → Tmˢ Γ
(tmˢ _ t τ) [ σˢ ]tˢ = tmˢ _ t (τ ∘ ⌜ σˢ ⌝subˢ)

∅Sˢ : Subˢ Γ ∅
∅Sˢ = subˢ (λ _ → ∅) λ τ _ → sym (η∅ (∅ ∘ τ))

_,_∶[_]ˢ
  : (σˢ : Subˢ Γ Δ)(tˢ : Tmˢ Γ){Aˢ : Tyˢ Δ} → tyOfˢ tˢ ≣ Aˢ [ σˢ ]ˢ
  → Subˢ Γ (Δ ,ˢ Aˢ)
_,_∶[_]ˢ {Γ} σˢ (tmˢ _ t τ) {tyˢ _ A θ} p = record
  { y = λ γ → y σˢ γ , t [ τ ] [ γ ] ∶[ q ]
  ; natˢ = λ τ' δ →
      y σˢ (δ ∘ τ') , t [ τ ] [ δ ∘ τ' ] ∶[ q ]
        ≡⟨ cong,∶[] q
            (cong (λ A' → A' [ δ ] [ τ' ]) p
            ∙ cong (_[ τ' ]) ([∘]T _ _ _)
            ∙ [∘]T _ _ _
            ∙ (λ i → A [ assocS δ (y σˢ idS) θ i ∘ τ' ])
            ∙ cong (A [_]) (assocS _ _ _)
            ∙ sym ([∘]T _ _ _)
            ∙ (λ i → A [ θ ] [ natˢ-id σˢ δ i ∘ τ' ]))
            (natˢ σˢ τ' δ)
            (sym ([∘]t _ _ _)) ⟩
      y σˢ δ ∘ τ' , t [ τ ] [ δ ] [ τ' ] ∶[ _ ]
        ≡⟨ sym (,∘ (y σˢ δ) (t [ τ ] [ δ ]) τ' q _) ⟩
      (y σˢ δ , t [ τ ] [ δ ] ∶[ q ]) ∘ τ'
        ∎
  }
  where
    q : {γ : Sub Θ Γ} → _≡_ {A = Ty Θ} (tyOf t [ τ ] [ γ ]) (A [ θ ] [ y σˢ γ ])
    q {γ = γ} =
      tyOf t [ τ ] [ γ ]
        ≡⟨ cong (_[ γ ]) p ⟩
      A [ θ ∘ y σˢ idS ] [ γ ]
        ≡[ i ]⟨ [∘]T A (y σˢ idS) θ (~ i) [ γ ] ⟩
      A [ θ ] [ y σˢ idS ] [ γ ]
        ≡⟨ [∘]T _ _ _ ⟩
      A [ θ ] [ y σˢ idS ∘ γ ]
        ≡[ i ]⟨ A [ θ ] [ (sym (natˢ σˢ γ idS) ∙ cong (y σˢ) (idS∘ γ)) i ] ⟩
      A [ θ ] [ y σˢ γ ]
        ∎

idSˢ : Subˢ Γ Γ
idSˢ = subˢ (λ γ → γ) λ _ _ → refl

_∘ˢ_ : Subˢ Δ Θ → Subˢ Γ Δ → Subˢ Γ Θ
σˢ ∘ˢ τˢ = record
  { y = λ γ → y σˢ (y τˢ γ)
  ; natˢ = λ τ δ → cong (y σˢ) (natˢ τˢ τ δ) ∙ natˢ σˢ τ (y τˢ δ)
  }

π₁ˢ : Subˢ Γ (Δ ,ˢ Aˢ) → Subˢ Γ Δ
π₁ˢ σˢ = subˢ (λ γ → π₁ (y σˢ γ)) λ τ δ →
  cong π₁ (natˢ σˢ τ δ) ∙ π₁∘ (y σˢ δ) τ 

π₂ˢ : Subˢ Γ (Δ ,ˢ Aˢ) → Tmˢ Γ
π₂ˢ σˢ = tmˢ _ (π₂ ⌜ σˢ ⌝subˢ) idS

tyOfπ₂ˢ
  : {Aˢ : Tyˢ Δ}(σˢ : Subˢ Γ (Δ ,ˢ Aˢ))
  → tyOfˢ (π₂ˢ {Aˢ = Aˢ} σˢ) ≣ Aˢ [ π₁ˢ σˢ ]ˢ
tyOfπ₂ˢ σˢ = {!   !}

idS∘ˢ_ : (σˢ : Subˢ Γ Δ) → idSˢ {Δ} ∘ˢ σˢ ≡ σˢ
idS∘ˢ σˢ = λ i → subˢ (λ γ → y σˢ γ) λ τ δ →
  UIP {x = y σˢ (δ ∘ τ)} {y σˢ δ ∘ τ}
      (cong (y idSˢ) (natˢ σˢ τ δ) ∙ natˢ idSˢ τ (y σˢ δ))
      (σˢ .natˢ τ δ)
       i

_∘idSˢ : (σˢ : Subˢ Γ Δ) → σˢ ∘ˢ idSˢ ≡ σˢ
σˢ ∘idSˢ = λ i → subˢ (λ γ → y σˢ γ) λ τ δ →
  UIP {x = y σˢ (δ ∘ τ)} {y σˢ δ ∘ τ}
      (cong (y σˢ) (natˢ idSˢ τ δ) ∙ natˢ σˢ τ (y idSˢ δ))
      (σˢ .natˢ τ δ)
       i

assocSˢ
  : (σˢ : Subˢ Γ Δ)(τˢ : Subˢ Δ Θ)(γˢ : Subˢ Θ Ξ)
  → (γˢ ∘ˢ τˢ) ∘ˢ σˢ ≡ γˢ ∘ˢ (τˢ ∘ˢ σˢ)
assocSˢ σˢ τˢ γˢ i = record
  { y = λ γ → y γˢ (y τˢ (y σˢ γ))
  ; natˢ = λ τ δ →
      UIP {x = y γˢ (y τˢ (y σˢ (δ ∘ τ)))} {y γˢ (y τˢ (y σˢ δ)) ∘ τ}
          (cong (λ γ → y γˢ (y τˢ γ)) (natˢ σˢ τ δ) ∙ cong (y γˢ) (natˢ τˢ τ (y σˢ δ)) ∙ natˢ γˢ τ (y τˢ (y σˢ δ)))
          (cong (y γˢ) (cong (y τˢ) (natˢ σˢ τ δ) ∙ natˢ τˢ τ (y σˢ δ)) ∙ natˢ γˢ τ (y τˢ (y σˢ δ)))
          i
  }

[idS]ˢ : Aˢ ≣ Aˢ [ idSˢ ]ˢ
[idS]ˢ {Aˢ = tyˢ _ A τ} i = A [ (τ ∘idS) (~ i) ]

βπ₁ˢ
  : (σˢ : Subˢ Γ Δ)(tˢ : Tmˢ Γ){Aˢ : Tyˢ Δ}(p : tyOfˢ tˢ ≣ Aˢ [ σˢ ]ˢ)
  → π₁ˢ (σˢ , tˢ ∶[ p ]ˢ) ≡ σˢ
βπ₁ˢ σˢ tˢ p = {!   !}

-}