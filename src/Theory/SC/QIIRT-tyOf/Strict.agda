module Theory.SC.QIIRT-tyOf.Strict where

open import Prelude
open import Theory.SC.QIIRT-tyOf.Syntax
open import Theory.SC.QIIRT-tyOf.Model

cong,∶[]
  : {σ σ' : Sub Γ Δ}{t t' : Tm Γ}
  → (p : tyOf t ≡ A [ σ ])(p' : tyOf t' ≡ A [ σ' ])
  → σ ≡ σ' → t ≡ t'
  → (σ , t ∶[ p ]) ≡ (σ' , t' ∶[ p' ])
cong,∶[] {A = A} p p' eqσ eqt =
  cong₃ _,_∶[_] eqσ eqt (isSet→SquareP (λ _ _ → Ty-is-set) p p' (cong tyOf eqt) (cong (A [_]) eqσ))

open Motive

よᵃ : Motive _ _ _ _
よᵃ .Ctxᴬ       = Ctx
よᵃ .Tyᴬ        = Ty
よᵃ .Subᴬ       = λ Γ Δ → Σ[ θ ∈ (∀ {Θ} → Sub Θ Γ → Sub Θ Δ) ]
  ({Ξ Θ : Ctx} (τ : Sub Ξ Θ) (δ : Sub Θ Γ) → θ δ ∘ τ ≡ θ (δ ∘ τ))
よᵃ .Tmᴬ        = Tm
よᵃ .tyOfᴬ      = tyOf
よᵃ .Tyᴬ-is-set = Ty-is-set

open SCᴹ
よᵐ : SCᴹ よᵃ
よᵐ .∅ᴹ          = ∅
よᵐ ._,ᴹ_        = _,_
よᵐ ._[_]Tᴹ A (σ , _) = A [ σ idS ]
よᵐ ._[_]tᴹ t (σ , _) = t [ σ idS ]
よᵐ .tyOf[]ᴹ     = refl   
よᵐ .∅Sᴹ         = (λ _ → ∅) , λ τ δ → η∅ _
よᵐ ._,ᴹ_∶[_] {Aᴹ = A} (σ , pσ) t p =
  (λ γ → σ γ , t [ γ ] ∶[ cong _[ γ ] p ∙ [∘]T A γ (σ idS) ∙ cong (A [_]) (pσ γ idS ∙ cong σ (idS∘ γ)) ]) , λ τ δ → {!!}
よᵐ .idSᴹ        = (λ γ → γ) , λ τ δ → refl
よᵐ ._∘ᴹ_ (σ , pσ) (τ , pτ) = (λ γ → σ (τ γ)) ,
  λ τ δ → pσ τ _ ∙ cong σ (pτ _ _)
よᵐ .π₁ᴹ (σ , pσ) = (λ γ → π₁ (σ γ)) ,
  λ τ δ → sym (π₁∘ _ _) ∙ cong π₁ (pσ _ _)
よᵐ .π₂ᴹ (σ , pσ) = π₂ (σ idS)   
よᵐ .tyOfπ₂ᴹ (σ , pσ) = refl   
よᵐ .idS∘ᴹ_ (σ , pσ) i = σ ,
  λ τ δ → Sub-is-set _ _ (refl ∙ pσ τ δ) (pσ _ _) i 
よᵐ ._∘idSᴹ (σ , pσ) i = σ ,
  λ τ δ → Sub-is-set _ _ (pσ τ δ ∙ refl) (pσ τ δ) i
よᵐ .assocSᴹ (σ , pσ) (τ , pτ) (θ , pθ) i = (λ γ → θ (τ (σ γ))) ,
  λ τ' δ → Sub-is-set _ _ ((λ i₁ →
            hcomp
            (doubleComp-faces (λ _ → θ (τ (σ δ)) ∘ τ')
             (λ i₂ → θ (τ (pσ τ' δ i₂))) i₁)
            (hcomp
             (doubleComp-faces (λ _ → θ (τ (σ δ)) ∘ τ')
              (λ i₂ → θ (pτ τ' (σ δ) i₂)) i₁)
             (pθ τ' (τ (σ δ)) i₁)))) ((λ i₁ →
            hcomp
            (doubleComp-faces (λ _ → θ (τ (σ δ)) ∘ τ')
             (λ i₂ →
                θ
                (hcomp
                 (doubleComp-faces (λ _ → τ (σ δ) ∘ τ') (λ i₃ → τ (pσ τ' δ i₃)) i₂)
                 (pτ τ' (σ δ) i₂)))
             i₁)
            (pθ τ' (τ (σ δ)) i₁))) i
よᵐ .[idS]Tᴹ = [idS]T  
よᵐ .[∘]Tᴹ A (σ , pσ) (τ , pτ) = [∘]T A (σ idS) (τ idS) ∙
  cong (A [_]) (pτ (σ idS) idS ∙ cong τ (idS∘ _))
よᵐ .,∘ᴹ (σ , pσ) t (τ , pτ) p q = {!   !}
よᵐ .ηπᴹ (σ , pσ) i = {!!} , {!!}   
よᵐ .η∅ᴹ (σ , pσ) i = (λ γ → η∅ (σ γ) i) ,
  λ τ δ → {! !}
よᵐ .βπ₁ᴹ (σ , pσ) t p = {!   !}
よᵐ .βπ₂ᴹ (σ , pσ) t p = {! βπ₂ (σ idS) t ? ? !}
よᵐ .[idS]tᴹ t = [idS]t t
よᵐ .[∘]tᴹ   t (σ , _) (τ , pτ) = [∘]t t (σ idS) (τ idS) ∙
  cong (t [_]) (pτ (σ idS) idS ∙ cong τ (idS∘ σ idS))   
よᵐ .Uᴹ   = U   
よᵐ .U[]ᴹ = U[]   

-- {-
-- _≣S_ : Subˢ Γ Δ → Subˢ Γ Δ → Set
-- σˢ ≣S τˢ = ∀{Θ} → y σˢ {Θ} ≡ y τˢ

-- ≣S→≡ : {σˢ σ'ˢ : Subˢ Γ Δ} → σˢ ≣S σ'ˢ → σˢ ≡ σ'ˢ
-- ≣S→≡ σˢ≣σ'ˢ i = record
--   { y = σˢ≣σ'ˢ i
--   ; natˢ = λ τ δ → {! σˢ≣σ'ˢ i  !}
--   }

-- tyOfˢ : Tmˢ Γ → Tyˢ Γ
-- tyOfˢ (tmˢ _ t τ) = tyˢ _ (tyOf t) τ

-- Strictᵃ : Motive _ _ _ _
-- Strictᵃ = record
--   { Ctxᴬ = Ctx
--   ; Tyᴬ = Tyˢ
--   ; Subᴬ = Subˢ
--   ; Tmᴬ = Tmˢ
--   ; tyOfᴬ = tyOfˢ
--   ; Tyᴬ-is-set = λ Aˢ A'ˢ p p' → UIP p p'
--   }

-- variable
--   Aˢ Bˢ : Tyˢ Γ
--   σˢ τˢ : Subˢ Γ Δ
--   tˢ t'ˢ sˢ : Tmˢ Γ

-- _[_]ˢ : Tyˢ Δ → Subˢ Γ Δ → Tyˢ Γ
-- (tyˢ _ A τ) [ σˢ ]ˢ = tyˢ _ A (τ ∘ ⌜ σˢ ⌝subˢ)

-- _[_]tˢ : Tmˢ Δ → Subˢ Γ Δ → Tmˢ Γ
-- (tmˢ _ t τ) [ σˢ ]tˢ = tmˢ _ t (τ ∘ ⌜ σˢ ⌝subˢ)

-- ∅Sˢ : Subˢ Γ ∅
-- ∅Sˢ = subˢ (λ _ → ∅) λ τ _ → sym (η∅ (∅ ∘ τ))

-- _,_∶[_]ˢ
--   : (σˢ : Subˢ Γ Δ)(tˢ : Tmˢ Γ){Aˢ : Tyˢ Δ} → tyOfˢ tˢ ≣ Aˢ [ σˢ ]ˢ
--   → Subˢ Γ (Δ ,ˢ Aˢ)
-- _,_∶[_]ˢ {Γ} σˢ (tmˢ _ t τ) {tyˢ _ A θ} p = record
--   { y = λ γ → y σˢ γ , t [ τ ] [ γ ] ∶[ q ]
--   ; natˢ = λ τ' δ →
--       y σˢ (δ ∘ τ') , t [ τ ] [ δ ∘ τ' ] ∶[ q ]
--         ≡⟨ cong,∶[] q
--             (cong (λ A' → A' [ δ ] [ τ' ]) p
--             ∙ cong (_[ τ' ]) ([∘]T _ _ _)
--             ∙ [∘]T _ _ _
--             ∙ (λ i → A [ assocS δ (y σˢ idS) θ i ∘ τ' ])
--             ∙ cong (A [_]) (assocS _ _ _)
--             ∙ sym ([∘]T _ _ _)
--             ∙ (λ i → A [ θ ] [ natˢ-id σˢ δ i ∘ τ' ]))
--             (natˢ σˢ τ' δ)
--             (sym ([∘]t _ _ _)) ⟩
--       y σˢ δ ∘ τ' , t [ τ ] [ δ ] [ τ' ] ∶[ _ ]
--         ≡⟨ sym (,∘ (y σˢ δ) (t [ τ ] [ δ ]) τ' q _) ⟩
--       (y σˢ δ , t [ τ ] [ δ ] ∶[ q ]) ∘ τ'
--         ∎
--   }
--   where
--     q : {γ : Sub Θ Γ} → _≡_ {A = Ty Θ} (tyOf t [ τ ] [ γ ]) (A [ θ ] [ y σˢ γ ])
--     q {γ = γ} =
--       tyOf t [ τ ] [ γ ]
--         ≡⟨ cong (_[ γ ]) p ⟩
--       A [ θ ∘ y σˢ idS ] [ γ ]
--         ≡[ i ]⟨ [∘]T A (y σˢ idS) θ (~ i) [ γ ] ⟩
--       A [ θ ] [ y σˢ idS ] [ γ ]
--         ≡⟨ [∘]T _ _ _ ⟩
--       A [ θ ] [ y σˢ idS ∘ γ ]
--         ≡[ i ]⟨ A [ θ ] [ (sym (natˢ σˢ γ idS) ∙ cong (y σˢ) (idS∘ γ)) i ] ⟩
--       A [ θ ] [ y σˢ γ ]
--         ∎

-- idSˢ : Subˢ Γ Γ
-- idSˢ = subˢ (λ γ → γ) λ _ _ → refl

-- _∘ˢ_ : Subˢ Δ Θ → Subˢ Γ Δ → Subˢ Γ Θ
-- σˢ ∘ˢ τˢ = record
--   { y = λ γ → y σˢ (y τˢ γ)
--   ; natˢ = λ τ δ → cong (y σˢ) (natˢ τˢ τ δ) ∙ natˢ σˢ τ (y τˢ δ)
--   }

-- π₁ˢ : Subˢ Γ (Δ ,ˢ Aˢ) → Subˢ Γ Δ
-- π₁ˢ σˢ = subˢ (λ γ → π₁ (y σˢ γ)) λ τ δ →
--   cong π₁ (natˢ σˢ τ δ) ∙ π₁∘ (y σˢ δ) τ 

-- π₂ˢ : Subˢ Γ (Δ ,ˢ Aˢ) → Tmˢ Γ
-- π₂ˢ σˢ = tmˢ _ (π₂ ⌜ σˢ ⌝subˢ) idS

-- tyOfπ₂ˢ
--   : {Aˢ : Tyˢ Δ}(σˢ : Subˢ Γ (Δ ,ˢ Aˢ))
--   → tyOfˢ (π₂ˢ {Aˢ = Aˢ} σˢ) ≣ Aˢ [ π₁ˢ σˢ ]ˢ
-- tyOfπ₂ˢ σˢ = {!   !}

-- idS∘ˢ_ : (σˢ : Subˢ Γ Δ) → idSˢ {Δ} ∘ˢ σˢ ≡ σˢ
-- idS∘ˢ σˢ = λ i → subˢ (λ γ → y σˢ γ) λ τ δ →
--   UIP {x = y σˢ (δ ∘ τ)} {y σˢ δ ∘ τ}
--       (cong (y idSˢ) (natˢ σˢ τ δ) ∙ natˢ idSˢ τ (y σˢ δ))
--       (σˢ .natˢ τ δ)
--        i

-- _∘idSˢ : (σˢ : Subˢ Γ Δ) → σˢ ∘ˢ idSˢ ≡ σˢ
-- σˢ ∘idSˢ = λ i → subˢ (λ γ → y σˢ γ) λ τ δ →
--   UIP {x = y σˢ (δ ∘ τ)} {y σˢ δ ∘ τ}
--       (cong (y σˢ) (natˢ idSˢ τ δ) ∙ natˢ σˢ τ (y idSˢ δ))
--       (σˢ .natˢ τ δ)
--        i

-- assocSˢ
--   : (σˢ : Subˢ Γ Δ)(τˢ : Subˢ Δ Θ)(γˢ : Subˢ Θ Ξ)
--   → (γˢ ∘ˢ τˢ) ∘ˢ σˢ ≡ γˢ ∘ˢ (τˢ ∘ˢ σˢ)
-- assocSˢ σˢ τˢ γˢ i = record
--   { y = λ γ → y γˢ (y τˢ (y σˢ γ))
--   ; natˢ = λ τ δ →
--       UIP {x = y γˢ (y τˢ (y σˢ (δ ∘ τ)))} {y γˢ (y τˢ (y σˢ δ)) ∘ τ}
--           (cong (λ γ → y γˢ (y τˢ γ)) (natˢ σˢ τ δ) ∙ cong (y γˢ) (natˢ τˢ τ (y σˢ δ)) ∙ natˢ γˢ τ (y τˢ (y σˢ δ)))
--           (cong (y γˢ) (cong (y τˢ) (natˢ σˢ τ δ) ∙ natˢ τˢ τ (y σˢ δ)) ∙ natˢ γˢ τ (y τˢ (y σˢ δ)))
--           i
--   }

-- [idS]ˢ : Aˢ ≣ Aˢ [ idSˢ ]ˢ
-- [idS]ˢ {Aˢ = tyˢ _ A τ} i = A [ (τ ∘idS) (~ i) ]

-- βπ₁ˢ
--   : (σˢ : Subˢ Γ Δ)(tˢ : Tmˢ Γ){Aˢ : Tyˢ Δ}(p : tyOfˢ tˢ ≣ Aˢ [ σˢ ]ˢ)
--   → π₁ˢ (σˢ , tˢ ∶[ p ]ˢ) ≡ σˢ
-- βπ₁ˢ σˢ tˢ p = {!   !}

-- -}
