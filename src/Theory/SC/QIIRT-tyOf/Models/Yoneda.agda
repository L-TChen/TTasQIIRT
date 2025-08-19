open import Prelude
open import Theory.SC.QIIRT-tyOf.Model

module Theory.SC.QIIRT-tyOf.Models.Yoneda
  (C : SC ℓ₁ ℓ₂ ℓ₃ ℓ₄) where

open SC C
open GVars

record Subʸ (Γ Δ : Ctx) : Set (ℓ-max ℓ₁ ℓ₃) where
  inductive
  eta-equality
  constructor _,_
  field
    y : ∀{Θ} → Sub Θ Γ → Sub Θ Δ
    natʸ : {Ξ Θ : Ctx} (τ : Sub Ξ Θ) (δ : Sub Θ Γ) → y δ ∘ τ ≡ y (δ ∘ τ)

  Subʸ-τidS∘
    : ∀{Ξ} (γ : Sub Ξ Γ)
    → y idS ∘ γ ≡ y γ
  Subʸ-τidS∘ γ = natʸ γ idS ∙ cong y (idS∘ γ)
open Subʸ

--  Subʸ-is-set : ∀{Γ Δ} → isSet (Subʸ Γ Δ)
--  Subʸ-is-set {Γ} {Δ} (σ , pσ) (σ' , pσ') p q i j = record
--    { y = λ γᴹ → isSet→SquareP (λ _ _ → Subᴬ-is-set) refl refl (λ k → y (p k) γᴹ) (λ k → y (q k) γᴹ) j i
--    ; natʸ = λ {Ξ} {Θ} τ δ k →
--      isGroupoid→CubeP (λ _ _ _ → Sub Ξ Δ)
--        (λ j i → isSet→SquareP (λ _ _ _ _ → UIP) refl refl (λ k → y (p k) δ) (λ k → y (q k) δ) j i ∘ τ)
--        (λ j i → isSet→SquareP (λ _ _ _ _ → UIP) refl refl (λ k → y (p k) (δ ∘ τ)) (λ k → y (q k) (δ ∘ τ)) j i)
--        (λ k _ → pσ τ δ k)
--        (λ k _ → pσ' τ δ k)
--        (λ k j → natʸ (p j) τ δ k)
--        (λ k j → natʸ (q j) τ δ k)
--        (isSet→isGroupoid UIP') k j i
--    }

_≡ʸ_ : Subʸ Γ Δ → Subʸ Γ Δ → Set (ℓ-max ℓ₁ ℓ₃)
_≡ʸ_ {Γ} {Δ} (σ , _) (σ' , _) = _≡_ {A = {Θ : Ctx} → Sub Θ Γ → Sub Θ Δ} σ σ'
-- ∀{Θ} {γᴹ : Subᴬ Θ _} → σ γᴹ ≡ σ' γᴹ

≡ʸ→≡ : {σʸ σ'ʸ : Subʸ Γ Δ} → σʸ ≡ʸ σ'ʸ → σʸ ≡ σ'ʸ
≡ʸ→≡  {σʸ = σʸ} {σ'ʸ} eqʸ i = record
  { y = eqʸ i
  ; natʸ = λ τ δ j →
      isSet→SquareP (λ _ _ → UIP')
        (λ i → eqʸ i δ ∘ τ)
        (λ i → eqʸ i (δ ∘ τ))
        (natʸ σʸ τ δ)
        (natʸ σ'ʸ τ δ)
        j i
  }

infixr 2 step-≡ʸ

step-≡ʸ : ∀{Γ Δ σ'ʸ σ''ʸ}(σʸ : Subʸ Γ Δ) → σ'ʸ ≡ σ''ʸ → σʸ ≡ʸ σ'ʸ → σʸ ≡ σ''ʸ
step-≡ʸ σʸ p pʸ = ≡ʸ→≡ pʸ ∙ p

syntax step-≡ʸ σ τ p = σ ≡ʸ⟨ p ⟩ τ

_∘ʸ_ : ∀{Γ Δ Θ} → Subʸ Δ Θ → Subʸ Γ Δ → Subʸ Γ Θ
(σ , pσ) ∘ʸ (σ' , pσ') = (λ γ → σ (σ' γ)) , λ τ δ → pσ τ _ ∙ cong σ (pσ' _ _)

[∘]Tʸ
  : (A : Ty Θ)(σʸ : Subʸ Γ Δ)(τʸ : Subʸ Δ Θ)
  → A [ y τʸ idS ]T [ y σʸ idS ]T ≡ A [ y (τʸ ∘ʸ σʸ) idS ]T
[∘]Tʸ A σʸ τʸ = [∘]T A (y σʸ idS) (y τʸ idS) ∙ cong (A [_]T) (Subʸ-τidS∘ τʸ (y σʸ idS))

_,ʸ_∶[_]
  : (σʸ : Subʸ Γ Δ) (t : Tm Γ) → tyOf t ≡ A [ σʸ .y idS ]T
  → Subʸ Γ (Δ ,C A)
_,ʸ_∶[_] {Γ} {Δ} {A} (σ , pσ) t p = 
  (λ γ → σ γ , t [ γ ]t ∶[ tyOf[] ∙ (λ i → p i [ γ ]T) ∙ [∘]T A γ (σ idS) ∙ (λ i → A [ (pσ γ idS ∙ cong σ (idS∘ γ)) i ]T)  ])
  , λ τ δ →
    let q = tyOf[] ∙ cong _[ τ ]T (tyOf[] ∙ (λ i → p i [ δ ]T) ∙ [∘]T A δ (σ idS) ∙ cong (A [_]T) (Subʸ-τidS∘ (σ , pσ) δ)) ∙ [∘]T A τ (σ δ) in 
  ,∘ (σ δ) (t [ δ ]t) τ
    (tyOf[] ∙ (λ i → p i [ δ ]T) ∙ [∘]T A δ (σ idS) ∙ cong (A [_]T) (Subʸ-τidS∘ (σ , pσ) δ)) q
    ∙ cong,∶[] q (tyOf[] ∙ cong _[ δ ∘ τ ]T p ∙ [∘]T A (δ ∘ τ) (σ idS) ∙ cong (A [_]T) (pσ (δ ∘ τ) idS ∙ cong σ (idS∘ _)))
        (pσ τ δ) ([∘]t t τ δ) 

よM : Motive
よM = record
  { Ctx  = Ctx
  ; Ty   = Ty
  ; Sub  = Subʸ
  ; Tm   = Tm
  ; tyOf = tyOf
--    ; Tyᴬ-is-set  = Tyᴬ-is-set
--    ; Motive.Subᴬ-is-set = Subʸ-is-set
--    ; Motive.Tmᴬ-is-set  = Tmᴬ-is-set
    }

よIsSC : IsSC よM
よIsSC .IsSC.∅    = ∅
よIsSC .IsSC._,C_ = _,C_
よIsSC .IsSC._[_]T A (σ , _) = A [ σ idS ]T
よIsSC .IsSC._[_]t t (σ , _) = t [ σ idS ]t
よIsSC .IsSC.tyOf[]   = tyOf[]
よIsSC .IsSC.∅S       = (λ _ → ∅S) , λ τ δ → η∅ _
よIsSC .IsSC._,_∶[_]  = _,ʸ_∶[_]
よIsSC .IsSC.idS      = (λ γ → γ) , λ τ δ → refl
よIsSC .IsSC._∘_      = _∘ʸ_
よIsSC .IsSC.π₁ (σ , pσ) = (λ γ → π₁ (σ γ)) ,
  λ τ δ → sym (π₁∘ (σ δ) τ) ∙ cong π₁ (pσ _ _)
よIsSC .IsSC.π₂ (σ , pσ) = π₂ (σ idS)   
よIsSC .IsSC.tyOfπ₂ (σ , pσ) = tyOfπ₂ (σ idS)
よIsSC .IsSC.idS∘_ (σ , pσ) = ≡ʸ→≡ refl
よIsSC .IsSC._∘idS (σ , pσ) = ≡ʸ→≡ refl
よIsSC .IsSC.assocS (σ , pσ) (τ , pτ) (θ , pθ) = ≡ʸ→≡ refl
よIsSC .IsSC.[idS]T = [idS]T
よIsSC .IsSC.[∘]T = [∘]Tʸ
よIsSC .IsSC.,∘ {A = A} (σ , pσ) t τʸ p q = ≡ʸ→≡ λ i γ →
  let r = tyOf[] ∙ (λ j → p j [ y τʸ γ ]T) ∙ [∘]T A (y τʸ γ) (σ idS) ∙ (λ j → A [ (pσ (y τʸ γ) idS ∙ (λ k → σ ((idS∘ (y τʸ γ)) k))) j ]T)
      r' = tyOf[] ∙ (λ j → q j [ γ ]T) ∙ [∘]T A γ (y ((σ , pσ) ∘ʸ τʸ) idS) ∙ (λ j → A [ (natʸ ((σ , pσ) ∘ʸ τʸ) γ idS ∙ (λ k → y ((σ , pσ) ∘ʸ τʸ) ((idS∘ γ) k))) j ]T)
  in cong,∶[] r r' refl (cong (t [_]t) (sym (Subʸ-τidS∘ τʸ γ)) ∙ sym ([∘]t _ _ _)) i
よIsSC .IsSC.ηπ {A = A} (σ , pσ) = ≡ʸ→≡ λ i γ →
  let p = tyOf[] ∙ (λ j → tyOfπ₂ (σ idS) j [ γ ]T) ∙ [∘]T A γ (π₁ (σ idS)) ∙ (λ j → A [ (((λ k → π₁∘ (σ idS) γ (~ k)) ∙ (λ k → π₁ (pσ γ idS k))) ∙ (λ k → π₁ (σ ((idS∘ γ) k)))) j ]T)
  in (ηπ (σ γ) ∙ cong,∶[] (tyOfπ₂ (σ γ)) p refl (sym (cong π₂ (Subʸ-τidS∘ (σ , pσ) γ)) ∙ π₂∘ (σ idS) γ)) i
よIsSC .IsSC.η∅ (σ , pσ) = ≡ʸ→≡ λ i γ → η∅ (σ γ) i
よIsSC .IsSC.βπ₁ {A = A} (σ , pσ) t p = ≡ʸ→≡ λ i γ →
  let p = tyOf[] ∙ (λ j → p j [ γ ]T) ∙ [∘]T A γ (σ idS) ∙ (λ j → A [ (pσ γ idS ∙ (λ k → σ ((idS∘ γ) k))) j ]T)
  in βπ₁ (σ γ) (t [ γ ]t) p i
よIsSC .IsSC.βπ₂ (σ , pσ) t p = βπ₂ (σ idS) _ _ ∙ sym ([idS]t t)
よIsSC .IsSC.[idS]t t = [idS]t t
よIsSC .IsSC.[∘]t   t (σ , _) (τ , pτ) = [∘]t t (σ idS) (τ idS) ∙ cong (t [_]t) (pτ (σ idS) idS ∙ cong τ (idS∘ _))
よIsSC .IsSC.U   = U
よIsSC .IsSC.U[] = U[]

よ : SC _ _ _ _
よ = record { mot = よM ; isSC = よIsSC }
