open import Prelude
open import Theory.SC.QIIRT-tyOf.Model

module Theory.SC.QIIRT-tyOf.Model.Yoneda
  (C : SC ℓ₁ ℓ₂ ℓ₃ ℓ₄) where

open SC C
open Var

record Subʸ (Γ Δ : Ctx) : Set (ℓ-max ℓ₁ ℓ₃) where
  constructor _,_
  field
    y : ∀{Θ} → Sub Θ Γ → Sub Θ Δ
    natʸ : {Ξ Θ : Ctx} (τ : Sub Ξ Θ) (δ : Sub Θ Γ)
         → {δ' : Sub Ξ Γ} → (δ ∘ τ) ≡ δ' → y δ ∘ τ ≡ y δ'

  Subʸ-τidS∘
    : ∀{Ξ} (γ : Sub Ξ Γ)
    → y idS ∘ γ ≡ y γ
  Subʸ-τidS∘ γ = natʸ γ idS (idS∘ γ)
open Subʸ

Subʸ-is-set : ∀{Γ Δ} → isSet (Subʸ Γ Δ)
Subʸ-is-set {Γ} {Δ} (σ , pσ) (σ' , pσ') p q i j = record
  { y = λ γᴹ → isSet→SquareP (λ _ _ → Sub-is-set) refl refl (λ k → y (p k) γᴹ) (λ k → y (q k) γᴹ) j i
  ; natʸ = λ {Ξ} {Θ} τ δ {δ'} r k → isGroupoid→CubeP (λ _ _ _ → Sub Ξ Δ)
                                                     (λ j i → isSet→SquareP (λ _ _ → Sub-is-set) refl refl (λ k → y (p k) δ)  (λ k → y (q k) δ) j i ∘ τ)
                                                     (λ j i → isSet→SquareP (λ _ _ → Sub-is-set) refl refl (λ k → y (p k) δ') (λ k → y (q k) δ') j i)
                                                     (λ k j → pσ τ δ r k)
                                                     (λ k j → pσ' τ δ r k)
                                                     (λ k j → natʸ (p j) τ δ r k)
                                                     (λ k j → natʸ (q j) τ δ r k)
                                                     (isSet→isGroupoid Sub-is-set) k j i
  }

_≡ʸ_ : Subʸ Γ Δ → Subʸ Γ Δ → Set (ℓ-max ℓ₁ ℓ₃)
_≡ʸ_ {Γ} {Δ} (σ , _) (σ' , _) = _≡_ {A = {Θ : Ctx} → Sub Θ Γ → Sub Θ Δ} σ σ'
-- ∀{Θ} {γᴹ : Subᴬ Θ _} → σ γᴹ ≡ σ' γᴹ

≡ʸ→≡ : {σʸ σ'ʸ : Subʸ Γ Δ} → σʸ ≡ʸ σ'ʸ → σʸ ≡ σ'ʸ
≡ʸ→≡  {σʸ = σʸ} {σ'ʸ} eqʸ i = record
  { y = eqʸ i
  ; natʸ = λ τ δ {δ'} r j →
      isSet→SquareP (λ i j → Sub-is-set) (λ i → eqʸ i δ ∘ τ) (λ i → eqʸ i δ') (natʸ σʸ τ δ {δ'} r) (natʸ σ'ʸ τ δ {δ'} r) j i
  }

infixr 2 step-≡ʸ

step-≡ʸ : ∀{Γ Δ σ'ʸ σ''ʸ}(σʸ : Subʸ Γ Δ) → σ'ʸ ≡ σ''ʸ → σʸ ≡ʸ σ'ʸ → σʸ ≡ σ''ʸ
step-≡ʸ σʸ p pʸ = ≡ʸ→≡ pʸ ∙ p

syntax step-≡ʸ σ τ p = σ ≡ʸ⟨ p ⟩ τ

_∘ʸ_ : ∀{Γ Δ Θ} → Subʸ Δ Θ → Subʸ Γ Δ → Subʸ Γ Θ
(σ , pσ) ∘ʸ (σ' , pσ') = (λ γ → σ (σ' γ)) , λ τ δ {δ'} r → pσ τ (σ' δ) (pσ' τ δ r)


[∘]Tʸ
  : (A : Ty Θ)(σʸ : Subʸ Γ Δ)(τʸ : Subʸ Δ Θ)
  → A [ y τʸ idS ]T [ y σʸ idS ]T ≡ A [ y (τʸ ∘ʸ σʸ) idS ]T
[∘]Tʸ A σʸ τʸ = [∘]T A (y σʸ idS) (y τʸ idS) ∙ cong (A [_]T) (Subʸ-τidS∘ τʸ (y σʸ idS))


_,ʸ_∶[_]
  : (σʸ : Subʸ Γ Δ) (t : Tm Γ) → tyOf t ≡ A [ σʸ .y idS ]T
  → Subʸ Γ (Δ ,C A)
_,ʸ_∶[_] {Γ} {Δ} {A} (σ , pσ) t p =   (λ γ → σ γ , t [ γ ]t ∶[ tyOf[] ∙ cong _[ γ ]T p ∙ [∘]T A γ (σ idS) ∙ cong (A [_]T) (Subʸ-τidS∘ (σ , pσ) γ) ])
                                    , λ τ δ {δ'} r → let q = (tyOf[] ∙ cong _[ τ ]T (tyOf[] ∙ cong _[ δ ]T p ∙ [∘]T A δ (σ idS) ∙ cong (A [_]T) (Subʸ-τidS∘ (σ , pσ) δ)) ∙ [∘]T A τ (σ δ))
                                                     in  ,∘ (σ δ) (t [ δ ]t) τ _ q
                                                       ∙ cong,∶[] q (tyOf[] ∙ cong _[ δ' ]T p ∙ [∘]T A δ' (σ idS) ∙ cong (A [_]T) (Subʸ-τidS∘ (σ , pσ) δ'))
                                                                    (pσ τ δ r)
                                                                    ([∘]t t τ δ ∙ cong (t [_]t) r)

よM : Motive
よM = record
  { Ctx  = Ctx
  ; Ty   = Ty
  ; Sub  = Subʸ
  ; Tm   = Tm
  ; tyOf = tyOf
  ; Ty-is-set  = Ty-is-set
  ; Sub-is-set = Subʸ-is-set
  ; Tm-is-set  = Tm-is-set
  }

よIsSC : IsSC よM
よIsSC .IsSC.∅    = ∅
よIsSC .IsSC._,C_ = _,C_
よIsSC .IsSC._[_]T A (σ , _) = A [ σ idS ]T
よIsSC .IsSC._[_]t t (σ , _) = t [ σ idS ]t
よIsSC .IsSC.tyOf[]   = tyOf[]
よIsSC .IsSC.∅S       = (λ _ → ∅S) , λ τ δ r → η∅ _
よIsSC .IsSC._,_∶[_]  = _,ʸ_∶[_]
よIsSC .IsSC.idS      = (λ γ → γ) , λ τ δ r → r
よIsSC .IsSC._∘_      = _∘ʸ_
よIsSC .IsSC.π₁ (σ , pσ) = (λ γ → π₁ (σ γ)) ,
  λ τ δ r → sym (π₁∘ (σ δ) τ) ∙ cong π₁ (pσ _ _ r)
よIsSC .IsSC.π₂ (σ , pσ) = π₂ (σ idS)
よIsSC .IsSC.tyOfπ₂ (σ , pσ) = tyOfπ₂ (σ idS)
よIsSC .IsSC.idS∘_ (σ , pσ) = refl
よIsSC .IsSC._∘idS (σ , pσ) = refl
よIsSC .IsSC.assocS (σ , pσ) (τ , pτ) (θ , pθ) = refl
よIsSC .IsSC.[idS]T = [idS]T
よIsSC .IsSC.[∘]T   = [∘]Tʸ
よIsSC .IsSC.,∘ {A = A} σʸ@(σ , pσ) t τʸ p q = ≡ʸ→≡ λ i γ →
  let r = tyOf[] ∙ (λ j → p j [ y τʸ γ ]T) ∙ [∘]T A (y τʸ γ) (σ idS) ∙ (λ j → A [ Subʸ-τidS∘ σʸ (y τʸ γ) j ]T)
      r' = tyOf[] ∙ (λ j → q j [ γ ]T) ∙ [∘]T A γ (y ((σ , pσ) ∘ʸ τʸ) idS) ∙ (cong (A [_]T) (pσ γ (y τʸ idS) (Subʸ-τidS∘ τʸ γ)))
  in cong,∶[] r r' refl (cong (t [_]t) (sym (Subʸ-τidS∘ τʸ γ)) ∙ sym ([∘]t _ _ _)) i
よIsSC .IsSC.ηπ {A = A} σʸ@(σ , pσ) = ≡ʸ→≡ λ i γ →
  let p = tyOf[] ∙ cong _[ γ ]T (tyOfπ₂ (σ idS)) ∙ [∘]T A γ (π₁ (σ idS)) ∙ cong (A [_]T) (sym (π₁∘ (σ idS) γ) ∙ cong π₁ (Subʸ-τidS∘ σʸ γ))
  in (ηπ (σ γ) ∙ cong,∶[] (tyOfπ₂ (σ γ)) p refl (sym (cong π₂ (Subʸ-τidS∘ (σ , pσ) γ)) ∙ π₂∘ (σ idS) γ)) i
よIsSC .IsSC.η∅ (σ , pσ) = ≡ʸ→≡ λ i γ → η∅ (σ γ) i
よIsSC .IsSC.βπ₁ {A = A} (σ , pσ) t p = ≡ʸ→≡ λ i γ →
  let p = tyOf[] ∙ (λ j → p j [ γ ]T) ∙ [∘]T A γ (σ idS) ∙ cong (A [_]T) (Subʸ-τidS∘ (σ , pσ) γ)
  in βπ₁ (σ γ) (t [ γ ]t) p i
よIsSC .IsSC.βπ₂ (σ , pσ) t p = βπ₂ (σ idS) _ _ ∙ sym ([idS]t t)
よIsSC .IsSC.[idS]t t = [idS]t t
よIsSC .IsSC.[∘]t   t (σ , _) τʸ@(τ , pτ) = [∘]t t (σ idS) (τ idS) ∙ cong (t [_]t) (Subʸ-τidS∘ τʸ (σ idS))
よIsSC .IsSC.U   = U
よIsSC .IsSC.U[] = U[]

よ : SC _ _ _ _
よ = record { mot = よM ; isSC = よIsSC }
