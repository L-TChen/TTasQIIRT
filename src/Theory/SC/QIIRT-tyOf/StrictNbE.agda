module Theory.SC.QIIRT-tyOf.StrictNbE where

open import Prelude
open import Theory.SC.QIIRT-tyOf.Syntax
  hiding
  ( Γ; Δ; Θ; Ξ
  ; A; B; C; D
  ; t; u
  ; σ; τ; δ; γ
  )
open import Theory.SC.QIIRT-tyOf.StrictSyntax
open import Theory.SC.QIIRT-tyOf.Model
open import Theory.SC.QIIRT-tyOf.Models.LocalNoQuotient
open Ty³

tr-nat
  : {X : Set} (A B : X → Set)
  → (f : ∀{x} → A x → B x) {x y : X} (p : x ≡ y) {a : A x}
  → f (transport (λ i → A (p i)) a) ≡ transport (λ i → B (p i)) (f a)
tr-nat A B f p {a} = {!    !}

-- Definition of neutral and normal forms
data NfTy (Γ : Ctxₛ) : Set where
  `U : NfTy Γ

⌜_⌝ty : NfTy Γ → Tyₛ Γ
⌜ `U ⌝ty = Uₛ

data NeSub (Γ : Ctx) : Ctx → Set where
  `∅S : NeSub Γ ∅ₛ
  `idS : NeSub Γ Γ
  `π₁ : (A : Tyₛ Δ) → NeSub Γ (Δ ,ₛ A) → NeSub Γ Δ

⌜_⌝subⁿᵉ : NeSub Γ Δ → Subₛ Γ Δ
⌜ `∅S ⌝subⁿᵉ = ∅Sₛ
⌜ `idS ⌝subⁿᵉ = idSₛ
⌜ `π₁ A σ ⌝subⁿᵉ = π₁ₛ {Aᴹ = A} ⌜ σ ⌝subⁿᵉ

data NeTm (Γ : Ctx) : Set where
  `π₂ : (A : Tyₛ Δ) → NeSub Γ (Δ ,ₛ A) → NeTm Γ

⌜_⌝tm : NeTm Γ → Tmₛ Γ
⌜ `π₂ A σⁿᵉ ⌝tm = π₂ₛ {Aᴹ = A} ⌜ σⁿᵉ ⌝subⁿᵉ

data NfSub (Γ : Ctx) : Ctx → Set
⌜_⌝subⁿᶠ : NfSub Γ Δ → Subₛ Γ Δ

data NfSub Γ where
  `ne_ : NeSub Γ Δ → NfSub Γ Δ
  _`,_∶[_]
    : (σⁿᶠ : NfSub Γ Δ)(tⁿᵉ : NeTm Γ)
    → tyOfₛ (⌜ tⁿᵉ ⌝tm) ≡ A [ ⌜ σⁿᶠ ⌝subⁿᶠ ]ₛ
    → NfSub Γ (Δ ,ₛ A)

⌜ `ne σⁿᵉ ⌝subⁿᶠ = ⌜ σⁿᵉ ⌝subⁿᵉ
⌜ _`,_∶[_] {A = A} σⁿᶠ tⁿᵉ p ⌝subⁿᶠ = _,ₛ_∶[_] {Aᴹ = A} ⌜ σⁿᶠ ⌝subⁿᶠ ⌜ tⁿᵉ ⌝tm p

-- Definitions of variables and renamings
data Var : (Γ : Ctx) → Set where
  here  : ∀{A}(Aₛ : Tyₛ Γ) → [ Aₛ ]³ ≡ A → Var (Γ , A)
  there : ∀{B}(Bₛ : Tyₛ Γ) → Var Γ → [ Bₛ ]³ ≡ B → Var (Γ , B)

⌜_⌝ⱽ : Var Γ → Tmₛ Γ
⌜ here Aₛ p ⌝ⱽ = transport (λ i → Tmₛ (_ , p i)) (π₂ₛ {Aᴹ = Aₛ} idSₛ)
⌜ there {Γ} Bₛ x p ⌝ⱽ = ⌜ x ⌝ⱽ [ transport (λ i → Subₛ (Γ , p i) Γ) (π₁ₛ {Γ ,ₛ Bₛ} {Aᴹ = Bₛ} idSₛ) ]tₛ

tyOfⱽ : Var Γ → Σ[ Δ ∈ Ctx ] Σ[ σ ∈ Subₛ Γ Δ ] Tyₛ Δ
tyOfⱽ {Γ , A} (here Aₛ p) = Γ , transport (λ i → Subₛ (_ , p i) Γ) (π₁ₛ {Aᴹ = Aₛ} idSₛ) , Aₛ
tyOfⱽ {Γ , B} (there Bₛ x p) =
  let (Δ , σ , Aₛ) = tyOfⱽ x
  in Δ , σ ∘ₛ transport (λ i → Subₛ (_ , p i) Γ) (π₁ₛ {Aᴹ = Bₛ} idSₛ) , Aₛ

tyOfⱽ-sound : (x : Var Γ) → tyOfₛ ⌜ x ⌝ⱽ ≡ let (Δ , σ , A) = tyOfⱽ x in A [ σ ]ₛ
tyOfⱽ-sound (here Aₛ p) = {!  tyOfₛ  !} -- refl
tyOfⱽ-sound (there Bₛ x p) = {!   !} -- let (Δ , σ , A) = tyOfⱽ x in (λ i → tyOfⱽ-sound x i [ π₁ₛ {Aᴹ = B} idSₛ ]ₛ) ∙ [∘]Tₛ A (π₁ₛ {Aᴹ = B} idSₛ) σ

data Ren : Ctx → Ctx → Set
⌜_⌝ᴿ : Ren Γ Δ → Subₛ Γ Δ

data Ren where
  ∅ : Ren Γ ∅ₛ
  _,_∶[_∣_]
    : ∀{B} (ρ : Ren Γ Δ)(x : Var Γ)
    → tyOfₛ ⌜ x ⌝ⱽ ≡ A [ ⌜ ρ ⌝ᴿ ]ₛ
    → [ A ]³ ≡ B
    → Ren Γ (Δ , B)

⌜ ∅ ⌝ᴿ = ∅Sₛ
⌜_⌝ᴿ {Γ} {Δ , _} (_,_∶[_∣_] {A = Aₛ} ρ x p q) = transport (λ i → Subₛ Γ (Δ , q i)) (_,ₛ_∶[_] {Aᴹ = Aₛ} ⌜ ρ ⌝ᴿ ⌜ x ⌝ⱽ p) 

lookupVar : (ρ : Ren Γ Δ) → Var Δ → Var Γ
lookupVar (_ , x ∶[ _ ∣ _ ]) (here _ _) = x
lookupVar (ρ , _ ∶[ _ ∣ _ ]) (there _ y _) = lookupVar ρ y

⌜lookupVar⌝ : (ρ : Ren Γ Δ)(x : Var Δ) → ⌜ x ⌝ⱽ [ ⌜ ρ ⌝ᴿ ]tₛ ≡ ⌜ lookupVar ρ x ⌝ⱽ
⌜lookupVar⌝ (ρ , x ∶[ p ∣ q ]) (here A p') =
  {! transport-filler (λ i → Tmₛ (_ , p' i)) (π₂ₛ idSₛ) !}
  -- sym (π₂idSₛ (transport (λ i → Subₛ _ (_ , q (~ i))) (⌜ ρ ⌝ᴿ ,ₛ ⌜ x ⌝ⱽ ∶[ p ]))) ∙ ?
⌜lookupVar⌝ (ρ , x ∶[ p ∣ q ]) (there B y p') = {!   !}

-- cong,∶[]ᴿ
--   : ∀{B}{ρ ρ' : Ren Γ Δ}{x x' : Var Γ}{p : tyOfₛ ⌜ x ⌝ⱽ ≡ A [ ⌜ ρ ⌝ᴿ ]ₛ}{p' : tyOfₛ ⌜ x' ⌝ⱽ ≡ A [ ⌜ ρ' ⌝ᴿ ]ₛ}
--     {q q' : B ≡ [ A ]³}
--   → ρ ≡ ρ' → x ≡ x'
--   → _,_∶[_∣_] {A = A} {B = B} ρ x p q ≡ _,_∶[_∣_] {A = A} {B = B} ρ' x' p' q'
-- cong,∶[]ᴿ {A = A} {B = B} {p = p} {p'} {q} {q'} ρ≡ρ' x≡x' i =
--   _,_∶[_∣_] {A = A} (ρ≡ρ' i) (x≡x' i)
--     (isSet→SquareP (λ _ _ → Tyₛ-is-set) p p' (λ i → tyOfₛ ⌜ x≡x' i ⌝ⱽ) (λ i → A [ ⌜ ρ≡ρ' i ⌝ᴿ ]ₛ) i)
--     (isSet→SquareP (λ _ _ → Ty-is-set) q q' (λ _ → B) (λ _ → [ A ]³) i)

η∅ᴿ : (ρ : Ren Γ ∅) → ρ ≡ ∅
η∅ᴿ ∅ = refl

η,ᴿ
  : ∀{B}(ρ : Ren Γ (Δ , B))
  → Σ[ A ∈ Tyₛ Δ ] Σ[ q' ∈ [ A ]³ ≡ B ]
    Σ[ ρ' ∈ Ren Γ Δ ] Σ[ x' ∈ Var Γ ]
    Σ[ p' ∈ tyOfₛ ⌜ x' ⌝ⱽ ≡ A [ ⌜ ρ' ⌝ᴿ ]ₛ ]
    (ρ ≡ _,_∶[_∣_] {A = A} {B = B} ρ' x' p' q')
η,ᴿ (_,_∶[_∣_] {A = A} ρ x p q) = A , q , ρ , x , p , refl

wkᴿ : (A : Tyₛ Γ) → Ren Γ Δ → Ren (Γ ,ₛ A) Δ
⌜wkᴿ⌝ : (A : Tyₛ Γ)(ρ : Ren Γ Δ) → ⌜ ρ ⌝ᴿ ∘ₛ π₁ₛ {Aᴹ = A} idSₛ ≡ ⌜ wkᴿ A ρ ⌝ᴿ
wkᴿ A ∅ = ∅
wkᴿ A (_,_∶[_∣_] {A = A'} ρ x p q) = wkᴿ A ρ , there A x refl ∶[ {!   !} ∣ q ]
⌜wkᴿ⌝ A ρ = {!   !}

idR : Ren Γ Γ
⌜idR⌝ : ∀{Γ} → idSₛ ≡ ⌜ idR {Γ} ⌝ᴿ
idR {∅} = ∅
idR {Γ , A} = {! wkᴿ ⟨ A , idSₛ ⟩! idR , ? ∶[ ? ∣ ? ]   !}
⌜idR⌝ {Γ} = {!   !}

_⊙_ : Ren Δ Θ → Ren Γ Δ → Ren Γ Θ
⌜⊙⌝ : (ρ : Ren Δ Θ)(ρ' : Ren Γ Δ) → ⌜ ρ ⌝ᴿ ∘ₛ ⌜ ρ' ⌝ᴿ ≡ ⌜ ρ ⊙ ρ' ⌝ᴿ
ρ ⊙ ρ' = {!   !}
⌜⊙⌝ ρ ρ' = {!   !}

-- 
-- open import Theory.SC.QIIRT-tyOf.Models.Yoneda

-- evalSub : (σ : Subₛ Γ Δ) → Σ[ ρ ∈ Ren Γ Δ ] σ ≡ ⌜ ρ ⌝ᴿ
-- evalTm : (t : Tmₛ Γ) → Σ[ x ∈ Var Γ ] t ≡ ⌜ x ⌝ⱽ
-- evalSub (y , natʸ) = {!   !}
-- evalTm t = {!   !}