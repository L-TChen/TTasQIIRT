module Theory.SC.QIIRT-tyOf.NbE where

open import Prelude
open import Theory.SC.QIIRT-tyOf.Syntax

cong,∶[]
  : {σ σ' : Sub Γ Δ}{t t' : Tm Γ}{p : tyOf t ≡ A [ σ ]}{p' : tyOf t' ≡ A [ σ' ]}
  → σ ≡ σ' → t ≡ t'
  → (σ , t ∶[ p ]) ≡ (σ' , t' ∶[ p' ])
cong,∶[] {A = A} {p = p} {p'} eqσ eqt =
  cong₃ _,_∶[_] eqσ eqt (isSet→SquareP (λ _ _ → Ty-is-set) p p' (cong tyOf eqt) (cong (A [_]) eqσ))

-- Definition of neutral and normal forms
data NfTy (Γ : Ctx) : Set where
  `U : NfTy Γ

⌜_⌝ty : NfTy Γ → Ty Γ
⌜ `U ⌝ty = U

data NeSub (Γ : Ctx) : Ctx → Set where
  `∅S : NeSub Γ ∅
  `idS : NeSub Γ Γ
  `π₁ : NeSub Γ (Δ , A) → NeSub Γ Δ

⌜_⌝subⁿᵉ : NeSub Γ Δ → Sub Γ Δ
⌜ `∅S ⌝subⁿᵉ = ∅S
⌜ `idS ⌝subⁿᵉ = idS
⌜ `π₁ σ ⌝subⁿᵉ = π₁ ⌜ σ ⌝subⁿᵉ

data NeTm (Γ : Ctx) : Set where
  `π₂ : NeSub Γ (Δ , A) → NeTm Γ

⌜_⌝tm : NeTm Γ → Tm Γ
⌜ `π₂ σⁿᵉ ⌝tm = π₂ ⌜ σⁿᵉ ⌝subⁿᵉ

data NfSub (Γ : Ctx) : Ctx → Set
⌜_⌝subⁿᶠ : NfSub Γ Δ → Sub Γ Δ

data NfSub Γ where
  `ne_ : NeSub Γ Δ → NfSub Γ Δ
  _`,_∶[_]
    : (σⁿᶠ : NfSub Γ Δ)(tⁿᵉ : NeTm Γ)
    → tyOf (⌜ tⁿᵉ ⌝tm) ≡ A [ ⌜ σⁿᶠ ⌝subⁿᶠ ]
    → NfSub Γ (Δ , A)

⌜ `ne σⁿᵉ ⌝subⁿᶠ = ⌜ σⁿᵉ ⌝subⁿᵉ
⌜ σⁿᶠ `, tⁿᵉ ∶[ p ] ⌝subⁿᶠ = ⌜ σⁿᶠ ⌝subⁿᶠ , ⌜ tⁿᵉ ⌝tm ∶[ p ]

-- Definitions of variables and renamings
data Var : (Γ : Ctx) → Set where
  here  : Var (Γ , A)
  there : Var Γ → Var (Γ , B)

⌜_⌝ⱽ : Var Γ → Tm Γ
⌜ here ⌝ⱽ = π₂ idS
⌜ there x ⌝ⱽ = ⌜ x ⌝ⱽ [ π₁ idS ]

tyOfⱽ : Var Γ → Σ[ Δ ∈ Ctx ] Σ[ σ ∈ Sub Γ Δ ] Ty Δ
tyOfⱽ (here {Γ} {A}) = Γ , π₁ idS , A
tyOfⱽ (there {Γ} {B} x) = let (Δ , σ , A) = tyOfⱽ x in Δ , σ ∘ π₁ idS , A

tyOfⱽ-sound : (x : Var Γ) → tyOf ⌜ x ⌝ⱽ ≡ let (Δ , σ , A) = tyOfⱽ x in A [ σ ]
tyOfⱽ-sound here = refl
tyOfⱽ-sound (there x) = let (Δ , σ , A) = tyOfⱽ x in (λ i → tyOfⱽ-sound x i [ π₁ idS ]) ∙ [∘]T A (π₁ idS) σ

data Ren : Ctx → Ctx → Set
⌜_⌝ᴿ : Ren Γ Δ → Sub Γ Δ

data Ren where
  ∅ : Ren Γ ∅
  _,_∶[_] : (ρ : Ren Γ Δ)(x : Var Γ) → tyOf ⌜ x ⌝ⱽ ≡ A [ ⌜ ρ ⌝ᴿ ] → Ren Γ (Δ , A)

⌜ ∅ ⌝ᴿ = ∅S
⌜ ρ , x ∶[ p ] ⌝ᴿ = ⌜ ρ ⌝ᴿ , ⌜ x ⌝ⱽ ∶[ p ]

η∅ᴿ : (ρ : Ren Γ ∅) → ρ ≡ ∅
η∅ᴿ ∅ = refl

lookupVar : (ρ : Ren Γ Δ) → Var Δ → Var Γ
lookupVar (ρ , x' ∶[ p ]) here = x'
lookupVar (ρ , x' ∶[ p ]) (there x) = lookupVar ρ x

⌜lookupVar⌝ : (ρ : Ren Γ Δ)(x : Var Δ) → ⌜ x ⌝ⱽ [ ⌜ ρ ⌝ᴿ ] ≡ ⌜ lookupVar ρ x ⌝ⱽ
⌜lookupVar⌝ (ρ , x' ∶[ p ]) here = sym (π₂idS (⌜ ρ ⌝ᴿ , ⌜ x' ⌝ⱽ ∶[ p ])) ∙ ⟨βπ₂⟩ ⌜ ρ ⌝ᴿ ⌜ x' ⌝ⱽ _
⌜lookupVar⌝ (ρ , x' ∶[ p ]) (there x) =
  ⌜ x ⌝ⱽ [ π₁ idS ] [ ⌜ ρ ⌝ᴿ , ⌜ x' ⌝ⱽ ∶[ p ] ]
    ≡⟨ [∘]t ⌜ x ⌝ⱽ (⌜ ρ ⌝ᴿ , ⌜ x' ⌝ⱽ ∶[ p ]) (π₁ idS) ⟩
  ⌜ x ⌝ⱽ [ π₁ idS ∘ (⌜ ρ ⌝ᴿ , ⌜ x' ⌝ⱽ ∶[ p ]) ]
    ≡⟨ (λ i → ⌜ x ⌝ⱽ [ (sym (π₁idS (⌜ ρ ⌝ᴿ , ⌜ x' ⌝ⱽ ∶[ p ])) ∙ βπ₁ ⌜ ρ ⌝ᴿ ⌜ x' ⌝ⱽ p) i ]) ⟩
  ⌜ x ⌝ⱽ [ ⌜ ρ ⌝ᴿ ]
    ≡⟨ ⌜lookupVar⌝ ρ x ⟩
  ⌜ lookupVar ρ x ⌝ⱽ
    ∎

wkᴿ : (A : Ty Γ) → Ren Γ Δ → Ren (Γ , A) Δ
⌜wkᴿ⌝ : (A : Ty Γ)(ρ : Ren Γ Δ) → ⌜ ρ ⌝ᴿ ∘ π₁ idS ≡ ⌜ wkᴿ A ρ ⌝ᴿ
wkᴿ A ∅ = ∅
wkᴿ A (_,_∶[_] {A = A'} ρ x p) = wkᴿ A ρ , there x ∶[ cong (_[ π₁ idS ]) p ∙ [∘]T A' (π₁ idS) ⌜ ρ ⌝ᴿ ∙ cong (A' [_]) (⌜wkᴿ⌝ A ρ) ]
⌜wkᴿ⌝ A ∅ = η∅ _
⌜wkᴿ⌝ A (_,_∶[_] {A = A'} ρ x p) =
  let q = cong (_[ π₁ idS ]) p ∙ [∘]T A' (π₁ idS) ⌜ ρ ⌝ᴿ ∙ cong (A' [_]) (⌜wkᴿ⌝ A ρ) in
  (⌜ ρ ⌝ᴿ , ⌜ x ⌝ⱽ ∶[ p ]) ∘ π₁ idS
    ≡⟨ ⟨,∘⟩ ⌜ ρ ⌝ᴿ ⌜ x ⌝ⱽ (π₁ idS) p ⟩
  ⌜ ρ ⌝ᴿ ∘ π₁ idS , ⌜ x ⌝ⱽ [ π₁ idS ] ∶[ cong (_[ π₁ idS ]) p ∙ [∘]T A' (π₁ idS) ⌜ ρ ⌝ᴿ ]
    ≡⟨ cong,∶[] (⌜wkᴿ⌝ A ρ) refl ⟩
  ⌜ wkᴿ A ρ ⌝ᴿ , ⌜ x ⌝ⱽ [ π₁ idS ] ∶[ q ]
    ∎

idR : Ren Γ Γ
⌜idR⌝ : ∀{Γ} → idS ≡ ⌜ idR {Γ} ⌝ᴿ
idR {∅} = ∅
idR {Γ , A} = wkᴿ A idR , here ∶[ cong (A [_]) (sym (idS∘ (π₁ idS)) ∙ cong (_∘ π₁ idS) ⌜idR⌝ ∙ ⌜wkᴿ⌝ A idR) ]
⌜idR⌝ {∅} = η∅ _
⌜idR⌝ {Γ , A} =
  idS
    ≡⟨ ηπ idS ⟩
  π₁ idS , π₂ idS ∶[ tyOfπ₂ idS ]
    ≡⟨ cong,∶[] (sym (idS∘ (π₁ idS)) ∙ cong (_∘ π₁ idS) ⌜idR⌝ ∙ ⌜wkᴿ⌝ A idR) refl ⟩
  ⌜ wkᴿ A idR ⌝ᴿ , π₂ idS ∶[ _ ]
    ∎

_⊙_ : Ren Δ Θ → Ren Γ Δ → Ren Γ Θ
⌜⊙⌝ : (ρ : Ren Δ Θ)(ρ' : Ren Γ Δ) → ⌜ ρ ⌝ᴿ ∘ ⌜ ρ' ⌝ᴿ ≡ ⌜ ρ ⊙ ρ' ⌝ᴿ
∅ ⊙ ρ = ∅
(_,_∶[_] {A = A} ρ x p) ⊙ ρ' =
  ρ ⊙ ρ' , lookupVar ρ' x
  ∶[
    cong tyOf (sym (⌜lookupVar⌝ ρ' x))
    ∙ (λ i → p i [ ⌜ ρ' ⌝ᴿ ])
    ∙ [∘]T A ⌜ ρ' ⌝ᴿ ⌜ ρ ⌝ᴿ
    ∙ cong (A [_]) (⌜⊙⌝ ρ ρ')
  ]
⌜⊙⌝ ∅ ρ' = η∅ _
⌜⊙⌝ (_,_∶[_] {A = A} ρ x p) ρ' =
  (⌜ ρ ⌝ᴿ , ⌜ x ⌝ⱽ ∶[ p ]) ∘ ⌜ ρ' ⌝ᴿ
    ≡⟨ ⟨,∘⟩ ⌜ ρ ⌝ᴿ ⌜ x ⌝ⱽ ⌜ ρ' ⌝ᴿ p ⟩
  ⌜ ρ ⌝ᴿ ∘ ⌜ ρ' ⌝ᴿ , ⌜ x ⌝ⱽ [ ⌜ ρ' ⌝ᴿ ] ∶[ cong (_[ ⌜ ρ' ⌝ᴿ ]) p ∙ [∘]T A ⌜ ρ' ⌝ᴿ ⌜ ρ ⌝ᴿ ]
    ≡⟨ cong,∶[] (⌜⊙⌝ ρ ρ') (⌜lookupVar⌝ ρ' x) ⟩
  ⌜ ρ ⊙ ρ' ⌝ᴿ , ⌜ lookupVar ρ' x ⌝ⱽ ∶[ _ ]
    ∎

-- Evaluate substitutions and terms to renamings and variables
evalSub : (σ : Sub Γ Δ) → Σ[ ρ ∈ Ren Γ Δ ] σ ≡ ⌜ ρ ⌝ᴿ
evalTm : (t : Tm Γ) → Σ[ x ∈ Var Γ ] t ≡ ⌜ x ⌝ⱽ

evalSub ∅S = ∅ , refl
evalSub (_,_∶[_] {A = A} σ t p) with evalSub σ | evalTm t
... | ρ , eqρ | x , eqx = (ρ , x ∶[ cong tyOf (sym eqx) ∙ p ∙ cong (A [_]) eqρ ]) , {!   !}
evalSub idS = idR , ⌜idR⌝
evalSub (σ ∘ τ) with evalSub σ | evalSub τ
... | ρ , eqρ | ρ' , eqρ' = ρ ⊙ ρ' , cong₂ _∘_ eqρ eqρ' ∙ ⌜⊙⌝ ρ ρ'
evalSub (π₁ σ) with evalSub σ
... | (ρ , x ∶[ p ]) , eqρ = ρ , cong π₁ eqρ ∙ βπ₁ ⌜ ρ ⌝ᴿ ⌜ x ⌝ⱽ _
evalSub (βπ₁ σ t p i) = {!   !}
evalSub ((idS∘ σ) i) = {!   !}
evalSub ((σ ∘idS) i) = {!   !}
evalSub (assocS σ σ₁ σ₂ i) = {!   !}
evalSub (,∘ σ t σ₁ p q i) = {!   !}
evalSub (η∅ σ i) = η∅ᴿ (evalSub σ .fst) i , λ j → {!   !}
evalSub (ηπ σ i) = {!   !}

evalTm (t [ σ ]) with evalTm t | evalSub σ
... | x , eqx | ρ , eqρ = lookupVar ρ x , (λ i → eqx i [ eqρ i ]) ∙ ⌜lookupVar⌝ ρ x
evalTm (π₂ σ) with evalSub σ
... | (ρ , x ∶[ p ]) , eqρ = x , cong π₂ eqρ ∙ ⟨βπ₂⟩ ⌜ ρ ⌝ᴿ ⌜ x ⌝ⱽ _
evalTm (βπ₂ σ t p q i) = {!   !}
evalTm ([idS]t t i) = {!   !}
evalTm ([∘]t t σ τ i) = {!   !}

-- Reify variables and renamings to neutral forms and normal forms
⇓ⱽ : (`σ : NeSub Γ Δ) → Var Δ → NeTm Γ
⇓ⱽ `σ here = `π₂ `σ
⇓ⱽ `σ (there x) = ⇓ⱽ (`π₁ `σ) x

⌜⇓ⱽπ₁⌝ : (`σ : NeSub Γ (Δ , A))(x : Var Δ) → ⌜ ⇓ⱽ (`π₁ `σ) x ⌝tm ≡ ⌜ x ⌝ⱽ [ π₁ ⌜ `σ ⌝subⁿᵉ ]
⌜⇓ⱽπ₁⌝ `σ here = π₂idS (π₁ ⌜ `σ ⌝subⁿᵉ)
⌜⇓ⱽπ₁⌝ `σ (there x) = ⌜⇓ⱽπ₁⌝ (`π₁ `σ) x ∙ (λ i → ⌜ x ⌝ⱽ [ π₁idS (π₁ ⌜ `σ ⌝subⁿᵉ) i ]) ∙ (sym ([∘]t ⌜ x ⌝ⱽ (π₁ ⌜ `σ ⌝subⁿᵉ) (π₁ idS)))

⌜⇓ⱽid⌝ : (x : Var Γ) → ⌜ ⇓ⱽ `idS x ⌝tm ≡ ⌜ x ⌝ⱽ
⌜⇓ⱽid⌝ here = refl
⌜⇓ⱽid⌝ (there x) = ⌜⇓ⱽπ₁⌝ `idS x

⇓ᴿ : Ren Γ Δ → NfSub Γ Δ
⌜⇓ᴿ⌝ : (ρ : Ren Γ Δ) → ⌜ ρ ⌝ᴿ ≡ ⌜ ⇓ᴿ ρ ⌝subⁿᶠ
⇓ᴿ ∅ = `ne `∅S
⇓ᴿ (_,_∶[_] {A = A} ρ x p) = ⇓ᴿ ρ `, ⇓ⱽ `idS x ∶[ cong tyOf (⌜⇓ⱽid⌝ x) ∙ p ∙ cong (A [_]) (⌜⇓ᴿ⌝ ρ) ]
⌜⇓ᴿ⌝ ∅ = refl
⌜⇓ᴿ⌝ (_,_∶[_] {A = A} ρ x p) =
  ⌜ ρ ⌝ᴿ , ⌜ x ⌝ⱽ ∶[ p ]
    ≡⟨ cong,∶[] (⌜⇓ᴿ⌝ ρ) (sym (⌜⇓ⱽid⌝ x)) ⟩
  ⌜ ⇓ᴿ ρ ⌝subⁿᶠ , ⌜ ⇓ⱽ `idS x ⌝tm ∶[ cong tyOf (⌜⇓ⱽid⌝ x) ∙ p ∙ cong (A [_]) (⌜⇓ᴿ⌝ ρ) ]
    ∎

-- Normalisation by evaluation
normalise : (t : Tm Γ) → Σ[ tⁿ ∈ NeTm Γ ] t ≡ ⌜ tⁿ ⌝tm
normalise t = ⇓ⱽ `idS (evalTm t .fst) , evalTm t .snd ∙ sym (⌜⇓ⱽid⌝ (evalTm t .fst))