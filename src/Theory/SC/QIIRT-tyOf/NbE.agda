module Theory.SC.QIIRT-tyOf.NbE where

open import Prelude
open import Theory.SC.QIIRT-tyOf.Syntax

postulate
  UIP : ∀ {ℓ} → {A : Set ℓ} → {x y : A} → isProp (x ≡ y)

cong,∶[]
  : {σ σ' : Sub Γ Δ}{t t' : Tm Γ}
  → (p : tyOf t ≡ A [ σ ])(p' : tyOf t' ≡ A [ σ' ])
  → σ ≡ σ' → t ≡ t'
  → (σ , t ∶[ p ]) ≡ (σ' , t' ∶[ p' ])
cong,∶[] {A = A} p p' eqσ eqt =
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

cong,∶[]ᴿ
  : {ρ ρ' : Ren Γ Δ}{x x' : Var Γ}{p : tyOf ⌜ x ⌝ⱽ ≡ A [ ⌜ ρ ⌝ᴿ ]}{p' : tyOf ⌜ x' ⌝ⱽ ≡ A [ ⌜ ρ' ⌝ᴿ ]}
  → ρ ≡ ρ' → x ≡ x'
  → (ρ , x ∶[ p ]) ≡ (ρ' , x' ∶[ p' ])
cong,∶[]ᴿ {A = A} {p = p} {p'} ρ≡ρ' x≡x' i = ρ≡ρ' i , x≡x' i ∶[ isSet→SquareP (λ _ _ → Ty-is-set) p p' (λ i → tyOf ⌜ x≡x' i ⌝ⱽ) (λ i → A [ ⌜ ρ≡ρ' i ⌝ᴿ ]) i ]

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
    ≡⟨ cong,∶[] (cong _[ π₁ idS ] p ∙ [∘]T _ _ _) q (⌜wkᴿ⌝ A ρ) refl ⟩
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
    ≡⟨ cong,∶[] refl {!!} (sym (idS∘ (π₁ idS)) ∙ cong (_∘ π₁ idS) ⌜idR⌝ ∙ ⌜wkᴿ⌝ A idR) refl ⟩
  ⌜ wkᴿ A idR ⌝ᴿ , π₂ idS ∶[ _ ]
    ∎

lookupVar-wkᴿ : (ρ : Ren Γ Δ)(x : Var Δ) → lookupVar (wkᴿ A ρ) x ≡ there (lookupVar ρ x)
lookupVar-wkᴿ (ρ , x ∶[ p ]) here = refl
lookupVar-wkᴿ (ρ , x' ∶[ p ]) (there x) = lookupVar-wkᴿ ρ x

lookupVar-idR : (x : Var Γ) → lookupVar idR x ≡ x
lookupVar-idR here = refl
lookupVar-idR (there x) = lookupVar-wkᴿ idR x ∙ cong there (lookupVar-idR x)

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
    ≡⟨ cong,∶[] (cong _[  ⌜ ρ' ⌝ᴿ ] p ∙ [∘]T _ _ _) _ (⌜⊙⌝ ρ ρ') (⌜lookupVar⌝ ρ' x) ⟩
  ⌜ ρ ⊙ ρ' ⌝ᴿ , ⌜ lookupVar ρ' x ⌝ⱽ ∶[ _ ]
    ∎

lookupVar⊙ : (ρ : Ren Δ Θ)(ρ' : Ren Γ Δ)(x : Var Θ)
           → lookupVar ρ' (lookupVar ρ x) ≡ lookupVar (ρ ⊙ ρ') x
lookupVar⊙ (ρ , y ∶[ p ]) ρ' here = refl
lookupVar⊙ (ρ , y ∶[ p ]) ρ' (there x) = lookupVar⊙ ρ ρ' x

wkᴿ⊙ : (ρ : Ren Δ Θ)(ρ' : Ren Γ Δ){A : Ty Δ}(x : Var Γ)(p : tyOf ⌜ x ⌝ⱽ ≡ A [ ⌜ ρ' ⌝ᴿ ])
     → wkᴿ A ρ ⊙ (ρ' , x ∶[ p ]) ≡ ρ ⊙ ρ'
wkᴿ⊙ ∅ ρ' x p = refl
wkᴿ⊙ (ρ , x ∶[ p ]) ρ' {A} x' p' =
  (wkᴿ A ρ ⊙ (ρ' , x' ∶[ p' ])) , lookupVar ρ' x ∶[ _ ]
    ≡⟨ cong,∶[]ᴿ (wkᴿ⊙ ρ ρ' x' p') refl ⟩
  (ρ ⊙ ρ') , lookupVar ρ' x ∶[ _ ]
    ∎

idR⊙ : (ρ : Ren Γ Δ) → idR ⊙ ρ ≡ ρ
idR⊙ {_} {∅} ∅ = refl
idR⊙ {_} {Δ , A} (ρ , x ∶[ p ]) = cong,∶[]ᴿ (wkᴿ⊙ idR ρ x p ∙ idR⊙ ρ) refl

_⊙idR : (ρ : Ren Γ Δ) → ρ ⊙ idR ≡ ρ
∅ ⊙idR = refl
(ρ , x ∶[ p ]) ⊙idR = cong,∶[]ᴿ (ρ ⊙idR) (lookupVar-idR x)

⊙-assoc : (ρ : Ren Γ Δ)(ρ' : Ren Δ Θ)(ρ'' : Ren Θ Ξ)
        → (ρ'' ⊙ ρ') ⊙ ρ ≡ ρ'' ⊙ (ρ' ⊙ ρ)
⊙-assoc ρ ρ' ∅ = refl
⊙-assoc ρ ρ' (ρ'' , x'' ∶[ p'' ]) = cong,∶[]ᴿ (⊙-assoc ρ ρ' ρ'') (lookupVar⊙ ρ' ρ x'')

-- Evaluate substitutions and terms to renamings and variables
evalSub : (σ : Sub Γ Δ) → Σ[ ρ ∈ Ren Γ Δ ] σ ≡ ⌜ ρ ⌝ᴿ
evalTm : (t : Tm Γ) → Σ[ x ∈ Var Γ ] t ≡ ⌜ x ⌝ⱽ

evalSub ∅S = ∅ , refl
evalSub (_,_∶[_] {A = A} σ t p) with evalSub σ | evalTm t
... | ρ , eqρ | x , eqx =
  (ρ , x ∶[ cong tyOf (sym eqx) ∙ p ∙ cong (A [_]) eqρ ]) ,
  cong,∶[] p _ eqρ eqx
evalSub idS = idR , ⌜idR⌝
evalSub (σ ∘ τ) with evalSub σ | evalSub τ
... | ρ , eqρ | ρ' , eqρ' = ρ ⊙ ρ' , cong₂ _∘_ eqρ eqρ' ∙ ⌜⊙⌝ ρ ρ'
evalSub (π₁ σ) with evalSub σ
... | (ρ , x ∶[ p ]) , eqρ = ρ , cong π₁ eqρ ∙ βπ₁ ⌜ ρ ⌝ᴿ ⌜ x ⌝ⱽ _
evalSub (βπ₁ σ t p i) with evalSub σ | evalTm t
... | ρ , eqρ | x , eqx = ρ ,
  isProp→PathP {B = λ j → βπ₁ σ t p j ≡ ⌜ ρ ⌝ᴿ}
    (λ j → UIP {x = βπ₁ σ t p j} {⌜ ρ ⌝ᴿ})
    (cong π₁ (cong,∶[] p ? eqρ eqx) ∙ βπ₁ ⌜ ρ ⌝ᴿ ⌜ x ⌝ⱽ _)
    eqρ
    i
evalSub ((idS∘ σ) i) with evalSub σ
... | ρ , eqρ = idR⊙ ρ i ,
  isProp→PathP {B = λ j → (idS∘ σ) j ≡ ⌜ idR⊙ ρ j ⌝ᴿ}
    (λ j → UIP {x = (idS∘ σ) j} {⌜ idR⊙ ρ j ⌝ᴿ})
    (cong₂ _∘_ ⌜idR⌝ eqρ ∙ ⌜⊙⌝ idR ρ)
    eqρ
    i
evalSub ((σ ∘idS) i) with evalSub σ
... | ρ , eqρ = (ρ ⊙idR) i ,
  isProp→PathP {B = λ j → (σ ∘idS) j ≡ ⌜ (ρ ⊙idR) j ⌝ᴿ}
    (λ j → UIP {x = (σ ∘idS) j} {⌜ (ρ ⊙idR) j ⌝ᴿ})
    (cong₂ _∘_ eqρ ⌜idR⌝ ∙ ⌜⊙⌝ ρ idR)
    eqρ
    i
evalSub (assocS σ₁ σ₂ σ₃ i) with evalSub σ₁ | evalSub σ₂ | evalSub σ₃
... | ρ₁ , eqρ₁ | ρ₂ , eqρ₂ | ρ₃ , eqρ₃ = ⊙-assoc ρ₁ ρ₂ ρ₃ i ,
  isProp→PathP {B = λ j → assocS σ₁ σ₂ σ₃ j ≡ ⌜ ⊙-assoc ρ₁ ρ₂ ρ₃ j ⌝ᴿ}
    (λ j → UIP {x = assocS σ₁ σ₂ σ₃ j} {⌜ ⊙-assoc ρ₁ ρ₂ ρ₃ j ⌝ᴿ})
    (cong₂ _∘_ (cong₂ _∘_ eqρ₃ eqρ₂ ∙ ⌜⊙⌝ ρ₃ ρ₂) eqρ₁ ∙ ⌜⊙⌝ (ρ₃ ⊙ ρ₂) ρ₁)
    (cong₂ _∘_ eqρ₃ (cong₂ _∘_ eqρ₂ eqρ₁ ∙ ⌜⊙⌝ ρ₂ ρ₁) ∙ ⌜⊙⌝ ρ₃ (ρ₂ ⊙ ρ₁))
     i
evalSub (η∅ σ i) with evalSub σ
... | ρ , eqρ = η∅ᴿ ρ i , isProp→PathP {B = λ j → η∅ σ j ≡ ⌜ η∅ᴿ ρ j ⌝ᴿ} (λ j → UIP {x = η∅ σ j} {⌜ η∅ᴿ ρ j ⌝ᴿ}) eqρ (λ _ → ∅S) i
evalSub (ηπ σ i) = {!   !}
evalSub (,∘ σ t τ p q i) = {!   !}

evalTm (t [ σ ]) with evalTm t | evalSub σ
... | x , eqx | ρ , eqρ = lookupVar ρ x , (λ i → eqx i [ eqρ i ]) ∙ ⌜lookupVar⌝ ρ x
evalTm (π₂ σ) with evalSub σ
... | (ρ , x ∶[ p ]) , eqρ = x , cong π₂ eqρ ∙ ⟨βπ₂⟩ ⌜ ρ ⌝ᴿ ⌜ x ⌝ⱽ _
evalTm (βπ₂ σ t p q i) with evalSub σ | evalTm t
... | ρ , eqρ | x , eqx = x ,
  isProp→PathP {B = λ j → βπ₂ σ t p q j ≡ ⌜ x ⌝ⱽ}
    (λ j → UIP {x = βπ₂ σ t p q j} {⌜ x ⌝ⱽ})
    (cong π₂ (cong,∶[] {!!} {!!} eqρ eqx) ∙ ⟨βπ₂⟩ ⌜ ρ ⌝ᴿ ⌜ x ⌝ⱽ _)
     eqx
     i
evalTm ([idS]t t i) with evalTm t
... | x , eqx = lookupVar-idR x (~ i) ,
  isProp→PathP {B = λ j → [idS]t t j ≡ ⌜ lookupVar-idR x (~ j) ⌝ⱽ}
    (λ j → UIP {x = [idS]t t j} {⌜ lookupVar-idR x (~ j) ⌝ⱽ})
     eqx
    ((λ i → eqx i [ ⌜idR⌝ i ]) ∙ ⌜lookupVar⌝ idR x)
     i
evalTm ([∘]t t σ τ i) with evalTm t | evalSub σ | evalSub τ
... | x , eqx | ρ , eqρ | ρ' , eqρ' = lookupVar⊙ ρ' ρ x i ,
  isProp→PathP {B = λ j → [∘]t t σ τ j ≡ ⌜ lookupVar⊙ ρ' ρ x j ⌝ⱽ}
    (λ j → UIP {x = [∘]t t σ τ j} {⌜ lookupVar⊙ ρ' ρ x j ⌝ⱽ})
    ((λ i → ((λ i → eqx i [ eqρ' i ]) ∙ ⌜lookupVar⌝ ρ' x) i [ eqρ i ]) ∙ ⌜lookupVar⌝ ρ (lookupVar ρ' x))
    ((λ i → eqx i [ (cong₂ _∘_ eqρ' eqρ ∙ ⌜⊙⌝ ρ' ρ) i ]) ∙ ⌜lookupVar⌝ (ρ' ⊙ ρ) x)
     i

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
    ≡⟨ cong,∶[] {!!} {!!} (⌜⇓ᴿ⌝ ρ) (sym (⌜⇓ⱽid⌝ x)) ⟩
  ⌜ ⇓ᴿ ρ ⌝subⁿᶠ , ⌜ ⇓ⱽ `idS x ⌝tm ∶[ cong tyOf (⌜⇓ⱽid⌝ x) ∙ p ∙ cong (A [_]) (⌜⇓ᴿ⌝ ρ) ]
    ∎

-- Normalisation by evaluation
normalise : (t : Tm Γ) → Σ[ tⁿ ∈ NeTm Γ ] t ≡ ⌜ tⁿ ⌝tm
normalise t = ⇓ⱽ `idS (evalTm t .fst) , evalTm t .snd ∙ sym (⌜⇓ⱽid⌝ (evalTm t .fst))
