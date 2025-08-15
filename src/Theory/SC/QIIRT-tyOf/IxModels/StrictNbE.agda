{-# OPTIONS -WnoUnsupportedIndexedMatch --show-implicit #-}

module Theory.SC.QIIRT-tyOf.IxModels.StrictNbE where

open import Prelude
open import Theory.SC.QIIRT-tyOf.Syntax
  hiding
  ( Γ; Δ; Θ; Ξ
  ; A; B; C; D
  ; t; u
  ; σ; τ; δ; γ
  )
open import Theory.SC.QIIRT-tyOf.Models.StrictTerm

open import Theory.SC.QIIRT-tyOf.Models.Term
open import Theory.SC.QIIRT-tyOf.Models.Yoneda Termᵃ Termᵐ
-- open Yoneda 
open Subʸ

open import Theory.SC.QIIRT-tyOf.Models.LocalNoQuotient
open Ty³

-- Ctx' is defined in order to pattern match in Var
data Ctx' : Set
[_]ᶜ : Ctx' → Ctx

data Ctx' where
  ∅
    : Ctx'
  _,_
    : (Γ' : Ctx') (Aₛ : Tyₛ [ Γ' ]ᶜ)
    → Ctx'

[ ∅       ]ᶜ = ∅
[ Γ' , Aₛ ]ᶜ = [ Γ' ]ᶜ ,ₛ Aₛ

variable
  Γ' Δ' Θ' Ξ' : Ctx'
-- Definition of neutral and normal forms
data NfTy (Γ : Ctxₛ) : Set where
  `U : NfTy Γ

⌜_⌝ty : NfTy Γ → Tyₛ Γ
⌜ `U ⌝ty = Uₛ

data NeSub (Γ : Ctx) : Ctx → Set where
  `∅S
    : NeSub Γ ∅ₛ
  `idS
    : NeSub Γ Γ
  `π₁
    : (A : Tyₛ Δ) → NeSub Γ (Δ ,ₛ A)
    → NeSub Γ Δ

⌜_⌝subⁿᵉ : NeSub Γ Δ → Subₛ Γ Δ
⌜ `∅S     ⌝subⁿᵉ = ∅Sₛ
⌜ `idS    ⌝subⁿᵉ = idSₛ
⌜ `π₁ A σ ⌝subⁿᵉ = π₁ₛ {Aᴹ = A} ⌜ σ ⌝subⁿᵉ

data NeTm (Γ : Ctx) : Set where
  `π₂
    : (A : Tyₛ Δ) → NeSub Γ (Δ ,ₛ A)
    → NeTm Γ

⌜_⌝tm
  : NeTm Γ
  → Tmₛ Γ
⌜ `π₂ A σⁿᵉ ⌝tm = π₂ₛ {Aᴹ = A} ⌜ σⁿᵉ ⌝subⁿᵉ

data NfSub (Γ : Ctx) : Ctx → Set
⌜_⌝subⁿᶠ
  : NfSub Γ Δ
  → Subₛ Γ Δ

data NfSub Γ where
  `ne_
    : NeSub Γ Δ
    → NfSub Γ Δ
  _`,_∶[_]
    : (σⁿᶠ : NfSub Γ Δ)(tⁿᵉ : NeTm Γ)
    → tyOfₛ (⌜ tⁿᵉ ⌝tm) ≡ A [ ⌜ σⁿᶠ ⌝subⁿᶠ ]ₛ
    → NfSub Γ (Δ ,ₛ A)

⌜ `ne σⁿᵉ ⌝subⁿᶠ = ⌜ σⁿᵉ ⌝subⁿᵉ
⌜ _`,_∶[_] {A = A} σⁿᶠ tⁿᵉ p ⌝subⁿᶠ = _,ₛ_∶[_] {Aᴹ = A} ⌜ σⁿᶠ ⌝subⁿᶠ ⌜ tⁿᵉ ⌝tm p

-- Definitions of variables and renamings
data Var : (Γ' : Ctx') → Set where
  here
    : (Aₛ : Tyₛ [ Γ' ]ᶜ)
    → Var (Γ' , Aₛ)
  there
    : (Bₛ : Tyₛ [ Γ' ]ᶜ)
    → Var Γ'
    → Var (Γ' , Bₛ)

⌜_⌝ⱽ
  : Var Γ'
  → Tmₛ [ Γ' ]ᶜ
⌜ here Aₛ    ⌝ⱽ = π₂ₛ {Aᴹ = Aₛ} idSₛ
⌜ there Bₛ x ⌝ⱽ = ⌜ x ⌝ⱽ [ π₁ₛ {Aᴹ = Bₛ} idSₛ ]tₛ

tyOfⱽ
  : Var Γ'
  → Σ[ Δ' ∈ Ctx' ] Σ[ σ ∈ Subₛ [ Γ' ]ᶜ [ Δ' ]ᶜ ] Tyₛ [ Δ' ]ᶜ
tyOfⱽ (here {Γ'} Aₛ)    = Γ' , π₁ₛ {Aᴹ = Aₛ} idSₛ , Aₛ
tyOfⱽ (there {Γ'} Bₛ x) =
  let (Δ' , σ , Aₛ) = tyOfⱽ x in
  Δ' , σ ∘ₛ π₁ₛ {Aᴹ = Bₛ} idSₛ , Aₛ

tyOfⱽ-sound
  : (x : Var Γ')
  → tyOfₛ ⌜ x ⌝ⱽ ≡ let (_ , σ , Aₛ) = tyOfⱽ x in Aₛ [ σ ]ₛ
tyOfⱽ-sound (here Aₛ)    = refl
tyOfⱽ-sound (there Bₛ x) =
  let (Γ , σ , Aₛ) = tyOfⱽ x
  in (λ i → tyOfⱽ-sound x i [ π₁ₛ {Aᴹ = Bₛ} idSₛ ]ₛ)
     ∙ cong (ty³ _ _ _ _ (E Aₛ)) (≡ʸ→≡ refl)

data Ren : Ctx' → Ctx' → Set
⌜_⌝ᴿ : Ren Γ' Δ' → Subₛ [ Γ' ]ᶜ [ Δ' ]ᶜ

data Ren where
  ∅
    : Ren Γ' ∅
  _,_∶[_]
    : (ρ : Ren Γ' Δ')(x : Var Γ')
    → tyOfₛ ⌜ x ⌝ⱽ ≡ A [ ⌜ ρ ⌝ᴿ ]ₛ
    → Ren Γ' (Δ' , A)
cong,∶[]ᴿ
  : {ρ ρ' : Ren Γ' Δ'}{x x' : Var Γ'}{p : tyOfₛ ⌜ x ⌝ⱽ ≡ A [ ⌜ ρ ⌝ᴿ ]ₛ}{p' : tyOfₛ ⌜ x' ⌝ⱽ ≡ A [ ⌜ ρ' ⌝ᴿ ]ₛ}
  → ρ ≡ ρ' → x ≡ x'
  → _,_∶[_] {A = A} ρ x p ≡ _,_∶[_] {A = A} ρ' x' p'
cong,∶[]ᴿ {A = A} {p = p} {p'} ρ≡ρ' x≡x' i =
  _,_∶[_] {A = A} (ρ≡ρ' i) (x≡x' i)
    (isSet→SquareP (λ _ _ → UIP') p p' (λ i → tyOfₛ ⌜ x≡x' i ⌝ⱽ) (λ i → A [ ⌜ ρ≡ρ' i ⌝ᴿ ]ₛ) i)
--    (isSet→SquareP (λ _ _ → Tyₛ-is-set) p p' (λ i → tyOfₛ ⌜ x≡x' i ⌝ⱽ) (λ i → A [ ⌜ ρ≡ρ' i ⌝ᴿ ]ₛ) i)

⌜ ∅ ⌝ᴿ = ∅Sₛ
⌜ _,_∶[_] {Γ'} {Δ'} {A} ρ x p ⌝ᴿ =
  _,ₛ_∶[_] {[ Γ' ]ᶜ} {[ Δ' ]ᶜ} {Aᴹ = A} ⌜ ρ ⌝ᴿ ⌜ x ⌝ⱽ p

lookupVar
  : (ρ : Ren Γ' Δ') → Var Δ'
  → Var Γ'
lookupVar (_ , x ∶[ _ ]) (here _) = x
lookupVar (ρ , _ ∶[ _ ]) (there _ x) = lookupVar ρ x

⌜lookupVar⌝
  : (ρ : Ren Γ' Δ')(x : Var Δ')
  → ⌜ x ⌝ⱽ [ ⌜ ρ ⌝ᴿ ]tₛ ≡ ⌜ lookupVar ρ x ⌝ⱽ
⌜lookupVar⌝ (ρ , x ∶[ p ]) (here Aₛ) =
  sym (π₂idSₛ {Aᴹ = Aₛ} (_,ₛ_∶[_] {Aᴹ = Aₛ} ⌜ ρ ⌝ᴿ ⌜ x ⌝ⱽ p)) ∙ βπ₂ₛ {Aᴹ = Aₛ} ⌜ ρ ⌝ᴿ ⌜ x ⌝ⱽ p
⌜lookupVar⌝ (ρ , x' ∶[ p ]) (there Bₛ x) =
  [∘]tₛ ⌜ x ⌝ⱽ (_,ₛ_∶[_] {Aᴹ = Bₛ} ⌜ ρ ⌝ᴿ ⌜ x' ⌝ⱽ p) (π₁ₛ {Aᴹ = Bₛ} idSₛ)
  ∙ (λ i → ⌜ x ⌝ⱽ [ π₁idSₛ {Aᴹ = Bₛ} (_,ₛ_∶[_] {Aᴹ = Bₛ} ⌜ ρ ⌝ᴿ ⌜ x' ⌝ⱽ p) (~ i) ]tₛ)
  ∙ (λ i → ⌜ x ⌝ⱽ [ βπ₁ₛ {Aᴹ = Bₛ} ⌜ ρ ⌝ᴿ ⌜ x' ⌝ⱽ p i ]tₛ)
  ∙ ⌜lookupVar⌝ ρ x

η∅ᴿ
  : (ρ : Ren Γ' ∅)
  → ρ ≡ ∅
η∅ᴿ ∅ = refl

η,ᴿ
  : (ρ : Ren Γ' (Δ' , A))
  → Σ[ ρ' ∈ Ren Γ' Δ' ] Σ[ x' ∈ Var Γ' ] Σ[ p' ∈ tyOfₛ ⌜ x' ⌝ⱽ ≡ A [ ⌜ ρ' ⌝ᴿ ]ₛ ]
    ρ ≡ ρ'  , x' ∶[ p' ]
η,ᴿ (ρ , x ∶[ p ]) = ρ , x , p , refl

wkᴿ
  : (A : Tyₛ [ Γ' ]ᶜ) → Ren Γ' Δ'
  → Ren (Γ' , A) Δ'
⌜wkᴿ⌝
  : (A : Tyₛ [ Γ' ]ᶜ)(ρ : Ren Γ' Δ')
  → ⌜ ρ ⌝ᴿ ∘ₛ π₁ₛ {Aᴹ = A} idSₛ ≡ ⌜ wkᴿ A ρ ⌝ᴿ
wkᴿ A ∅ = ∅
wkᴿ {Γ'} A (_,_∶[_] {A = A'} ρ x p) =
  wkᴿ A ρ  , there A x ∶[
    cong _[ π₁ₛ {Aᴹ = A} idSₛ ]ₛ p ∙ cong (ty³ _ _ _ _ (E (A' [ ⌜ ρ ⌝ᴿ ]ₛ))) (≡ʸ→≡ refl) ∙ cong (A' [_]ₛ) (⌜wkᴿ⌝ A ρ) 
  ]
⌜wkᴿ⌝ A ∅ = ≡ʸ→≡ refl
⌜wkᴿ⌝ A (_,_∶[_] {A = A'} ρ x p) =
  let q = (λ i → p i [ π₁ₛ {Aᴹ = A} idSₛ ]ₛ) ∙ (λ i → ⟨ E A' , ≡ʸ→≡ {σʸ = ⌜ A' [ ⌜ ρ ⌝ᴿ ]ₛ ⌝ ∘ₛ π₁ₛ {Aᴹ = A} idSₛ} {⌜ A' ⌝ ∘ₛ (⌜ ρ ⌝ᴿ ∘ₛ π₁ₛ {Aᴹ = A} idSₛ)} refl i ⟩!)
      q' = (λ i → p i [ π₁ₛ {Aᴹ = A} idSₛ ]ₛ) ∙ [∘]Tₛ A' (π₁ₛ {Aᴹ = A} idSₛ) ⌜ ρ ⌝ᴿ ∙ cong (A' [_]ₛ) (⌜wkᴿ⌝ A ρ)
  in {! !} 
  {-
  ,∘ₛ ⌜ ρ ⌝ᴿ ⌜ x ⌝ⱽ (π₁ₛ {Aᴹ = A} idSₛ) p q ∙ cong,∶[]ₛ q q' (⌜wkᴿ⌝ A ρ) (λ _ → ⌜ x ⌝ⱽ [ π₁ₛ {Aᴹ = A} idSₛ ]tₛ)
  (_,ₛ_∶[_] {Aᴹ = A'} ⌜ ρ ⌝ᴿ ⌜ x ⌝ⱽ p) ∘ₛ π₁ₛ {Aᴹ = A} idSₛ
    ≡⟨ ,∘ₛ ⌜ ρ ⌝ᴿ ⌜ x ⌝ⱽ (π₁ₛ {Aᴹ = A} idSₛ) p q ⟩
  _,ₛ_∶[_] {Aᴹ = A'} (⌜ ρ ⌝ᴿ ∘ₛ π₁ₛ {Aᴹ = A} idSₛ) (⌜ x ⌝ⱽ [ π₁ₛ {Aᴹ = A} idSₛ ]tₛ) q
    ≡⟨ cong,∶[]ₛ q q' (⌜wkᴿ⌝ A ρ) refl ⟩
  _,ₛ_∶[_] {Aᴹ = A'} ⌜ wkᴿ A ρ ⌝ᴿ (⌜ x ⌝ⱽ [ π₁ₛ {Aᴹ = A} idSₛ ]tₛ) q'
    ∎
  -}

idR : Ren Γ' Γ'
⌜idR⌝
  : idSₛ {[ Γ' ]ᶜ} ≡ ⌜ idR {Γ'} ⌝ᴿ
idR {∅} = ∅
idR {Γ' , Aₛ} = wkᴿ Aₛ idR , here Aₛ ∶[
  cong (Aₛ [_]ₛ) (≡ʸ→≡ refl ∙ cong (_∘ₛ π₁ₛ {[ Γ' ]ᶜ ,ₛ Aₛ} {[ Γ' ]ᶜ} {Aᴹ = Aₛ} idSₛ) (⌜idR⌝ {Γ'}) ∙ ⌜wkᴿ⌝ {Γ'} Aₛ idR) ]
⌜idR⌝ {∅}       = η∅ₛ _
⌜idR⌝ {Γ' , Aₛ} = 
  idSₛ
    ≡⟨ ηπₛ {Aᴹ = Aₛ} idSₛ ⟩
  _,ₛ_∶[_] {Aᴹ = Aₛ}        
       (π₁ₛ {Aᴹ = Aₛ} idSₛ) 
      -- these implicit arguments are necessary                                         
      -- We have to play with implicit arguments to find out
      -- what arguments are necessary and what are not during
      -- our formalisation.                                                             
       (π₂ₛ {Aᴹ = Aₛ} idSₛ)
       (tyOfπ₂ₛ {Aᴹ = Aₛ} idSₛ)
    ≡⟨ cong,∶[]ₛ {[ Γ' ]ᶜ ,ₛ Aₛ} {[ Γ' ]ᶜ} {Aₛ}
        (tyOfπ₂ₛ {Aᴹ = Aₛ} idSₛ)
        pf
        p
        refl ⟩

  _,ₛ_∶[_] {[ Γ' ]ᶜ ,ₛ Aₛ} {[ Γ' ]ᶜ} {Aₛ}
    ⌜ wkᴿ {Γ'} Aₛ idR ⌝ᴿ (π₂ₛ {Aᴹ = Aₛ} idSₛ) pf

    ≡⟨⟩

  _,ₛ_∶[_] {[ Γ' ]ᶜ ,ₛ Aₛ} {[ Γ' ]ᶜ} {Aₛ}
    ⌜ wkᴿ {Γ'} {Γ'} Aₛ (idR {Γ'}) ⌝ᴿ ⌜ here {Γ'} Aₛ ⌝ⱽ pf 
    
    ≡⟨ {!!} ⟩ -- Is this Agda's bug? 

  _,ₛ_∶[_] {[ Γ' , Aₛ ]ᶜ} {[ Γ' ]ᶜ} {Aₛ}
    ⌜ wkᴿ {Γ'} {Γ'} Aₛ (idR {Γ'}) ⌝ᴿ ⌜ here {Γ'} Aₛ ⌝ⱽ pf 
    
    ≡⟨⟩ 

  ⌜ idR {Γ' , Aₛ} ⌝ᴿ

    ∎
  where
    p : π₁ₛ {Aᴹ = Aₛ} idSₛ ≡ ⌜ wkᴿ {Γ'} Aₛ idR ⌝ᴿ
    p = ≡ʸ→≡ refl ∙ cong (_∘ₛ π₁ₛ {Aᴹ = Aₛ} idSₛ) (⌜idR⌝ {Γ'}) ∙ ⌜wkᴿ⌝ {Γ'} Aₛ idR
    pf : tyOfₛ (π₂ₛ {Aᴹ = Aₛ} idSₛ) ≡ (Aₛ [ ⌜_⌝ᴿ {Γ' , Aₛ} {Γ'} (wkᴿ {Γ'} {Γ'} Aₛ (idR {Γ'})) ]ₛ) 
    pf = cong (Aₛ [_]ₛ)
      (≡ʸ→≡ refl ∙ (cong (_∘ₛ π₁ₛ {Aᴹ = Aₛ} (idSₛ {[ Γ' ]ᶜ ,ₛ Aₛ})) (⌜idR⌝ {Γ'})) ∙ (⌜wkᴿ⌝ Aₛ (idR {Γ'})))

lookupVar-wkᴿ
  : {A : Tyₛ [ Γ' ]ᶜ}(ρ : Ren Γ' Δ')(x : Var Δ')
  → lookupVar (wkᴿ A ρ) x ≡ there A (lookupVar ρ x)
lookupVar-wkᴿ (_ , _ ∶[ _ ]) (here _) = refl
lookupVar-wkᴿ {A = A} (ρ , _ ∶[ _ ]) (there _ x) = lookupVar-wkᴿ {A = A} ρ x

lookupVar-idR
  : (x : Var Γ')
  → lookupVar idR x ≡ x
lookupVar-idR (here _) = refl
lookupVar-idR (there Bₛ x) = lookupVar-wkᴿ idR x ∙ cong (there Bₛ) (lookupVar-idR x)

_⊙_
  : Ren Δ' Θ' → Ren Γ' Δ'
  → Ren Γ' Θ'
⌜⊙⌝
  : (ρ : Ren Δ' Θ')(ρ' : Ren Γ' Δ')
  → ⌜ ρ ⌝ᴿ ∘ₛ ⌜ ρ' ⌝ᴿ ≡ ⌜ ρ ⊙ ρ' ⌝ᴿ
∅ ⊙ ρ' = ∅
(_,_∶[_] {A = Aₛ} ρ x p) ⊙ ρ' = ρ ⊙ ρ' , lookupVar ρ' x ∶[ q ]
  module ⊙Eq where
    q : tyOfₛ ⌜ lookupVar ρ' x ⌝ⱽ ≡ Aₛ [ ⌜ ρ ⊙ ρ' ⌝ᴿ ]ₛ
    q = cong tyOfₛ (sym (⌜lookupVar⌝ ρ' x))
      ∙ (λ i → p i [ ⌜ ρ' ⌝ᴿ ]ₛ)
      ∙ (λ i → ⟨ E Aₛ , ≡ʸ→≡ {σʸ = ⌜ Aₛ [ ⌜ ρ ⌝ᴿ ]ₛ ⌝ ∘ₛ ⌜ ρ' ⌝ᴿ} {⌜ Aₛ ⌝ ∘ₛ (⌜ ρ ⌝ᴿ ∘ₛ ⌜ ρ' ⌝ᴿ)} refl i ⟩!)
      ∙ cong (Aₛ [_]ₛ) (⌜⊙⌝ ρ ρ') 
⌜⊙⌝ ∅ ρ' = ∅Sₛ ∘ₛ ⌜ ρ' ⌝ᴿ ≡ʸ⟨ refl ⟩ ∅Sₛ ∎
⌜⊙⌝ (_,_∶[_] {A = Aₛ} ρ x p) ρ' =
  (_,ₛ_∶[_] {Aᴹ = Aₛ} ⌜ ρ ⌝ᴿ ⌜ x ⌝ⱽ p) ∘ₛ ⌜ ρ' ⌝ᴿ
    ≡⟨ ,∘ₛ {Aᴹ = Aₛ} ⌜ ρ ⌝ᴿ ⌜ x ⌝ⱽ ⌜ ρ' ⌝ᴿ p q ⟩
  _,ₛ_∶[_] {Aᴹ = Aₛ} (⌜ ρ ⌝ᴿ ∘ₛ ⌜ ρ' ⌝ᴿ) (⌜ x ⌝ⱽ [ ⌜ ρ' ⌝ᴿ ]tₛ) q
    ≡⟨ cong,∶[]ₛ {Aᴹ = Aₛ} q (⊙Eq.q {A = Aₛ} ρ x p ρ') (⌜⊙⌝ ρ ρ') (⌜lookupVar⌝ ρ' x) ⟩
  _,ₛ_∶[_] {Aᴹ = Aₛ} ⌜ ρ ⊙ ρ' ⌝ᴿ ⌜ lookupVar ρ' x ⌝ⱽ (⊙Eq.q {A = Aₛ} ρ x p ρ')
    ∎
  where
    q : tyOfₛ (⌜ x ⌝ⱽ [ ⌜ ρ' ⌝ᴿ ]tₛ) ≡ Aₛ [ ⌜ ρ ⌝ᴿ ∘ₛ ⌜ ρ' ⌝ᴿ ]ₛ
    q = cong (_[ ⌜ ρ' ⌝ᴿ ]ₛ) p
      ∙ λ i → ⟨ E Aₛ , ≡ʸ→≡ {σʸ = ⌜ Aₛ [ ⌜ ρ ⌝ᴿ ]ₛ ⌝ ∘ₛ ⌜ ρ' ⌝ᴿ} {⌜ Aₛ ⌝ ∘ₛ (⌜ ρ ⌝ᴿ ∘ₛ ⌜ ρ' ⌝ᴿ)} refl i ⟩!

lookupVar⊙
  : (ρ : Ren Δ' Θ')(ρ' : Ren Γ' Δ')(x : Var Θ')
  → lookupVar ρ' (lookupVar ρ x) ≡ lookupVar (ρ ⊙ ρ') x
lookupVar⊙ (_ , _ ∶[ _ ]) _  (here _)     = refl
lookupVar⊙ (ρ , _ ∶[ _ ]) ρ' (there Bₛ x) = lookupVar⊙ ρ ρ' x

wkᴿ⊙
  : (ρ : Ren Δ' Θ')(ρ' : Ren Γ' Δ'){A : Tyₛ [ Δ' ]ᶜ}
  → (x : Var Γ')(p : tyOfₛ ⌜ x ⌝ⱽ ≡ A [ ⌜ ρ' ⌝ᴿ ]ₛ)
  → wkᴿ A ρ ⊙ (ρ' , x ∶[ p ]) ≡ ρ ⊙ ρ'
wkᴿ⊙ ∅ ρ' x p = refl
wkᴿ⊙ (ρ , x ∶[ p ]) ρ' {A} x' p' =
  wkᴿ A ρ ⊙ (ρ' , x' ∶[ p' ]) , lookupVar ρ' x ∶[ _ ]
    ≡⟨ cong,∶[]ᴿ (wkᴿ⊙ ρ ρ' x' p') refl ⟩
  (ρ ⊙ ρ') , lookupVar ρ' x ∶[ _ ]
    ∎

idR⊙
  : (ρ : Ren Γ' Δ')
  → idR ⊙ ρ ≡ ρ
idR⊙ {_} {.∅} ∅ = refl
idR⊙ {_} {Δ} (ρ , x ∶[ p ]) = cong,∶[]ᴿ (wkᴿ⊙ idR ρ x p ∙ idR⊙ ρ) refl

_⊙idR : (ρ : Ren Γ' Δ') → ρ ⊙ idR ≡ ρ
∅ ⊙idR = refl
(ρ , x ∶[ p ]) ⊙idR = cong,∶[]ᴿ (ρ ⊙idR) (lookupVar-idR x)

⊙-assoc
  : (ρ : Ren Γ' Δ')(ρ' : Ren Δ' Θ')(ρ'' : Ren Θ' Ξ')
  → (ρ'' ⊙ ρ') ⊙ ρ ≡ ρ'' ⊙ (ρ' ⊙ ρ)
⊙-assoc ρ ρ' ∅ = refl
⊙-assoc ρ ρ' (ρ'' , x ∶[ p ]) =
  cong,∶[]ᴿ (⊙-assoc ρ ρ' ρ'') (lookupVar⊙ ρ' ρ x)

-- 
-- open import Theory.SC.QIIRT-tyOf.Models.Yoneda

-- Evaluate substitutions and terms to renamings and variables
-- evalSub : (σ : Subₛ [ Γ' ]ᶜ [ Δ' ]ᶜ) → Σ[ ρ ∈ Ren Γ' Δ' ] σ ≡ ⌜ ρ ⌝ᴿ
-- evalTm : (t : Tmₛ [ Γ' ]ᶜ) → Σ[ x ∈ Var Γ' ] t ≡ ⌜ x ⌝ⱽ
-- evalSub (y , natʸ) = {!   !}
-- evalTm t = {!   !}
