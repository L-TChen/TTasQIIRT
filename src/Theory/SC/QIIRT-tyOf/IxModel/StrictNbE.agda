{-# OPTIONS -WnoUnsupportedIndexedMatch --lossy-unification #-}

{-
  With --lossy-unification enabled,
  we even don't need to fill in impicit arguments!
  As strict interpretation of constructors are injective, using lossy unification shall be consistent.

  Can we just turn on lossy-unification for these definitions?
-}

module Theory.SC.QIIRT-tyOf.IxModel.StrictNbE where

open import Prelude
open import Theory.SC.QIIRT-tyOf.Model

open import Theory.SC.QIIRT-tyOf.Model.StrictTerm
open SC Termₛ
  renaming (module Var to GVar)
open GVar

open import Theory.SC.QIIRT-tyOf.Model.Term
  using (Term; Ctx-is-Set)

open import Theory.SC.QIIRT-tyOf.Model.Yoneda Term
open Subʸ

open import Theory.SC.QIIRT-tyOf.Model.LocalNoQuotient よ Ctx-is-Set
open Ty³

-- Ctx' is defined in order to pattern match in Var
data Ctx' : Set
[_]ᶜ : Ctx' → Ctx

data Ctx' where
  ∅'
    : Ctx'
  _,'_
    : (Γ' : Ctx') (Aₛ : Ty [ Γ' ]ᶜ)
    → Ctx'

[ ∅'       ]ᶜ = ∅
[ Γ' ,' Aₛ ]ᶜ = [ Γ' ]ᶜ ,C Aₛ

variable
  Γ' Δ' Θ' Ξ' : Ctx'

-- Definition of neutral and normal forms

data NfTy (Γ : Ctx) : Set where
  `U : NfTy Γ

⌜_⌝ty : NfTy Γ → Ty Γ
⌜ `U ⌝ty = U

data NeSub (Γ : Ctx) : Ctx → Set where
  `∅S
    : NeSub Γ ∅
  `idS
    : NeSub Γ Γ
  `π₁
    : (A : Ty Δ) → NeSub Γ (Δ ,C A)
    → NeSub Γ Δ

⌜_⌝subⁿᵉ : NeSub Γ Δ → Sub Γ Δ
⌜ `∅S     ⌝subⁿᵉ = ∅S
⌜ `idS    ⌝subⁿᵉ = idS
⌜ `π₁ A σ ⌝subⁿᵉ = π₁ ⌜ σ ⌝subⁿᵉ

data NeTm (Γ : Ctx) : Set where
  `π₂
    : (A : Ty Δ) → NeSub Γ (Δ ,C A)
    → NeTm Γ

⌜_⌝tm
  : NeTm Γ
  → Tm Γ
⌜ `π₂ A σⁿᵉ ⌝tm = π₂ ⌜ σⁿᵉ ⌝subⁿᵉ
--
data NfSub (Γ : Ctx) : Ctx → Set
⌜_⌝subⁿᶠ
  : NfSub Γ Δ
  → Sub Γ Δ

data NfSub Γ where
  `ne_
    : NeSub Γ Δ
    → NfSub Γ Δ
  _`,_∶[_]
    : (σⁿᶠ : NfSub Γ Δ)(tⁿᵉ : NeTm Γ)
    → tyOf (⌜ tⁿᵉ ⌝tm) ≡ A [ ⌜ σⁿᶠ ⌝subⁿᶠ ]T
    → NfSub Γ (Δ ,C A)

⌜ `ne σⁿᵉ ⌝subⁿᶠ = ⌜ σⁿᵉ ⌝subⁿᵉ
⌜ _`,_∶[_] {A = A} σⁿᶠ tⁿᵉ p ⌝subⁿᶠ =
  ⌜ σⁿᶠ ⌝subⁿᶠ , ⌜ tⁿᵉ ⌝tm ∶[ p ]

-- Definitions of variables and renamings
data Var : (Γ' : Ctx') → Set where
  here
    : {Aₛ : Ty [ Γ' ]ᶜ}
    → Var (Γ' ,' Aₛ)
  there
    : {Bₛ : Ty [ Γ' ]ᶜ}
    → Var Γ'
    → Var (Γ' ,' Bₛ)

⌜_⌝ⱽ
  : Var Γ'
  → Tm [ Γ' ]ᶜ
⌜ here    ⌝ⱽ = π₂ idS
⌜ there x ⌝ⱽ = ⌜ x ⌝ⱽ [ π₁ idS ]t

tyOfⱽ
  : Var Γ'
  → Σ[ Δ' ∈ Ctx' ] Σ[ σ ∈ Sub [ Γ' ]ᶜ [ Δ' ]ᶜ ] Ty [ Δ' ]ᶜ
tyOfⱽ (here {Γ'} {Aₛ})    = Γ' , π₁ idS , Aₛ
tyOfⱽ (there x) =
  let (Δ' , σ , Aₛ) = tyOfⱽ x in
  Δ' , σ ∘ π₁ idS , Aₛ

tyOfⱽ-sound
  : (x : Var Γ')
  → tyOf ⌜ x ⌝ⱽ ≡ let (_ , σ , Aₛ) = tyOfⱽ x in Aₛ [ σ ]T
tyOfⱽ-sound here      = refl
tyOfⱽ-sound (there x) = cong _[ π₁ idS ]T (tyOfⱽ-sound x)

data Ren : Ctx' → Ctx' → Set
⌜_⌝ᴿ : Ren Γ' Δ' → Sub [ Γ' ]ᶜ [ Δ' ]ᶜ

data Ren where
  ∅R
    : Ren Γ' ∅'
  _,R_∶[_]
    : (ρ : Ren Γ' Δ')(x : Var Γ')
    → tyOf ⌜ x ⌝ⱽ ≡ A [ ⌜ ρ ⌝ᴿ ]T
    → Ren Γ' (Δ' ,' A)

cong,∶[]ᴿ
  : {ρ ρ' : Ren Γ' Δ'}{x x' : Var Γ'}{p : tyOf ⌜ x ⌝ⱽ ≡ A [ ⌜ ρ ⌝ᴿ ]T}{p' : tyOf ⌜ x' ⌝ⱽ ≡ A [ ⌜ ρ' ⌝ᴿ ]T}
  → ρ ≡ ρ' → x ≡ x'
  → ρ ,R x ∶[ p ] ≡ ρ' ,R x' ∶[ p' ]
cong,∶[]ᴿ {A = A} {p = p} {p'} ρ≡ρ' x≡x' i = _,R_∶[_] (ρ≡ρ' i) (x≡x' i)
    (isSet→SquareP (λ _ _ → Ty³-is-set) p p' (λ i → tyOf ⌜ x≡x' i ⌝ⱽ) (λ i → A [ ⌜ ρ≡ρ' i ⌝ᴿ ]T) i)

⌜ ∅R ⌝ᴿ              = ∅S
⌜ _,R_∶[_] ρ x p ⌝ᴿ = ⌜ ρ ⌝ᴿ , ⌜ x ⌝ⱽ ∶[ p ]

lookupVar
  : (ρ : Ren Γ' Δ') → Var Δ'
  → Var Γ'
lookupVar (_ ,R x ∶[ _ ]) here = x
lookupVar (ρ ,R _ ∶[ _ ]) (there x) = lookupVar ρ x

⌜lookupVar⌝
  : (ρ : Ren Γ' Δ')(x : Var Δ')
  → ⌜ x ⌝ⱽ [ ⌜ ρ ⌝ᴿ ]t ≡ ⌜ lookupVar ρ x ⌝ⱽ
⌜lookupVar⌝ (ρ ,R x ∶[ p ]) here =
  sym (π₂idS (⌜ ρ ⌝ᴿ , ⌜ x ⌝ⱽ ∶[ p ])) ∙ βπ₂ ⌜ ρ ⌝ᴿ ⌜ x ⌝ⱽ p
⌜lookupVar⌝ (ρ ,R x' ∶[ p ]) (there x) =
  [∘]t ⌜ x ⌝ⱽ (⌜ ρ ⌝ᴿ ,  ⌜ x' ⌝ⱽ ∶[ p ]) (π₁ idS)
  ∙ (λ i → ⌜ x ⌝ⱽ [ π₁idS (⌜ ρ ⌝ᴿ , ⌜ x' ⌝ⱽ ∶[ p ]) (~ i) ]t)
  ∙ (λ i → ⌜ x ⌝ⱽ [ βπ₁ ⌜ ρ ⌝ᴿ ⌜ x' ⌝ⱽ p i ]t)
  ∙ ⌜lookupVar⌝ ρ x
{-
  -- Without lossy-unification, we need the following implicit arugments
  -- to type check:
  sym (π₂idSₛ {Aᴹ = Aₛ} (_,ₛ_∶[_] {Aᴹ = Aₛ} ⌜ ρ ⌝ᴿ ⌜ x ⌝ⱽ p)) ∙ βπ₂ₛ {Aᴹ = Aₛ} ⌜ ρ ⌝ᴿ ⌜ x ⌝ⱽ p
⌜lookupVar⌝ (ρ , x' ∶[ p ]) (there Bₛ x) =
  [∘]tₛ ⌜ x ⌝ⱽ (_,ₛ_∶[_] {Aᴹ = Bₛ} ⌜ ρ ⌝ᴿ ⌜ x' ⌝ⱽ p) (π₁ₛ {Aᴹ = Bₛ} idSₛ)
  ∙ (λ i → ⌜ x ⌝ⱽ [ π₁idSₛ {Aᴹ = Bₛ} (_,ₛ_∶[_] {Aᴹ = Bₛ} ⌜ ρ ⌝ᴿ ⌜ x' ⌝ⱽ p) (~ i) ]tₛ)
  ∙ (λ i → ⌜ x ⌝ⱽ [ βπ₁ₛ {Aᴹ = Bₛ} ⌜ ρ ⌝ᴿ ⌜ x' ⌝ⱽ p i ]tₛ)
  ∙ ⌜lookupVar⌝ ρ x
-}

η∅ᴿ
  : (ρ : Ren Γ' ∅')
  → ρ ≡ ∅R
η∅ᴿ ∅R = refl

η,ᴿ
  : (ρ : Ren Γ' (Δ' ,' A))
  → Σ[ ρ' ∈ Ren Γ' Δ' ] Σ[ x' ∈ Var Γ' ] Σ[ p' ∈ tyOf ⌜ x' ⌝ⱽ ≡ A [ ⌜ ρ' ⌝ᴿ ]T ]
    ρ ≡ ρ'  ,R x' ∶[ p' ]
η,ᴿ (ρ ,R x ∶[ p ]) = ρ , x , p , refl

wkᴿ
  : (A : Ty [ Γ' ]ᶜ) → Ren Γ' Δ'
  → Ren (Γ' ,' A) Δ'
⌜wkᴿ⌝
  : (A : Ty [ Γ' ]ᶜ)(ρ : Ren Γ' Δ')
  → ⌜ ρ ⌝ᴿ ∘ π₁ idS ≡ ⌜ wkᴿ A ρ ⌝ᴿ

wkᴿ A ∅R = ∅R
wkᴿ A (_,R_∶[_] {A = A'} ρ x p) =
  wkᴿ A ρ  ,R there x ∶[ cong _[ π₁ idS ]T p ∙ cong (A' [_]T) (⌜wkᴿ⌝ A ρ) ]

⌜wkᴿ⌝ A ∅R = refl
⌜wkᴿ⌝ A (_,R_∶[_] {A = A'} ρ x p) =
 let q : tyOf (⌜ x ⌝ⱽ [ π₁ idS ]t) ≡ A' [ ⌜ ρ ⌝ᴿ ∘ π₁ idS ]T
     q = cong _[ π₁ idS ]T p
     q' = cong _[ π₁ idS ]T p ∙ cong (A' [_]T) (⌜wkᴿ⌝ A ρ)
 in
  ⌜ ρ ,R x ∶[ p ] ⌝ᴿ ∘ π₁ idS
    ≡⟨  ,∘ ⌜ ρ ⌝ᴿ ⌜ x ⌝ⱽ (π₁ idS) p q ⟩
  (⌜ ρ ⌝ᴿ ∘ π₁ idS) , (⌜ x ⌝ⱽ [ π₁ idS ]t) ∶[ q ]
    ≡⟨ cong,∶[] q q' (⌜wkᴿ⌝ A ρ) refl ⟩
  ⌜ wkᴿ A ρ ⌝ᴿ , (⌜ x ⌝ⱽ [ π₁ idS ]t) ∶[ q' ]
    ∎

idR : Ren Γ' Γ'
⌜idR⌝
  : idS {[ Γ' ]ᶜ} ≡ ⌜ idR {Γ'} ⌝ᴿ
idR {∅'}      = ∅R
idR {Γ' ,' A} = wkᴿ A idR ,R here ∶[ cong (A [_]T) (cong (_∘ π₁ idS) ⌜idR⌝ ∙ ⌜wkᴿ⌝ A idR) ]
⌜idR⌝ {∅'}      = η∅ _
⌜idR⌝ {Γ' ,' A} =
  idS
    ≡⟨ ηπ idS ⟩
  (π₁ idS) , (π₂ idS) ∶[ tyOfπ₂ idS ]
    ≡⟨ cong,∶[] (tyOfπ₂ idS) pf p refl ⟩
  ⌜ wkᴿ {Γ'} A idR ⌝ᴿ , (π₂ idS) ∶[ pf ]
    ≡⟨⟩
  ⌜ idR {Γ' ,' A} ⌝ᴿ
    ∎
  where
    p : π₁ idS ≡ ⌜ wkᴿ A idR ⌝ᴿ
    p = cong (_∘ π₁ idS) ⌜idR⌝ ∙ ⌜wkᴿ⌝ A idR
    pf : tyOf (π₂ idS) ≡ (A [ ⌜_⌝ᴿ (wkᴿ A idR) ]T)
    pf = cong (A [_]T)
      (cong (_∘ π₁ idS) ⌜idR⌝ ∙ ⌜wkᴿ⌝ A idR)

lookupVar-wkᴿ
  : {A : Ty [ Γ' ]ᶜ}(ρ : Ren Γ' Δ')(x : Var Δ')
  → lookupVar (wkᴿ A ρ) x ≡ there (lookupVar ρ x)
lookupVar-wkᴿ (_ ,R _ ∶[ _ ]) here = refl
lookupVar-wkᴿ (ρ ,R _ ∶[ _ ]) (there x) = lookupVar-wkᴿ ρ x

lookupVar-idR
  : (x : Var Γ')
  → lookupVar idR x ≡ x
lookupVar-idR here = refl
lookupVar-idR (there x) =
  lookupVar-wkᴿ idR x ∙ cong there (lookupVar-idR x)

_⊙_
  : Ren Δ' Θ' → Ren Γ' Δ'
  → Ren Γ' Θ'
⌜⊙⌝
  : (ρ : Ren Δ' Θ')(ρ' : Ren Γ' Δ')
  → ⌜ ρ ⌝ᴿ ∘ ⌜ ρ' ⌝ᴿ ≡ ⌜ ρ ⊙ ρ' ⌝ᴿ
∅R                       ⊙ ρ' = ∅R
(_,R_∶[_] {A = A} ρ x p) ⊙ ρ' =
  (ρ ⊙ ρ') ,R lookupVar ρ' x ∶[ q ]
  module ⊙Eq where
    q : tyOf ⌜ lookupVar ρ' x ⌝ⱽ ≡ A [ ⌜ ρ ⊙ ρ' ⌝ᴿ ]T
    q = cong tyOf (sym (⌜lookupVar⌝ ρ' x))
      ∙ (λ i → p i [ ⌜ ρ' ⌝ᴿ ]T)
      ∙ (λ i → ⟨ E A , ≡ʸ→≡ {σʸ = ⌜ A [ ⌜ ρ ⌝ᴿ ]T ⌝ ∘ ⌜ ρ' ⌝ᴿ} {⌜ A ⌝ ∘ (⌜ ρ ⌝ᴿ ∘ ⌜ ρ' ⌝ᴿ)} refl i ⟩!)
      ∙ cong (A [_]T) (⌜⊙⌝ ρ ρ')
⌜⊙⌝ ∅R ρ'                       = refl
⌜⊙⌝ (_,R_∶[_] {A = A} ρ x p) ρ' =
  (⌜ ρ ⌝ᴿ , ⌜ x ⌝ⱽ ∶[ p ]) ∘ ⌜ ρ' ⌝ᴿ
    ≡⟨ ,∘ ⌜ ρ ⌝ᴿ ⌜ x ⌝ⱽ ⌜ ρ' ⌝ᴿ p q ⟩
  (⌜ ρ ⌝ᴿ ∘ ⌜ ρ' ⌝ᴿ) , (⌜ x ⌝ⱽ [ ⌜ ρ' ⌝ᴿ ]t) ∶[ q ]
    ≡⟨ cong,∶[] q (⊙Eq.q ρ x p ρ') (⌜⊙⌝ ρ ρ') (⌜lookupVar⌝ ρ' x) ⟩
  ⌜ ρ ⊙ ρ' ⌝ᴿ , ⌜ lookupVar ρ' x ⌝ⱽ ∶[ ⊙Eq.q {A = A} ρ x p ρ' ]
    ∎
  where
    q : tyOf (⌜ x ⌝ⱽ [ ⌜ ρ' ⌝ᴿ ]t) ≡ A [ ⌜ ρ ⌝ᴿ ∘ ⌜ ρ' ⌝ᴿ ]T
    q = cong (_[ ⌜ ρ' ⌝ᴿ ]T) p

lookupVar⊙
  : (ρ : Ren Δ' Θ')(ρ' : Ren Γ' Δ')(x : Var Θ')
  → lookupVar ρ' (lookupVar ρ x) ≡ lookupVar (ρ ⊙ ρ') x
lookupVar⊙ (_ ,R _ ∶[ _ ]) _  here      = refl
lookupVar⊙ (ρ ,R _ ∶[ _ ]) ρ' (there x) = lookupVar⊙ ρ ρ' x

wkᴿ⊙
  : (ρ : Ren Δ' Θ')(ρ' : Ren Γ' Δ'){A : Ty [ Δ' ]ᶜ}
  → (x : Var Γ')(p : tyOf ⌜ x ⌝ⱽ ≡ A [ ⌜ ρ' ⌝ᴿ ]T)
  → wkᴿ A ρ ⊙ (ρ' ,R x ∶[ p ]) ≡ ρ ⊙ ρ'
wkᴿ⊙ ∅R ρ' x p = refl
wkᴿ⊙ (ρ ,R x ∶[ p ]) ρ' {A} x' p' = cong,∶[]ᴿ (wkᴿ⊙ ρ ρ' x' p') refl

idR⊙
  : (ρ : Ren Γ' Δ')
  → idR ⊙ ρ ≡ ρ
idR⊙ {_} {∅} ∅R = refl
idR⊙ {_} {Δ} (ρ ,R x ∶[ p ]) = cong,∶[]ᴿ (wkᴿ⊙ idR ρ x p ∙ idR⊙ ρ) refl

_⊙idR : (ρ : Ren Γ' Δ') → ρ ⊙ idR ≡ ρ
∅R              ⊙idR = refl
(ρ ,R x ∶[ p ]) ⊙idR = cong,∶[]ᴿ (ρ ⊙idR) (lookupVar-idR x)

⊙-assoc
  : (ρ : Ren Γ' Δ')(ρ' : Ren Δ' Θ')(ρ'' : Ren Θ' Ξ')
  → (ρ'' ⊙ ρ') ⊙ ρ ≡ ρ'' ⊙ (ρ' ⊙ ρ)
⊙-assoc ρ ρ' ∅R = refl
⊙-assoc ρ ρ' (ρ'' ,R x ∶[ p ]) =
  cong,∶[]ᴿ (⊙-assoc ρ ρ' ρ'') (lookupVar⊙ ρ' ρ x)
