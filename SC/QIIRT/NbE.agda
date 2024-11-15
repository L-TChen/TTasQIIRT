module SC.QIIRT.NbE where

open import Prelude
open import SC.QIIRT.Base

data NeSub : (Δ Γ : Ctx) → Sub Δ Γ → Set where
  idS : NeSub Δ Δ idS
  π₁  : NeSub Δ (Γ ‣ A) σ → NeSub Δ Γ (π₁ σ)

data NfTm : (Γ : Ctx)(A : Ty Γ) → Tm Γ A → Set where
  π₂ : NeSub Δ (Γ ‣ A) σ → NfTm Δ (A [ π₁ σ ]) (π₂ σ)

data Var : (Γ : Ctx) → Ty Γ → Set where
  here : Var (Γ ‣ A) (A [ π₁ idS ])
  there : Var Γ A → Var (Γ ‣ B) (A [ π₁ idS ])

⌞_⌟V : Var Γ A → Tm Γ A
⌞ here ⌟V = π₂ idS
⌞ there x ⌟V  = ⌞ x ⌟V [ π₁ idS ]t

data Ren : Ctx → Ctx → Set
⌞_⌟R : Ren Δ Γ → Sub Δ Γ

data Ren where
  ∅ : Ren Δ ∅
  _‣_ : (ρ : Ren Δ Γ) → Var Δ (A [ ⌞ ρ ⌟R ]) → Ren Δ (Γ ‣ A)

⌞ ∅ ⌟R = ∅
⌞ σ ‣ t ⌟R = ⌞ σ ⌟R ‣ ⌞ t ⌟V

_↑R_ : Ren Δ Γ → (A : Ty Δ) → Ren (Δ ‣ A) Γ
∅ ↑R A = ∅
(_‣_ {A = U} ρ x) ↑R A = (ρ ↑R A) ‣ there x

idR : Ren Δ Δ
idR {∅} = ∅
idR {Δ ‣ U} = (idR ↑R U) ‣ here

lookupVar : (ρ : Ren Δ Γ) → Var Γ A → Var Δ (A [ ⌞ ρ ⌟R ])
lookupVar (_‣_ {A = U} ρ x) here = x 
lookupVar (_‣_ {A = U} ρ x') (there {A = U} x) = lookupVar ρ x
-- requires A [ π₁ idS ] [ ⌞ ρ ⌟R ‣ ⌞ x ⌟V ] ≡ A [ ⌞ ρ ⌟R ] , but pattern match on U for now

⌞lookup⌟ : (ρ : Ren Δ Γ)(x : Var Γ A) → ⌞ lookupVar ρ x ⌟V ≡ ⌞ x ⌟V [ ⌞ ρ ⌟R ]t
⌞lookup⌟ (_‣_ {A = U} ρ x) here = begin
    ⌞ x ⌟V
  ≡⟨ sym (βπ₂ {σ = ⌞ ρ ⌟R} {⌞ x ⌟V}) ⟩
    π₂ (⌞ ρ ⌟R ‣ ⌞ x ⌟V)
  ≡⟨ cong π₂ (sym (idS∘ (⌞ ρ ⌟R ‣ ⌞ x ⌟V))) ⟩
    π₂ (idS ∘ (⌞ ρ ⌟R ‣ ⌞ x ⌟V))
  ≡⟨ π₂∘ idS (⌞ ρ ⌟R ‣ ⌞ x ⌟V) ⟩
    π₂ idS [ ⌞ ρ ⌟R ‣ ⌞ x ⌟V ]tm
  ≡⟨⟩
    ⌞ here ⌟V [ ⌞ ρ ⌟R ‣ ⌞ x ⌟V ]t
  ∎
⌞lookup⌟ (_‣_ {A = U} ρ x') (there {A = U} x) = begin
    ⌞ lookupVar ρ x ⌟V
  ≡⟨ ⌞lookup⌟ ρ x ⟩
    ⌞ x ⌟V [ ⌞ ρ ⌟R ]t
  ≡⟨ cong (⌞ x ⌟V [_]t) (sym (βπ₁ {σ = ⌞ ρ ⌟R} {⌞ x' ⌟V})) ⟩
    ⌞ x ⌟V [ π₁ (⌞ ρ ⌟R ‣ ⌞ x' ⌟V) ]t
  ≡⟨ cong (⌞ x ⌟V [_]t) (cong π₁ (sym (idS∘ (⌞ ρ ⌟R ‣ ⌞ x' ⌟V)))) ⟩
    ⌞ x ⌟V [ π₁ (idS ∘ (⌞ ρ ⌟R ‣ ⌞ x' ⌟V)) ]t
  ≡⟨ cong (⌞ x ⌟V [_]t) (π₁∘ idS (⌞ ρ ⌟R ‣ ⌞ x' ⌟V)) ⟩
    ⌞ x ⌟V [ π₁ idS ∘ (⌞ ρ ⌟R ‣ ⌞ x' ⌟V) ]t
  ≡⟨⟩
    ⌞ x ⌟V [ π₁ idS ]t [ ⌞ ρ ⌟R ‣ ⌞ x' ⌟V ]t
  ≡⟨⟩
    ⌞ there x ⌟V [ ⌞ ρ ⌟R ‣ ⌞ x' ⌟V ]t
  ∎

_⊙_ : Ren Δ Γ → Ren Θ Δ → Ren Θ Γ
⌞⊙⌟ : (ρ : Ren Δ Γ)(ρ' : Ren Θ Δ) → ⌞ ρ ⊙ ρ' ⌟R ≡ ⌞ ρ ⌟R ∘ ⌞ ρ' ⌟R
∅ ⊙ _ = ∅
_‣_ {A = U} ρ x ⊙ ρ' = (ρ ⊙ ρ') ‣ lookupVar ρ' x
⌞⊙⌟ ∅ ρ' = sym η∅
⌞⊙⌟ (_‣_ {A = U} ρ x) ρ' = begin 
    ⌞ ρ ⊙ ρ' ⌟R ‣ ⌞ lookupVar ρ' x ⌟V
  ≡⟨ cong (_‣ ⌞ lookupVar ρ' x ⌟V) (⌞⊙⌟ ρ ρ') ⟩
    (⌞ ρ ⌟R ∘ ⌞ ρ' ⌟R) ‣ ⌞ lookupVar ρ' x ⌟V
  ≡⟨ cong ((⌞ ρ ⌟R ∘ ⌞ ρ' ⌟R) ‣_) (⌞lookup⌟ ρ' x) ⟩ 
    (⌞ ρ ⌟R ∘ ⌞ ρ' ⌟R) ‣ ⌞ x ⌟V [ ⌞ ρ' ⌟R ]t
  ≡⟨ sym (‣∘ {A = U} {⌞ ρ ⌟R} {⌞ x ⌟V} {⌞ ρ' ⌟R}) ⟩
    (⌞ ρ ⌟R ‣ ⌞ x ⌟V) ∘ ⌞ ρ' ⌟R
  ∎

reifyTm : Tm Γ A → Var Γ A
reifySub : Sub Γ Δ → Ren Γ Δ
reifyTm (π₂ {A = U} σ) with reifySub σ
... | ρ ‣ x = x
reifyTm (t [ σ ]tm) with reifyTm t | reifySub σ
... | here  {A = U}   | ρ ‣ x  = x
... | there {A = U} x | ρ ‣ x' = lookupVar ρ x
reifySub ∅ = ∅ 
reifySub (σ ‣ t) = reifySub σ ‣ reifyTm t
reifySub {∅} idS = ∅
reifySub {Γ ‣ U} idS = idR
reifySub (σ ∘ τ) = reifySub σ ⊙ reifySub τ
reifySub (π₁ σ) with reifySub σ
... | ρ ‣ _ = ρ 