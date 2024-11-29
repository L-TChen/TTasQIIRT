module SC.QIIRT.NbE where

open import Prelude
open ≡-Reasoning
open import Data.Product
open import SC.QIIRT.Base
open import SC.QIIRT.Model
open import SC.QIIRT.Elimination

-- Definition of Variables and Renaming
-- with embedding into Tm and Sub
data Var : (Γ : Ctx) → Ty Γ → Set where
  here  : Var (Γ ‣ A) (A [ π₁ idS ])
  there : Var Γ A → Var (Γ ‣ B) (A [ π₁ idS ])

⌞_⌟V : Var Γ A → Tm Γ A
⌞ here ⌟V = π₂ idS
⌞ there x ⌟V  = ⌞ x ⌟V [ π₁ idS ]tm

data Ren : Ctx → Ctx → Set
⌞_⌟R : Ren Δ Γ → Sub Δ Γ

data Ren where
  ∅ : Ren Δ ∅
  _‣_ : (ρ : Ren Δ Γ) → Var Δ (A [ ⌞ ρ ⌟R ]) → Ren Δ (Γ ‣ A)

⌞ ∅ ⌟R = ∅
⌞ σ ‣ t ⌟R = ⌞ σ ⌟R ‣ ⌞ t ⌟V

-- Operations about renamings: lift, identity, and variable lookup
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

-- Several lemmas
⌞lookup⌟ : (ρ : Ren Δ Γ)(x : Var Γ A) → ⌞ lookupVar ρ x ⌟V ≡ ⌞ x ⌟V [ ⌞ ρ ⌟R ]tm
⌞lookup⌟ (_‣_ {A = U} ρ x) here = begin
    ⌞ x ⌟V
  ≡⟨ sym (βπ₂ {σ = ⌞ ρ ⌟R} {⌞ x ⌟V}) ⟩
    π₂ (⌞ ρ ⌟R ‣ ⌞ x ⌟V)
  ≡⟨ cong π₂ (sym (idS∘ (⌞ ρ ⌟R ‣ ⌞ x ⌟V))) ⟩
    π₂ (idS ∘ (⌞ ρ ⌟R ‣ ⌞ x ⌟V))
  ≡⟨ π₂∘ idS (⌞ ρ ⌟R ‣ ⌞ x ⌟V) ⟩ -- TODO: turn into lemma
    π₂ idS [ ⌞ ρ ⌟R ‣ ⌞ x ⌟V ]tm
  ≡⟨⟩
    ⌞ here ⌟V [ ⌞ ρ ⌟R ‣ ⌞ x ⌟V ]tm
  ∎
⌞lookup⌟ (_‣_ {A = U} ρ x') (there {A = U} x) = begin
    ⌞ lookupVar ρ x ⌟V
  ≡⟨ ⌞lookup⌟ ρ x ⟩
    ⌞ x ⌟V [ ⌞ ρ ⌟R ]tm
  ≡⟨ cong (⌞ x ⌟V [_]tm) (sym (βπ₁ {σ = ⌞ ρ ⌟R} {⌞ x' ⌟V})) ⟩
    ⌞ x ⌟V [ π₁ (⌞ ρ ⌟R ‣ ⌞ x' ⌟V) ]tm -- could use lemma
  ≡⟨ cong (⌞ x ⌟V [_]tm) (cong π₁ (sym (idS∘ (⌞ ρ ⌟R ‣ ⌞ x' ⌟V)))) ⟩
    ⌞ x ⌟V [ π₁ (idS ∘ (⌞ ρ ⌟R ‣ ⌞ x' ⌟V)) ]tm
  ≡⟨ cong (⌞ x ⌟V [_]tm) (π₁∘ idS (⌞ ρ ⌟R ‣ ⌞ x' ⌟V)) ⟩
    ⌞ x ⌟V [ π₁ idS ∘ (⌞ ρ ⌟R ‣ ⌞ x' ⌟V) ]tm
  ≡⟨ [∘]tm ⌞ x ⌟V (π₁ idS) (⌞ ρ ⌟R ‣ ⌞ x' ⌟V) ⟩ -- would be "refl" using recursion _[_]t
    ⌞ x ⌟V [ π₁ idS ]tm [ ⌞ ρ ⌟R ‣ ⌞ x' ⌟V ]tm
  ≡⟨⟩
    ⌞ there x ⌟V [ ⌞ ρ ⌟R ‣ ⌞ x' ⌟V ]tm
  ∎

⌞↑⌟ : (ρ : Ren Δ Γ)(A : Ty Δ) → ⌞ ρ ↑R A ⌟R ≡ ⌞ ρ ⌟R ∘ π₁ idS
⌞↑⌟ ∅ A = sym η∅
⌞↑⌟ (_‣_ {A = U} ρ x) A = begin
    ⌞ ρ ↑R A ⌟R ‣ ⌞ x ⌟V [ π₁ idS ]tm
  ≡⟨ cong (_‣ ⌞ x ⌟V [ π₁ idS ]tm) (⌞↑⌟ ρ A) ⟩
    (⌞ ρ ⌟R ∘ π₁ idS) ‣ ⌞ x ⌟V [ π₁ idS ]tm
  ≡⟨ sym (‣∘ {σ = ⌞ ρ ⌟R} {⌞ x ⌟V} {π₁ idS}) ⟩
    ((⌞ ρ ⌟R ‣ ⌞ x ⌟V) ∘ π₁ idS)
  ∎

⌞idR⌟ : ⌞ idR {Δ} ⌟R ≡ idS
⌞idR⌟ {∅} = sym η∅
⌞idR⌟ {Δ ‣ U} = begin 
    ⌞ idR ↑R U ⌟R ‣ π₂ idS
  ≡⟨ cong (_‣ π₂ idS) (⌞↑⌟ idR U) ⟩
    (⌞ idR ⌟R ∘ π₁ idS) ‣ π₂ idS
  ≡⟨ cong (λ y → (y ∘ π₁ idS) ‣ π₂ idS) ⌞idR⌟ ⟩
    (idS ∘ π₁ idS) ‣ π₂ idS
  ≡⟨ cong (_‣ π₂ idS) (idS∘ (π₁ idS)) ⟩
    π₁ idS ‣ π₂ idS
  ≡⟨ sym ηπ ⟩
    idS
  ∎

-- Composition of renamings
_⊙_ : Ren Δ Γ → Ren Θ Δ → Ren Θ Γ
∅ ⊙ _ = ∅
_‣_ {A = U} ρ x ⊙ ρ' = (ρ ⊙ ρ') ‣ lookupVar ρ' x

⌞⊙⌟ : (ρ : Ren Δ Γ)(ρ' : Ren Θ Δ) → ⌞ ρ ⊙ ρ' ⌟R ≡ ⌞ ρ ⌟R ∘ ⌞ ρ' ⌟R
⌞⊙⌟ ∅ ρ' = sym η∅
⌞⊙⌟ (_‣_ {A = U} ρ x) ρ' = begin 
    ⌞ ρ ⊙ ρ' ⌟R ‣ ⌞ lookupVar ρ' x ⌟V
  ≡⟨ cong (_‣ ⌞ lookupVar ρ' x ⌟V) (⌞⊙⌟ ρ ρ') ⟩
    (⌞ ρ ⌟R ∘ ⌞ ρ' ⌟R) ‣ ⌞ lookupVar ρ' x ⌟V
  ≡⟨ cong ((⌞ ρ ⌟R ∘ ⌞ ρ' ⌟R) ‣_) (⌞lookup⌟ ρ' x) ⟩ 
    (⌞ ρ ⌟R ∘ ⌞ ρ' ⌟R) ‣ ⌞ x ⌟V [ ⌞ ρ' ⌟R ]tm
  ≡⟨ sym (‣∘ {A = U} {⌞ ρ ⌟R} {⌞ x ⌟V} {⌞ ρ' ⌟R}) ⟩
    (⌞ ρ ⌟R ‣ ⌞ x ⌟V) ∘ ⌞ ρ' ⌟R
  ∎

-- Reification of terms and substitutions into variables and renamings
---- This is feasible because the only type is U for now
DomainDecl : Pdc
DomainDecl .Pdc.PCtx Γ = Σ[ Γ' ∈ Ctx ] Γ ≡ Γ'
DomainDecl .Pdc.PTy (Γ , refl) A = Σ[ A' ∈ Ty Γ ] A ≡ A'
DomainDecl .Pdc.PSub (Γ , refl) (Δ , refl) σ = Σ[ ρ ∈ Ren Γ Δ ] σ ≡ ⌞ ρ ⌟R
DomainDecl .Pdc.PTm (Γ , refl) (A , eq) t = Σ[ x ∈ Var Γ A ] conv (congTmΓ eq) t ≡ ⌞ x ⌟V

Domain : IH DomainDecl
IH._[_]P Domain {PΓ = Γ , refl} {PΔ = Δ , refl} (A , eqA) (ρ , eqρ) = A [ ⌞ ρ ⌟R ] , cong[] refl eqA refl eqρ
Domain .IH.∅Ctx = ∅ , refl
Domain .IH._‣Ctx_ (Γ , refl) (A , refl) = Γ ‣ A , refl
Domain .IH.∅Sub {PΔ = Δ , refl} = ∅ , refl
IH._‣Sub_ Domain {PΔ = Δ , refl} {Γ , refl} {A , refl} (ρ , refl) (x , eqx) = ρ ‣ x , cong (⌞ ρ ⌟R ‣_) eqx
Domain .IH.PidS {PΔ = Γ , refl} = idR , sym ⌞idR⌟
Domain .IH._∘P_ {PΓ = Γ , refl} {Δ , refl} {Θ , refl} (ρ , refl) (ρ' , refl) = ρ ⊙ ρ' , sym (⌞⊙⌟ ρ ρ')
Domain .IH.π₁P {PΔ = Δ , refl} {Γ , refl} {A , refl} ((ρ ‣ x) , refl) = ρ , βπ₁
Domain .IH.PU {PΓ = Γ , refl} = U , refl
Domain .IH.PU[] {PΓ = Γ , refl} {Δ , refl} {ρ , refl} = refl
Domain .IH.π₂P {PΔ = Δ , refl} {Γ , refl} {A , refl} ((ρ ‣ x) , refl) = x , eq
  where
    eq : conv (congTmΓ (cong[] refl refl refl (βπ₁ {σ = ⌞ ρ ⌟R} {⌞ x ⌟V}))) (π₂ (⌞ ρ ⌟R ‣ ⌞ x ⌟V)) ≡ ⌞ x ⌟V
    eq = begin
        conv (congTmΓ (cong[] refl refl refl (βπ₁ {σ = ⌞ ρ ⌟R} {⌞ x ⌟V}))) (π₂ (⌞ ρ ⌟R ‣ ⌞ x ⌟V))
      ≡⟨ conv-unique (congTmΓ (cong[] refl refl refl (βπ₁ {σ = ⌞ ρ ⌟R} {⌞ x ⌟V}))) refl (π₂ (⌞ ρ ⌟R ‣ ⌞ x ⌟V)) ⟩
        π₂ (⌞ ρ ⌟R ‣ ⌞ x ⌟V)
      ≡⟨ βπ₂ ⟩
        ⌞ x ⌟V
      ∎
IH._[_]tmP Domain {PΓ = Γ , refl} {A , refl} {Δ , refl} (x , refl) (ρ , refl) = lookupVar ρ x , sym (⌞lookup⌟ ρ x)

open elim DomainDecl Domain

reifyTm : (t : Tm Γ A) → Σ[ x ∈ Var Γ A ] t ≡ ⌞ x ⌟V
reifyTm {Γ} {A} t with ElimCtx Γ | ElimTy A | ElimTm t
... | .Γ , refl | .A , refl | x , eq = x , eq

-- Inductive definition of the normal form
data NeSub (Δ : Ctx) : (Γ : Ctx) → Sub Δ Γ → Set where
  idS : NeSub Δ Δ idS
  π₁  : NeSub Δ (Γ ‣ A) σ → NeSub Δ Γ (π₁ σ)

data NfTm (Δ : Ctx) : Tm Δ A → Set where
  π₂ : NeSub Δ (Γ ‣ A) σ → NfTm Δ {A [ π₁ σ ]} (π₂ σ)

test : vs {B = B'} (vs {B = B} (vz {Γ} {U})) ≡ π₂ (π₁ (π₁ idS)) -- π₂ (π₁ (π₁ idS))
test {Γ} {B} {B'} =
  begin
    π₂ idS [ π₁ idS ]tm [ π₁ idS ]tm
  ≡⟨ cong (_[ π₁ idS ]tm) (sym (π₂∘ idS (π₁ idS))) ⟩
    π₂ (idS ∘ π₁ idS) [ π₁ idS ]tm
  ≡⟨ cong (_[ π₁ idS ]tm) (cong π₂ (idS∘ (π₁ idS))) ⟩
    π₂ (π₁ idS) [ π₁ idS ]tm
  ≡⟨ sym (π₂∘ (π₁ idS) (π₁ idS)) ⟩
    π₂ (π₁ idS ∘ π₁ idS)
  ≡⟨ cong π₂ (sym (π₁∘ idS (π₁ idS))) ⟩
    π₂ (π₁ (idS ∘ π₁ idS))
  ≡⟨ cong (λ y → π₂ (π₁ y)) (idS∘ (π₁ idS)) ⟩
    π₂ (π₁ (π₁ idS))
  ∎

accVar : (x : Var Γ A)(σ : Sub Δ Γ) → Tm Δ (A [ σ ])
accVar (here {A = U}) σ = π₂ σ
accVar (there {A = U} {U} x) σ = accVar x (π₁ σ)

accVar[]tm : (x : Var Γ A)(σ : Sub Δ Γ)(τ : Sub Θ Δ) → accVar x σ [ τ ]tm ≡ tr (Tm Θ) ([∘] A σ τ) (accVar x (σ ∘ τ))
accVar[]tm (here {A = U}) σ τ = sym (π₂∘ σ τ)
accVar[]tm (there {A = U} {U} x) σ τ = begin
    accVar x (π₁ σ) [ τ ]tm
  ≡⟨ accVar[]tm x (π₁ σ) τ ⟩
    accVar x (π₁ σ ∘ τ)
  ≡⟨ cong (accVar x) (sym (π₁∘ σ τ)) ⟩
    accVar x (π₁ (σ ∘ τ))
  ∎

nfVar : (x : Var Γ A) → Tm Γ A
nfVar {A = U} x = accVar x idS

soundnessNfVar : (x : Var Γ A) → ⌞ x ⌟V ≡ nfVar x
soundnessNfVar (here {A = U}) = refl
soundnessNfVar (there {A = U} {U} x) = begin
    ⌞ x ⌟V [ π₁ idS ]tm
  ≡⟨ cong (_[ π₁ idS ]tm) (soundnessNfVar x) ⟩
    accVar x idS [ π₁ idS ]tm
  ≡⟨ accVar[]tm x idS (π₁ idS) ⟩
    accVar x (idS ∘ π₁ idS)
  ≡⟨ cong (accVar x) (idS∘ π₁ idS) ⟩
    accVar x (π₁ idS)
  ∎

NfTm[accVar] : (x : Var Γ A){σ : Sub Δ Γ} → NeSub Δ Γ σ → NfTm Δ (accVar x σ)
NfTm[accVar] (here {A = U}) nσ = π₂ nσ
NfTm[accVar] (there {A = U} {U} x) nσ = NfTm[accVar] x (π₁ nσ)

NfTm[nfVar] : (x : Var Γ A) → NfTm Γ (nfVar x)
NfTm[nfVar] {A = U} x = NfTm[accVar] x idS

thm[normalization] : (t : Tm Γ A) → Σ[ t' ∈ Tm Γ A ] t ≡ t' × NfTm Γ t'
thm[normalization] t with reifyTm t
... | x , eq = nfVar x , trans eq (soundnessNfVar x) , NfTm[nfVar] x