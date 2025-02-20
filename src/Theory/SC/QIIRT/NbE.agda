
module SC.QIIRT2.NbE where

open import Prelude
  renaming (_,_ to _/_)
  hiding (_∘_)
open import SC.QIIRT2.Base
open import SC.QIIRT2.Cong
open import SC.QIIRT2.Model
open import SC.QIIRT2.Elimination

-- Definition of Variables and Renaming
-- with embedding into Tm and Sub
data Var : (Γ : Ctx) → Ty Γ → Set where
  here  :           Var (Γ , A) (A [ π₁ idS ])
  there : Var Γ A → Var (Γ , B) (A [ π₁ idS ])

⌞_⌟V : Var Γ A → Tm Γ A
⌞ here    ⌟V  = π₂ idS
⌞ there x ⌟V  = ⌞ x ⌟V [ π₁ idS ]tm

data Ren : Ctx → Ctx → Set
⌞_⌟R : Ren Δ Γ → Sub Δ Γ

data Ren where
  ∅
    : Ren Δ ∅
  _,_
    : (ρ : Ren Δ Γ) → Var Δ (A [ ⌞ ρ ⌟R ])
    → Ren Δ (Γ , A)

⌞ ∅     ⌟R = ∅
⌞ σ , t ⌟R = ⌞ σ ⌟R , ⌞ t ⌟V

-- {-# REWRITE [∘] #-} can reduce the transitivity
-- Operations about renamings: lift, identity, and variable lookup
_↑R_
  : Ren Δ Γ → (A : Ty Δ)
  → Ren (Δ , A) Γ
⌞↑R⌟
  : (ρ : Ren Δ Γ)(A : Ty Δ)
  → ⌞ ρ ⌟R ∘ π₁ idS ≡ ⌞ ρ ↑R A ⌟R

∅ ↑R A                        = ∅
_↑R_ {Δ} (_,_ {A = A'} ρ x) A = (ρ ↑R A) , conv eq (there x)
  where
    eq : Var (Δ , A) (A' [ ⌞ ρ ⌟R ] [ π₁ idS ]) ≡ Var (Δ , A) (A' [ ⌞ ρ ↑R A ⌟R ])
    eq = cong (Var (Δ , A)) (congA[] {A = A'} (⌞↑R⌟ ρ A)) -- [∘] is no longer needed
⌞↑R⌟ ∅ A = η∅
⌞↑R⌟ {Δ} (_,_ {A = A'} ρ x) A = ≅-to-≡ $ begin
    (⌞ ρ ⌟R , ⌞ x ⌟V) ∘ π₁ idS
  ≡⟨ ,∘ ⟩
    ⌞ ρ ⌟R ∘ π₁ idS , ⌞ x ⌟V [ π₁ idS ]tm
  ≡⟨ cong,Sub' {A = A'} refl (⌞↑R⌟ ρ A) eq,r ⟩
    ⌞ ρ ↑R A ⌟R , ⌞ conv eq (there x) ⌟V
  ∎
  where
    open ≅-Reasoning
    eq = cong (Var (Δ , A)) (congA[] {A = A'} (⌞↑R⌟ ρ A)) -- [∘] is no longer needed
    eq,r : conv (congTmΓ (congA[] {A = A'} (⌞↑R⌟ ρ A))) (⌞ x ⌟V [ π₁ idS ]tm) ≡ ⌞ conv eq  (there x) ⌟V
    eq,r = ≅-to-≡ $ begin
        conv (congTmΓ (congA[] (⌞↑R⌟ ρ A))) (⌞ x ⌟V [ π₁ idS ]tm)
      ≅⟨ conv-rm (congTmΓ (congA[] (⌞↑R⌟ ρ A))) _ ⟩
        ⌞ x ⌟V [ π₁ idS ]tm
      ≅⟨ HEq.icong (Var (Δ , A)) (congA[] {A = A'} (⌞↑R⌟ ρ A)) ⌞_⌟V (HEq.sym (conv-rm eq _)) ⟩
        ⌞ conv eq (there x) ⌟V
      ∎

idR    : (Δ : Ctx) → Ren Δ Δ
⌞idR⌟  : (Δ : Ctx) → idS ≡ ⌞ idR Δ ⌟R
⌞idR↑⌟ : (A : Ty Γ) → π₁ idS ≡ ⌞ idR _ ↑R A ⌟R
idR ∅       = ∅
idR (Δ , A) = (idR _ ↑R A) , conv (cong (Var (Δ , A)) eq) here
  module idRTy where
    eq : A [ π₁ idS ] ≡ A [ ⌞ idR _ ↑R A ⌟R ]
    eq = congA[] {A = A} (⌞idR↑⌟ A)
⌞idR⌟ ∅       = η∅
⌞idR⌟ (Δ , A) = ≅-to-≡ $ begin
    idS
  ≡⟨ η, ⟩
    π₁ idS , π₂ idS
  ≡⟨ cong,Sub' {A = A} refl (⌞idR↑⌟ A) eq,r ⟩
    ⌞ idR _ ↑R A ⌟R , ⌞ conv (cong (Var (Δ , A)) (idRTy.eq Δ A)) here ⌟V
  ≡⟨⟩
    ⌞ idR _ ↑R A , conv (cong (Var (Δ , A)) (idRTy.eq Δ A)) here ⌟R
  ∎
  where
    open ≅-Reasoning
    eq,r : conv (congTmΓ (congA[] {A = A} (⌞idR↑⌟ A))) (π₂ {A = A} idS) ≡ ⌞ conv (cong (Var (Δ , A)) (idRTy.eq Δ A)) here ⌟V
    eq,r = ≅-to-≡ $ begin
        conv (congTmΓ (congA[] (⌞idR↑⌟ A))) (π₂ idS)
      ≅⟨ conv-rm (congTmΓ (congA[] (⌞idR↑⌟ A))) _ ⟩
        π₂ idS
      ≅⟨ refl ⟩
        ⌞ here ⌟V
      ≅⟨ HEq.icong (Var (Δ , A)) (idRTy.eq Δ A) ⌞_⌟V (HEq.sym (conv-rm (cong (Var (Δ , A)) (idRTy.eq Δ A)) here)) ⟩
        ⌞ conv (cong (Var (Δ , A)) (idRTy.eq Δ A)) here ⌟V
      ∎
⌞idR↑⌟ A = begin
    π₁ idS
  ≡⟨ sym (idS∘ π₁ idS) ⟩
    idS ∘ π₁ idS
  ≡⟨ cong∘' (⌞idR⌟ _) refl ⟩
    ⌞ idR _ ⌟R ∘ π₁ idS
  ≡⟨ ⌞↑R⌟ (idR _) A ⟩
    ⌞ idR _ ↑R A ⌟R
  ∎
  where open ≡-Reasoning

lookupVar : (ρ : Ren Δ Γ) → Var Γ A → Var Δ (A [ ⌞ ρ ⌟R ])
lookupVar {Δ} {Γ , _} (_,_ {A = A} ρ x) here = conv (cong (Var Δ) (eq {A = A} {x = x})) x -- conv (cong (Var Δ) (sym (eq {A = A} {x = x}))) x
  module lkVarEq where
    open  ≡-Reasoning
    eq : {A A' : Ty Γ}{x : Var Δ (A' [ ⌞ ρ ⌟R ])}
       → A [ ⌞ ρ ⌟R ] ≡ A [ π₁ {A = A'} idS ] [ ⌞ ρ ⌟R , ⌞ x ⌟V ]
    eq {A = A} {x = x} = congA[] {A = A} (sym (π₁idS∘ (⌞ ρ ⌟R , ⌞ x ⌟V)))

lookupVar {Δ} {Γ , _} (_,_ {A = A} ρ x') (there {A = A'} x) =
  conv (cong (Var Δ) (lkVarEq.eq Γ A ρ x' {A'} {_} {x'})) (lookupVar ρ x)

-- Several lemmas
⌞lookup⌟ : (ρ : Ren Δ Γ)(x : Var Γ A) → ⌞ x ⌟V [ ⌞ ρ ⌟R ]tm ≡ ⌞ lookupVar ρ x ⌟V
⌞lookup⌟ {Δ} {Γ , A} (ρ , x) here = ≅-to-≡ $ begin
    π₂ idS [ ⌞ ρ ⌟R , ⌞ x ⌟V ]tm
  ≡⟨ sym (π₂∘ (⌞ ρ ⌟R , ⌞ x ⌟V) idS) ⟩
    π₂ (idS ∘ (⌞ ρ ⌟R , ⌞ x ⌟V))
  ≅⟨ HEq.cong π₂ (≡-to-≅ (idS∘ (⌞ ρ ⌟R , ⌞ x ⌟V))) ⟩
    π₂ (⌞ ρ ⌟R , ⌞ x ⌟V)
  ≅⟨ ≡-to-≅ π₂, ⟩
    ⌞ x ⌟V
  ≅⟨ HEq.icong (Var Δ) (lkVarEq.eq Γ A ρ x {A} {_} {x}) ⌞_⌟V (HEq.sym (conv-rm (cong (Var Δ) (lkVarEq.eq Γ A ρ x {A} {_} {x})) _)) ⟩
    ⌞ conv (cong (Var Δ) (lkVarEq.eq Γ A ρ x {A} {_} {x})) x ⌟V
  ∎
  where open ≅-Reasoning
⌞lookup⌟ {Δ} {Γ , A'} (ρ , x') (there {A = A} x) = ≅-to-≡ $ begin
    ⌞ x ⌟V [ wk ]tm [ ⌞ ρ ⌟R , ⌞ x' ⌟V ]tm  -- reduced by recursion _[_]t
  ≡⟨ [∘]tm ⟨
    ⌞ x ⌟V [ wk ∘ (⌞ ρ ⌟R , ⌞ x' ⌟V) ]tm  
  ≅⟨  hcong {B = λ σ → Tm Δ (A [ σ ])} (λ σ → ⌞ x ⌟V [ σ ]tm) eq  ⟩
    ⌞ x ⌟V [ ⌞ ρ ⌟R ]tm
  ≅⟨ ≡-to-≅ (⌞lookup⌟ ρ x) ⟩
    ⌞ lookupVar ρ x ⌟V
  ≅⟨ HEq.icong (Var Δ) (lkVarEq.eq Γ A' ρ x' {A} {A'} {x'}) ⌞_⌟V (HEq.sym (conv-rm (cong (Var Δ) (lkVarEq.eq Γ A' ρ x' {A} {_} {x'})) _)) ⟩
    ⌞ conv (cong (Var Δ) (lkVarEq.eq Γ A' ρ x' {A} {_} {x'})) (lookupVar ρ x) ⌟V
  ∎
  where
    open ≅-Reasoning
    eq : π₁ {A = A'} idS ∘ (⌞ ρ ⌟R , ⌞ x' ⌟V) ≅ ⌞ ρ ⌟R
    eq = begin
        π₁ idS ∘ (⌞ ρ ⌟R , ⌞ x' ⌟V)
      ≡⟨ π₁idS∘ (⌞ ρ ⌟R , ⌞ x' ⌟V) ⟩
        π₁ (⌞ ρ ⌟R , ⌞ x' ⌟V)
      ≡⟨ π₁, ⟩
        ⌞ ρ ⌟R
      ∎

-- Composition of renamings
_⊙_ : Ren Δ Γ → Ren Θ Δ → Ren Θ Γ
⌞⊙⌟ : (ρ : Ren Δ Γ)(ρ' : Ren Θ Δ) → ⌞ ρ ⌟R ∘ ⌞ ρ' ⌟R ≡ ⌞ ρ ⊙ ρ' ⌟R
∅ ⊙ _ = ∅
_⊙_ {Θ = Θ} (_,_ {A = A} ρ x) ρ' = (ρ ⊙ ρ') , conv (cong (Var Θ) eqA[]) (lookupVar ρ' x)
  module ⊙Eq where
    open ≡-Reasoning
    eqA[] : A [ ⌞ ρ ⌟R ] [ ⌞ ρ' ⌟R ] ≡ A [ ⌞ ρ ⊙ ρ' ⌟R ]
    eqA[] = congA[] {A = A} (⌞⊙⌟ ρ ρ')
⌞⊙⌟ ∅ ρ' = η∅
⌞⊙⌟ {Δ} {Γ , A} {Θ} (ρ , x) ρ' = ≅-to-≡ $ begin
    (⌞ ρ ⌟R , ⌞ x ⌟V) ∘ ⌞ ρ' ⌟R
  ≡⟨ ,∘ ⟩
    (⌞ ρ ⌟R ∘ ⌞ ρ' ⌟R) , ⌞ x ⌟V [ ⌞ ρ' ⌟R ]tm
  ≡⟨ cong,Sub' {A = A} refl (⌞⊙⌟ ρ ρ') eq,r ⟩
    ⌞ ρ ⊙ ρ' ⌟R , ⌞ conv (cong (Var Θ) (⊙Eq.eqA[] {A = A} ρ x ρ')) (lookupVar ρ' x) ⌟V
  ∎
  where
    open ≅-Reasoning
    eq,r : conv (congTmΓ (congA[] {A = A} (⌞⊙⌟ ρ ρ'))) (⌞ x ⌟V [ ⌞ ρ' ⌟R ]tm)
         ≡ ⌞ conv (cong (Var Θ) (⊙Eq.eqA[] {A = A} ρ x ρ')) (lookupVar ρ' x) ⌟V
    eq,r = ≅-to-≡ $ begin
        conv (congTmΓ (congA[] {A = A} (⌞⊙⌟ ρ ρ'))) (⌞ x ⌟V [ ⌞ ρ' ⌟R ]tm)
      ≅⟨ conv-rm _ _ ⟩
        ⌞ x ⌟V [ ⌞ ρ' ⌟R ]tm
      ≅⟨ ≡-to-≅ (⌞lookup⌟ ρ' x) ⟩
        ⌞ lookupVar ρ' x ⌟V
      ≅⟨ HEq.icong (Var Θ) (⊙Eq.eqA[] {A = A} ρ x ρ') ⌞_⌟V (HEq.sym (conv-rm (cong (Var Θ) (⊙Eq.eqA[] {A = A} ρ x ρ')) _)) ⟩
        ⌞ conv (cong (Var Θ) (⊙Eq.eqA[] ρ x ρ')) (lookupVar ρ' x) ⌟V
      ∎

-- Reification of terms and substitutions into variables and renamings
-- infixr 4 _/_

DomainDecl : Pdc
DomainDecl .Pdc.PCtx Γ = Σ[ Γ' ∈ Ctx ] Γ ≡ Γ'
DomainDecl .Pdc.PTy (Γ / refl) A = Σ[ A' ∈ Ty Γ ] A ≡ A'
DomainDecl .Pdc.PSub (Γ / refl) (Δ / refl) σ = Σ[ ρ ∈ Ren Γ Δ ] σ ≡ ⌞ ρ ⌟R
DomainDecl .Pdc.PTm (Γ / refl) (A / eq) t = Σ[ x ∈ Var Γ A ] conv (congTmΓ eq) t ≡ ⌞ x ⌟V

Domain : IH DomainDecl
IH._[_]P Domain {PΓ = Γ / refl} {PΔ = Δ / refl} (A / eqA) (ρ / eqρ) = A [ ⌞ ρ ⌟R ] / cong[] refl eqA refl eqρ
Domain .IH.∅Ctx = ∅ / refl
Domain .IH._,Ctx_ (Γ / refl) (A / refl) = (Γ , A) / refl
Domain .IH.∅Sub {PΔ = Δ / refl} = ∅ / refl
IH._,Sub_ Domain {PΔ = Δ / refl} {Γ / refl} {A / refl} (ρ / refl) (x / eqx) = (ρ , x) / cong (⌞ ρ ⌟R ,_) eqx
Domain .IH.PidS {PΔ = Γ / refl} = (idR _) / (⌞idR⌟ _)
Domain .IH._∘P_ {PΓ = Γ / refl} {Δ / refl} {Θ / refl} (ρ / refl) (ρ' / refl) = ρ ⊙ ρ' / ⌞⊙⌟ ρ ρ'
Domain .IH.π₁P {PΔ = Δ / refl} {Γ / refl} {A / refl} ((ρ , x) / refl) = ρ / π₁,
Domain .IH.PU {PΓ = Γ / refl} = U / refl
Domain .IH.PU[] {PΓ = Γ / refl} {Δ / refl} {ρ / refl} = refl
Domain .IH.π₂P {PΔ = Δ / refl} {Γ / refl} {A / refl} ((ρ , x) / refl) = x / eq
  where
    open ≅-Reasoning
    eq : conv (congTmΓ (congA[] {A = A} (π₁, {σ = ⌞ ρ ⌟R}))) (π₂ {A = A} (⌞ ρ ⌟R , ⌞ x ⌟V)) ≡ ⌞ x ⌟V
    eq = ≅-to-≡ $ begin
        conv (congTmΓ (congA[] π₁,)) (π₂ {A = A} (⌞ ρ ⌟R , ⌞ x ⌟V))
      ≅⟨ conv-rm _ _ ⟩
        π₂ (⌞ ρ ⌟R , ⌞ x ⌟V)
      ≡⟨ π₂, ⟩
        ⌞ x ⌟V
      ∎
IH._[_]tmP Domain {PΓ = Γ / refl} {A / refl} {Δ / refl} (x / refl) (ρ / refl) = lookupVar ρ x / ⌞lookup⌟ ρ x

open elim DomainDecl Domain

reifyTm : (t : Tm Γ A) → Σ[ x ∈ Var Γ A ] t ≡ ⌞ x ⌟V
reifyTm {Γ} {A} t with ElimCtx Γ | ElimTy A | ElimTm t
... | .Γ / refl | .A / refl | x / eq = x / eq

-- Inductive definition of the normal form
data NeSub (Δ : Ctx) : (Γ : Ctx) → Sub Δ Γ → Set where
  idS : NeSub Δ Δ idS
  π₁  : NeSub Δ (Γ , A) σ → NeSub Δ Γ (π₁ σ)

data NfTm (Δ : Ctx) : Tm Δ A → Set where
  π₂ : NeSub Δ (Γ , A) σ → NfTm Δ {A [ π₁ σ ]} (π₂ σ)

accVar : (x : Var Γ A)(σ : Sub Δ Γ) → Tm Δ (A [ σ ])
accVar (here {A = A}) σ = conv (congTmΓ (eqTy {A = A})) (π₂ σ)
  module accVarEq where
    open ≡-Reasoning
    eqTy : ∀{A} → A [ π₁ σ ] ≡ A [ π₁ idS ] [ σ ]
    eqTy {A = A} = congA[] {A = A} (sym (π₁idS∘ σ))
accVar (there {A = A} x) σ = conv (congTmΓ (accVarEq.eqTy σ {A})) (accVar x (π₁ σ))

accVar[]t : (x : Var Γ A)(σ : Sub Δ Γ)(τ : Sub Θ Δ) → accVar x (σ ∘ τ) ≡ accVar x σ [ τ ]tm
accVar[]t {Γ , A} {_} {Δ} {Θ} here σ τ = ≅-to-≡ $ begin
    conv (congTmΓ (accVarEq.eqTy (σ ∘ τ))) (π₂ (σ ∘ τ))
  ≅⟨ conv-rm (congTmΓ (accVarEq.eqTy (σ ∘ τ))) _ ⟩
    π₂ (σ ∘ τ)
  ≅⟨ ≡-to-≅ (π₂∘ τ σ) ⟩
    π₂ σ [ τ ]tm
  ≅⟨ HEq.icong (Tm Δ) (accVarEq.eqTy σ {A}) (_[ τ ]tm) (HEq.sym (conv-rm (congTmΓ (accVarEq.eqTy σ)) _)) ⟩
    conv (congTmΓ (accVarEq.eqTy σ)) (π₂ σ) [ τ ]tm
  ∎
  where open ≅-Reasoning
accVar[]t {Γ , A'} {_} {Δ} {Θ} (there {A = A} x) σ τ = ≅-to-≡ $ begin
    conv (congTmΓ (accVarEq.eqTy (σ ∘ τ))) (accVar x (π₁ (σ ∘ τ)))
  ≅⟨ conv-rm (congTmΓ (accVarEq.eqTy (σ ∘ τ))) _ ⟩
    accVar x (π₁ (σ ∘ τ))
  ≅⟨ HEq.cong (accVar x) (≡-to-≅ (π₁∘ τ σ)) ⟩
    accVar x (π₁ σ ∘ τ)
  ≅⟨ ≡-to-≅ (accVar[]t x (π₁ σ) τ) ⟩
    accVar x (π₁ σ) [ τ ]tm
  ≅⟨ HEq.icong (Tm Δ) (accVarEq.eqTy σ {A}) (_[ τ ]tm) (HEq.sym (conv-rm (congTmΓ (accVarEq.eqTy σ)) _)) ⟩
    conv (congTmΓ (accVarEq.eqTy σ)) (accVar x (π₁ σ)) [ τ ]tm
  ∎
  where open ≅-Reasoning

nfVar : (x : Var Γ A) → Tm Γ A
nfVar x = accVar x idS

soundnessNfVar : (x : Var Γ A) → nfVar x ≡ ⌞ x ⌟V
soundnessNfVar {Γ , A'} {A} here = ≅-to-≡ $ begin
    conv (congTmΓ (accVarEq.eqTy idS {A'})) (π₂ idS)
  ≅⟨ conv-rm (congTmΓ (accVarEq.eqTy idS {A'})) _ ⟩
    π₂ idS
  ∎
  where open ≅-Reasoning
soundnessNfVar {Γ , B} (there {A = A} x) = ≅-to-≡ $ begin
    conv (congTmΓ (accVarEq.eqTy idS {A})) (accVar x (π₁ idS))
  ≅⟨ conv-rm (congTmΓ (accVarEq.eqTy idS)) (accVar x (π₁ idS)) ⟩
    accVar x (π₁ idS)
  ≅⟨ HEq.cong (accVar x) (≡-to-≅ (sym (idS∘ π₁ idS))) ⟩
    accVar x (idS ∘ π₁ idS)
  ≡⟨ accVar[]t x idS (π₁ idS) ⟩
    accVar x idS [ π₁ idS ]tm
  ≡⟨ cong (_[ π₁ {A = B} idS ]tm) (soundnessNfVar x) ⟩
    ⌞ x ⌟V [ π₁ idS ]tm
  ∎
  where open ≅-Reasoning

NfTm[accVar] : (x : Var Γ A){σ : Sub Δ Γ} → NeSub Δ Γ σ → NfTm Δ (accVar x σ)
NfTm[accVar] {Γ , A} {_} {Δ} here {σ} nσ = conv (sym eqTy) (π₂ nσ)
  where
    open ≅-Reasoning
    eqTy : NfTm Δ (conv (congTmΓ (accVarEq.eqTy σ {A})) (π₂ σ)) ≡ NfTm Δ (π₂ σ)
    eqTy = ≅-to-≡ $ begin
        NfTm Δ (conv (congTmΓ (accVarEq.eqTy σ)) (π₂ σ))
      ≅⟨ HEq.icong (Tm Δ) (sym (accVarEq.eqTy σ {A})) (NfTm Δ) (conv-rm _ _) ⟩
        NfTm Δ (π₂ σ)
      ∎
NfTm[accVar] {Γ , A'} {_} {Δ} (there {A = A} x) {σ} nσ = conv (sym eqTy) (NfTm[accVar] x (π₁ nσ))
  where
    open ≅-Reasoning
    eqTy : NfTm Δ (conv (congTmΓ (accVarEq.eqTy σ {A})) (accVar x (π₁ σ))) ≡ NfTm Δ (accVar x (π₁ σ))
    eqTy = ≅-to-≡ $ begin
        NfTm Δ (conv (congTmΓ (accVarEq.eqTy σ)) (accVar x (π₁ σ)))
      ≅⟨ HEq.icong (Tm Δ) (sym (accVarEq.eqTy σ {A})) (NfTm Δ) (conv-rm _ _) ⟩
        NfTm Δ (accVar x (π₁ σ))
      ∎

NfTm[nfVar] : (x : Var Γ A) → NfTm Γ (nfVar x)
NfTm[nfVar] {Γ} {A} x = NfTm[accVar] x idS

thm[normalization] : (t : Tm Γ A) → Σ[ t' ∈ Tm Γ A ] t' ≡ t × NfTm Γ t'
thm[normalization] t with reifyTm t
... | x / eq = nfVar x / trans (soundnessNfVar x) (sym eq) / NfTm[nfVar] x 
