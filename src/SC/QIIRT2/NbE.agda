module SC.QIIRT2.NbE where

open import Prelude
  renaming (_,_ to _/_)
open import SC.QIIRT2.Base
open import SC.QIIRT2.Cong
open import SC.QIIRT2.Model
open import SC.QIIRT2.Elimination

-- Definition of Variables and Renaming
-- with embedding into Tm and Sub
data Var : (Γ : Ctx) → Ty Γ → Set where
  here  : Var (Γ , A) (A [ π₁ idS ])
  there : Var Γ A → Var (Γ , B) (A [ π₁ idS ])

⌞_⌟V : Var Γ A → Tm Γ A
⌞ here ⌟V = π₂ idS
⌞ there x ⌟V  = ⌞ x ⌟V [ π₁ idS ]t

data Ren : Ctx → Ctx → Set
⌞_⌟R : Ren Δ Γ → Sub Δ Γ

data Ren where
  ∅ : Ren Δ ∅
  _,_ : (ρ : Ren Δ Γ) → Var Δ (A [ ⌞ ρ ⌟R ]) → Ren Δ (Γ , A)

⌞ ∅ ⌟R = ∅
⌞ σ , t ⌟R = ⌞ σ ⌟R , ⌞ t ⌟V

-- {-# REWRITE [∘] #-} can reduce the transitivity
-- Operations about renamings: lift, identity, and variable lookup
_↑R_ : Ren Δ Γ → (A : Ty Δ) → Ren (Δ , A) Γ
⌞↑R⌟ : (ρ : Ren Δ Γ)(A : Ty Δ) → ⌞ ρ ↑R A ⌟R ≡ ⌞ ρ ⌟R ∘ π₁ idS
∅ ↑R A = ∅
_↑R_ {Δ} (_,_ {A = A'} ρ x) A = (ρ ↑R A) , conv (sym eq) (there x) 
  module ↑RTy where
    eq : Var (Δ , A) (A' [ ⌞ ρ ↑R A ⌟R ]) ≡ Var (Δ , A) (A' [ ⌞ ρ ⌟R ] [ π₁ idS ])
    eq = cong (Var (Δ , A)) (congA[] {A = A'} (⌞↑R⌟ ρ A)) -- [∘] is no longer needed
⌞↑R⌟ ∅ A = sym η∅
⌞↑R⌟ {Δ} (_,_ {A = A'} ρ x) A = ≅-to-≡ $ begin
    ⌞ ρ ↑R A ⌟R , ⌞ conv (sym (↑RTy.eq {A = A'} ρ x A)) (there x) ⌟V
  ≡⟨ cong,Sub' {A = A'} refl (⌞↑R⌟ ρ A) eq,r ⟩
    ⌞ ρ ⌟R ∘ π₁ idS , ⌞ there x ⌟V -- [∘] is no longer needed
  ≡⟨ sym ,∘ ⟩
    (⌞ ρ ⌟R , ⌞ x ⌟V) ∘ π₁ idS
  ∎
  where
    open ≅-Reasoning
    eq,r : conv (congTmΓ (congA[] {A = A'} (⌞↑R⌟ ρ A))) ⌞ conv (sym (↑RTy.eq {A = A'} ρ x A)) (there x) ⌟V
           ≡ ⌞ there x ⌟V
    eq,r = ≅-to-≡ $ begin
        conv (congTmΓ (congA[] {A = A'} (⌞↑R⌟ ρ A))) ⌞ conv (sym (↑RTy.eq {A = A'} ρ x A)) (there x) ⌟V
      ≅⟨ conv-rm _ _ ⟩
        ⌞ conv (sym (↑RTy.eq ρ x A)) (there x) ⌟V
      ≅⟨ HEq.icong (Var (Δ , A)) (congA[] {A = A'} (⌞↑R⌟ ρ A)) ⌞_⌟V (conv-rm (sym (↑RTy.eq ρ x A)) _) ⟩
        ⌞ x ⌟V [ π₁ idS ]t
      ≡⟨⟩
        ⌞ there x ⌟V  -- [∘] is no longer needed
      ∎


idR : Ren Δ Δ
⌞idR⌟ : ⌞ idR {Δ} ⌟R ≡ idS
⌞idR↑⌟ : (A : Ty Γ) → ⌞ idR ↑R A ⌟R ≡ π₁ idS
idR {∅} = ∅
idR {Δ , A} = (idR ↑R A) , conv (cong (Var (Δ , A)) (sym eq)) here
  module idRTy where
    eq : A [ ⌞ idR ↑R A ⌟R ] ≡ A [ π₁ idS ]
    eq = congA[] {A = A} (⌞idR↑⌟ A)
⌞idR⌟ {∅} = sym η∅
⌞idR⌟ {Δ , A} = ≅-to-≡ $ begin
    ⌞ idR ↑R A , conv (cong (Var (Δ , A)) (sym (idRTy.eq Δ A))) here ⌟R
  ≡⟨⟩
    ⌞ idR ↑R A ⌟R , ⌞ conv (cong (Var (Δ , A)) (sym (idRTy.eq Δ A))) here ⌟V
  ≡⟨ cong,Sub' {A = A} refl (⌞idR↑⌟ A) eq,r ⟩
    π₁ idS , π₂ idS
  ≡⟨ sym η, ⟩
    idS
  ∎
  where
    open ≅-Reasoning
    eq,r : conv (congTmΓ (congA[] (⌞idR↑⌟ A))) (⌞ conv (cong (Var (Δ , A)) (sym (idRTy.eq Δ A))) here ⌟V) 
         ≡ π₂ {A = A} idS
    eq,r = ≅-to-≡ $ begin
        conv (congTmΓ (congA[] (⌞idR↑⌟ A))) (⌞ conv (cong (Var (Δ , A)) (sym (idRTy.eq Δ A))) here ⌟V)
      ≅⟨ conv-rm _ _ ⟩
        ⌞ conv (cong (Var (Δ , A)) (sym (idRTy.eq Δ A))) here ⌟V
      ≅⟨ HEq.icong (Var (Δ , A)) (idRTy.eq Δ A) ⌞_⌟V (conv-rm (cong (Var (Δ , A)) (sym (idRTy.eq Δ A))) _) ⟩
        π₂ idS
      ∎
⌞idR↑⌟ A = begin
    ⌞ idR ↑R A ⌟R
  ≡⟨ ⌞↑R⌟ idR A ⟩
    ⌞ idR ⌟R ∘ π₁ idS
  ≡⟨ cong∘' ⌞idR⌟ refl ⟩
    idS ∘ π₁ idS
  ≡⟨ idS∘ π₁ idS ⟩
    π₁ idS
  ∎
  where open ≡-Reasoning

lookupVar : (ρ : Ren Δ Γ) → Var Γ A → Var Δ (A [ ⌞ ρ ⌟R ])
lookupVar {Δ} {Γ , _} (_,_ {A = A} ρ x) here = conv (cong (Var Δ) (sym (eq {A = A} {x = x}))) x
  module lkVarEq where
    open  ≡-Reasoning
    eq : {A A' : Ty Γ}{x : Var Δ (A' [ ⌞ ρ ⌟R ])} → A [ π₁ {A = A'} idS ] [ ⌞ ρ ⌟R , ⌞ x ⌟V ] ≡ A [ ⌞ ρ ⌟R ]
    eq {A = A} {x = x} = begin
        A [ π₁ idS ] [ ⌞ ρ ⌟R , ⌞ x ⌟V ]
      ≡⟨ congA[] {A = A} (π₁idS∘ (⌞ ρ ⌟R , ⌞ x ⌟V)) ⟩ -- [∘] and A[βπ₁] are no longer needed
        A [ ⌞ ρ ⌟R ]
      ∎
lookupVar {Δ} {Γ , _} (_,_ {A = A} ρ x') (there {A = A'} x) = conv (cong (Var Δ) (sym (lkVarEq.eq Γ A ρ x' {A'} {_} {x'}))) (lookupVar ρ x)

-- Several lemmas
⌞lookup⌟ : (ρ : Ren Δ Γ)(x : Var Γ A) → ⌞ lookupVar ρ x ⌟V ≡ ⌞ x ⌟V [ ⌞ ρ ⌟R ]t
⌞lookup⌟ {Δ} {Γ , A} (ρ , x) here = ≅-to-≡ $ begin
    ⌞ conv (cong (Var Δ) (sym (lkVarEq.eq Γ A ρ x {A} {_} {x}))) x ⌟V
  ≅⟨ HEq.icong (Var Δ) (lkVarEq.eq Γ A ρ x {A} {_} {x}) ⌞_⌟V (conv-rm (cong (Var Δ) (sym (lkVarEq.eq Γ A ρ x {A} {_} {x}))) _) ⟩
    ⌞ x ⌟V
  ≅⟨ ≡-to-≅ (sym (π₂, {A = A} {σ = ⌞ ρ ⌟R} {t = ⌞ x ⌟V})) ⟩ -- no conv in π₂, here
    π₂ (⌞ ρ ⌟R , ⌞ x ⌟V)
  ≅⟨ HEq.cong π₂ (≡-to-≅ (sym (idS∘ (⌞ ρ ⌟R , ⌞ x ⌟V)))) ⟩
    π₂ (idS ∘ (⌞ ρ ⌟R , ⌞ x ⌟V))
  ≡⟨ π₂∘ (⌞ ρ ⌟R , ⌞ x ⌟V) idS ⟩
    π₂ idS [ ⌞ ρ ⌟R , ⌞ x ⌟V ]tm
  ∎ 
  where open ≅-Reasoning
⌞lookup⌟ {Δ} {Γ , A'} (ρ , x') (there {A = A} x) = ≅-to-≡ $ begin
    ⌞ conv (cong (Var Δ) (sym (lkVarEq.eq Γ A' ρ x' {A} {_} {x'}))) (lookupVar ρ x) ⌟V
  ≅⟨ HEq.icong (Var Δ) (lkVarEq.eq Γ A' ρ x' {A} {_} {x'}) ⌞_⌟V (conv-rm (cong (Var Δ) (sym (lkVarEq.eq Γ A' ρ x' {A} {_} {x'}))) _) ⟩
    ⌞ lookupVar ρ x ⌟V
  ≅⟨ ≡-to-≅ (⌞lookup⌟ ρ x) ⟩
    ⌞ x ⌟V [ ⌞ ρ ⌟R ]t
  ≅⟨ HEq.cong {A = Sub Δ Γ} {B = λ σ → Tm Δ (A [ σ ])} (⌞ x ⌟V [_]t) eq ⟩
    ⌞ x ⌟V [ π₁ idS ]t [ ⌞ ρ ⌟R , ⌞ x' ⌟V ]t  -- reduced by recursion _[_]t
  ∎
  where
    open ≅-Reasoning
    eq : ⌞ ρ ⌟R ≅ π₁ {A = A'} idS ∘ (⌞ ρ ⌟R , ⌞ x' ⌟V)
    eq = begin
        ⌞ ρ ⌟R
      ≡⟨ sym (π₁, {σ = ⌞ ρ ⌟R} {t = ⌞ x' ⌟V}) ⟩
        π₁ (⌞ ρ ⌟R , ⌞ x' ⌟V)
      ≡⟨ sym (π₁idS∘ (⌞ ρ ⌟R , ⌞ x' ⌟V)) ⟩
        π₁ idS ∘ (⌞ ρ ⌟R , ⌞ x' ⌟V)
      ∎

-- Composition of renamings
_⊙_ : Ren Δ Γ → Ren Θ Δ → Ren Θ Γ
⌞⊙⌟ : (ρ : Ren Δ Γ)(ρ' : Ren Θ Δ) → ⌞ ρ ⊙ ρ' ⌟R ≡ ⌞ ρ ⌟R ∘ ⌞ ρ' ⌟R
∅ ⊙ _ = ∅
_⊙_ {Θ = Θ} (_,_ {A = A} ρ x) ρ' = (ρ ⊙ ρ') , conv (cong (Var Θ) (sym eqA[])) (lookupVar ρ' x)
  module ⊙Eq where
    open ≡-Reasoning
    eqA[] : A [ ⌞ ρ ⊙ ρ' ⌟R ] ≡ A [ ⌞ ρ ⌟R ] [ ⌞ ρ' ⌟R ]
    eqA[] = congA[] {A = A} (⌞⊙⌟ ρ ρ')
⌞⊙⌟ ∅ ρ' = sym η∅
⌞⊙⌟ {Δ} {Γ , A} {Θ} (ρ , x) ρ' = ≅-to-≡ $ begin
    ⌞ ρ ⊙ ρ' ⌟R , ⌞ conv (cong (Var Θ) (sym (⊙Eq.eqA[] {A = A} ρ x ρ'))) (lookupVar ρ' x) ⌟V
  ≡⟨ cong,Sub' {A = A} refl (⌞⊙⌟ ρ ρ') eq,r ⟩
    (⌞ ρ ⌟R ∘ ⌞ ρ' ⌟R) , ⌞ x ⌟V [ ⌞ ρ' ⌟R ]t
  ≡⟨ sym ,∘ ⟩
    (⌞ ρ ⌟R , ⌞ x ⌟V) ∘ ⌞ ρ' ⌟R
  ∎
  where
    open ≅-Reasoning
    eq,r : conv (congTmΓ (congA[] {A = A} (⌞⊙⌟ ρ ρ'))) ⌞ conv (cong (Var Θ) (sym (⊙Eq.eqA[] {A = A} ρ x ρ'))) (lookupVar ρ' x) ⌟V
         ≡ ⌞ x ⌟V [ ⌞ ρ' ⌟R ]t
    eq,r = ≅-to-≡ $ begin
        conv (congTmΓ (congA[] {A = A} (⌞⊙⌟ ρ ρ'))) ⌞ conv (cong (Var Θ) (sym (⊙Eq.eqA[] {A = A} ρ x ρ'))) (lookupVar ρ' x) ⌟V
      ≅⟨ conv-rm _ _ ⟩
        ⌞ conv (cong (Var Θ) (sym (⊙Eq.eqA[] {A = A} ρ x ρ'))) (lookupVar ρ' x) ⌟V
      ≅⟨ HEq.icong (Var Θ) (⊙Eq.eqA[] {A = A} ρ x ρ') ⌞_⌟V (conv-rm (cong (Var Θ) (sym (⊙Eq.eqA[] {A = A} ρ x ρ'))) _) ⟩
        ⌞ lookupVar ρ' x ⌟V
      ≡⟨ ⌞lookup⌟ ρ' x ⟩
        ⌞ x ⌟V [ ⌞ ρ' ⌟R ]t -- no need to conv
      ∎

-- Reification of terms and substitutions into variables and renamings
infixr 4 _/_

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
Domain .IH.PidS {PΔ = Γ / refl} = idR / sym ⌞idR⌟
Domain .IH._∘P_ {PΓ = Γ / refl} {Δ / refl} {Θ / refl} (ρ / refl) (ρ' / refl) = ρ ⊙ ρ' / sym (⌞⊙⌟ ρ ρ')
Domain .IH.π₁P {PΔ = Δ / refl} {Γ / refl} {A / refl} ((ρ , x) / refl) = ρ / π₁,
Domain .IH.PU {PΓ = Γ / refl} = U / refl
Domain .IH.PU[] {PΓ = Γ / refl} {Δ / refl} {ρ / refl} = refl
Domain .IH.π₂P {PΔ = Δ / refl} {Γ / refl} {A / refl} ((ρ , x) / refl) = x / eq -- π₂,
  where
    open ≅-Reasoning
    eq : conv (congTmΓ (congA[] {A = A} (π₁, {A = A} {σ = ⌞ ρ ⌟R} {⌞ x ⌟V}))) (π₂ {A = A} (⌞ ρ ⌟R , ⌞ x ⌟V)) ≡ ⌞ x ⌟V
    eq = ≅-to-≡ $ begin
        conv (congTmΓ (congA[] π₁,)) (π₂ {A = A} (⌞ ρ ⌟R , ⌞ x ⌟V))
      ≅⟨ conv-rm _ _ ⟩
        π₂ (⌞ ρ ⌟R , ⌞ x ⌟V)
      ≡⟨ π₂, ⟩
        ⌞ x ⌟V
      ∎
IH._[_]tmP Domain {PΓ = Γ / refl} {A / refl} {Δ / refl} (x / refl) (ρ / refl) = lookupVar ρ x / eq
  where
    open ≡-Reasoning
    eq : ⌞ x ⌟V [ ⌞ ρ ⌟R ]tm ≡ ⌞ lookupVar ρ x ⌟V
    eq = begin
        ⌞ x ⌟V [ ⌞ ρ ⌟R ]tm
      ≡⟨ []tm≡[]t ⌞ x ⌟V ⌞ ρ ⌟R ⟩
        ⌞ x ⌟V [ ⌞ ρ ⌟R ]t
      ≡⟨ sym (⌞lookup⌟ ρ x) ⟩
        ⌞ lookupVar ρ x ⌟V
      ∎

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
accVar (here {A = A}) σ = conv (congTmΓ (sym (eqTy {A = A}))) (π₂ σ)
  module accVarEq where
    open ≡-Reasoning
    eqTy : ∀{A} → A [ π₁ idS ] [ σ ] ≡ A [ π₁ σ ]
    eqTy {A = A} = congA[] {A = A} (π₁idS∘ σ)
accVar (there {A = A} x) σ = conv (congTmΓ (sym (accVarEq.eqTy σ {A}))) (accVar x (π₁ σ))

accVar[]t : (x : Var Γ A)(σ : Sub Δ Γ)(τ : Sub Θ Δ) → accVar x σ [ τ ]t ≡ accVar x (σ ∘ τ)
accVar[]t {Γ , A} {_} {Δ} {Θ} here σ τ = ≅-to-≡ $ begin
    conv (congTmΓ (sym (accVarEq.eqTy σ {A}))) (π₂ σ) [ τ ]t
  ≅⟨ HEq.icong (Tm Δ) (accVarEq.eqTy σ {A}) (_[ τ ]t) (conv-rm _ _) ⟩
    π₂ σ [ τ ]t
  ≅⟨ HEq.sym (≡-to-≅ ([]tm≡[]t (π₂ σ) τ)) ⟩
    π₂ σ [ τ ]tm
  ≅⟨ HEq.sym (≡-to-≅ (π₂∘ τ σ)) ⟩
    π₂ (σ ∘ τ)
  ≅⟨ HEq.sym (conv-rm _ _) ⟩
    conv (congTmΓ (sym (accVarEq.eqTy (σ ∘ τ)))) (π₂ (σ ∘ τ))
  ∎
  where open ≅-Reasoning
accVar[]t {Γ , A'} {_} {Δ} {Θ} (there {A = A} x) σ τ = ≅-to-≡ $ begin
    conv (congTmΓ (sym (accVarEq.eqTy σ {A}))) (accVar x (π₁ σ)) [ τ ]t
  ≅⟨ HEq.icong (Tm Δ) (accVarEq.eqTy σ {A}) (_[ τ ]t) (conv-rm (congTmΓ (sym (accVarEq.eqTy σ))) _) ⟩
    accVar x (π₁ σ) [ τ ]t
  ≅⟨ ≡-to-≅ (accVar[]t x (π₁ σ) τ) ⟩
    accVar x (π₁ σ ∘ τ)
  ≅⟨ HEq.cong (accVar x) (≡-to-≅ (sym (π₁∘ τ σ))) ⟩
    accVar x (π₁ (σ ∘ τ))
  ≅⟨ HEq.sym (conv-rm _ _) ⟩
    conv (congTmΓ (sym (accVarEq.eqTy (σ ∘ τ) {A}))) (accVar x (π₁ (σ ∘ τ)))
  ∎
  where open ≅-Reasoning

nfVar : (x : Var Γ A) → Tm Γ A
nfVar x = accVar x idS

soundnessNfVar : (x : Var Γ A) → ⌞ x ⌟V ≡ nfVar x
soundnessNfVar {Γ , A'} {A} here = sym (≅-to-≡ $ begin
    conv (congTmΓ (sym (accVarEq.eqTy idS {A'}))) (π₂ idS)
  ≅⟨ conv-rm _ _ ⟩
    π₂ idS
  ∎)
  where open ≅-Reasoning
soundnessNfVar {Γ , B} (there {A = A} x) = ≅-to-≡ $ begin
    ⌞ x ⌟V [ π₁ idS ]t
  ≅⟨ HEq.cong (_[ π₁ idS ]t) (≡-to-≅ (soundnessNfVar x)) ⟩
    accVar x idS [ π₁ idS ]t
  ≅⟨ ≡-to-≅ (accVar[]t x idS (π₁ idS)) ⟩
    accVar x (idS ∘ π₁ idS)
  ≅⟨ HEq.cong (accVar x) (≡-to-≅ (idS∘ π₁ idS)) ⟩
    accVar x (π₁ idS)
  ≅⟨ HEq.sym (conv-rm _ _) ⟩
    conv (congTmΓ (sym (accVarEq.eqTy idS {A}))) (accVar x (π₁ idS))
  ∎
  where open ≅-Reasoning

NfTm[accVar] : (x : Var Γ A){σ : Sub Δ Γ} → NeSub Δ Γ σ → NfTm Δ (accVar x σ)
NfTm[accVar] {Γ , A} {_} {Δ} here {σ} nσ = conv (sym eqTy) (π₂ nσ)
  where
    open ≅-Reasoning
    eqTy : NfTm Δ (conv (congTmΓ (sym (accVarEq.eqTy σ))) (π₂ σ)) ≡ NfTm Δ (π₂ σ)
    eqTy = ≅-to-≡ $ begin
        NfTm Δ (conv (congTmΓ (Eq.sym (accVarEq.eqTy σ))) (π₂ σ))
      ≅⟨ HEq.icong (Tm Δ) (accVarEq.eqTy σ {A}) (NfTm Δ) (conv-rm _ _) ⟩
        NfTm Δ (π₂ σ)
      ∎
NfTm[accVar] {Γ , A'} {_} {Δ} (there {A = A} x) {σ} nσ = conv (sym eqTy) (NfTm[accVar] x (π₁ nσ))
  where
    open ≅-Reasoning
    eqTy : NfTm Δ (conv (congTmΓ (Eq.sym (accVarEq.eqTy σ))) (accVar x (π₁ σ))) ≡ NfTm Δ (accVar x (π₁ σ))
    eqTy = ≅-to-≡ $ begin
        NfTm Δ (conv (congTmΓ (sym (accVarEq.eqTy σ))) (accVar x (π₁ σ)))
      ≅⟨ HEq.icong (Tm Δ) (accVarEq.eqTy σ {A}) (NfTm Δ) (conv-rm _ _) ⟩
        NfTm Δ (accVar x (π₁ σ))
      ∎

NfTm[nfVar] : (x : Var Γ A) → NfTm Γ (nfVar x)
NfTm[nfVar] {Γ} {A} x = NfTm[accVar] x idS

thm[normalization] : (t : Tm Γ A) → Σ[ t' ∈ Tm Γ A ] t ≡ t' × NfTm Γ t'
thm[normalization] t with reifyTm t
... | x / eq = nfVar x / trans eq (soundnessNfVar x) / NfTm[nfVar] x