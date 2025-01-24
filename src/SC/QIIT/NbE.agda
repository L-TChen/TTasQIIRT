module SC.QIIT.NbE where

open import Prelude
  hiding (_∘_)
open import Data.Product
open import SC.QIIT.Base
open import SC.QIIT.Model
open import SC.QIIT.Elimination

-- Definition of Variables and Renaming
-- with embedding into Tm and Sub
data Var : (Γ : Ctx) → Ty Γ → Set where
  here  : Var (Γ , A) (A [ π₁ idS ])
  there : Var Γ A → Var (Γ , B) (A [ π₁ idS ])

⌞_⌟V : Var Γ A → Tm Γ A
⌞ here ⌟V = π₂ idS
⌞ there x ⌟V  = ⌞ x ⌟V [ π₁ idS ]

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
⌞↑R⌟ : (ρ : Ren Δ Γ)(A : Ty Δ) → ⌞ ρ ⌟R ∘ π₁ idS ≡ ⌞ ρ ↑R A ⌟R
∅ ↑R A = ∅
_↑R_ {Δ} (_,_ {A = A'} ρ x) A = (ρ ↑R A) , conv eq (there x) -- conv eq (there x) 
  module ↑RTy where
    eqA'[] : A' [ ⌞ ρ ⌟R ] [ π₁ idS ] ≡ A' [ ⌞ ρ ↑R A ⌟R ]
    eqA'[] = trans (sym ([∘] A' _ _)) (congA[] (⌞↑R⌟ ρ A))
    
    eq : Var (Δ , A) (A' [ ⌞ ρ ⌟R ] [ π₁ idS ]) ≡ Var (Δ , A) (A' [ ⌞ ρ ↑R A ⌟R ])
    eq = cong (Var (Δ , A)) eqA'[]
⌞↑R⌟ ∅ A = η∅
⌞↑R⌟ {Δ} (_,_ {A = A'} ρ x) A = ≅-to-≡ $ begin
    (⌞ ρ ⌟R , ⌞ x ⌟V) ∘ π₁ idS
  ≡⟨ ,∘ ⟩
    ⌞ ρ ⌟R ∘ π₁ idS , conv (congTmΓ (sym ([∘] A' ⌞ ρ ⌟R (π₁ idS)))) ⌞ there x ⌟V
  ≡⟨ cong,Sub' {A = A'} refl (⌞↑R⌟ ρ A) eq,r ⟩
    ⌞ ρ ↑R A ⌟R , ⌞ conv (↑RTy.eq ρ x A) (there x) ⌟V
  ∎
  where
    open ≅-Reasoning
    eq,r : conv (congTmΓ (congA[] (⌞↑R⌟ ρ A))) (conv (congTmΓ (sym ([∘] A' ⌞ ρ ⌟R (π₁ idS)))) ⌞ there x ⌟V)
           ≡ ⌞ conv (↑RTy.eq ρ x A) (there x) ⌟V
    eq,r = ≅-to-≡ $ begin
        conv (congTmΓ (congA[] (⌞↑R⌟ ρ A))) (conv (congTmΓ (sym ([∘] A' ⌞ ρ ⌟R (π₁ idS)))) ⌞ there x ⌟V)
      ≅⟨ conv-rm (congTmΓ (congA[] (⌞↑R⌟ ρ A))) _ ⟩
        conv (congTmΓ (sym ([∘] A' ⌞ ρ ⌟R (π₁ idS)))) ⌞ there x ⌟V
      ≅⟨ conv-rm (congTmΓ (sym ([∘] A' ⌞ ρ ⌟R (π₁ idS)))) _ ⟩
        ⌞ there x ⌟V
      ≅⟨ HEq.icong (Var (Δ , A)) (↑RTy.eqA'[] ρ x A) ⌞_⌟V (HEq.sym (conv-rm (↑RTy.eq ρ x A) (there x))) ⟩
        ⌞ conv (↑RTy.eq ρ x A) (there x) ⌟V
      ∎

idR : Ren Δ Δ
⌞idR⌟ : idS ≡ ⌞ idR {Δ} ⌟R
⌞idR↑⌟ : (A : Ty Γ) → π₁ idS ≡ ⌞ idR ↑R A ⌟R
idR {∅} = ∅
idR {Δ , A} = (idR ↑R A) , conv (cong (Var (Δ , A)) eq) here
  module idRTy where
    eq : A [ π₁ idS ] ≡ A [ ⌞ idR ↑R A ⌟R ]
    eq = congA[] (⌞idR↑⌟ A)
⌞idR⌟ {∅} = η∅
⌞idR⌟ {Δ , A} = ≅-to-≡ $ begin
    idS
  ≡⟨ ηπ ⟩
    π₁ idS , π₂ idS
  ≡⟨ cong,Sub' {A = A} refl (⌞idR↑⌟ A) eq,r ⟩
    ⌞ idR ↑R A ⌟R , ⌞ conv (cong (Var (Δ , A)) (congA[] (⌞idR↑⌟ A))) here ⌟V
  ≡⟨⟩
    ⌞ idR ↑R A  , conv (cong (Var (Δ , A)) (congA[] (⌞idR↑⌟ A))) here ⌟R
  ∎
  where
    open ≅-Reasoning
    eq,r : conv (congTmΓ (congA[] (⌞idR↑⌟ A))) (π₂ idS) 
         ≡ ⌞ conv (cong (Var (Δ , A)) (congA[] (⌞idR↑⌟ A))) here ⌟V
    eq,r = ≅-to-≡ $ begin
        conv (congTmΓ (congA[] (⌞idR↑⌟ A))) (π₂ idS)
      ≅⟨ conv-rm (congTmΓ (congA[] (⌞idR↑⌟ A))) _ ⟩
        π₂ idS
      ≅⟨ HEq.icong (Var (Δ , A)) (congA[] (⌞idR↑⌟ A)) ⌞_⌟V (HEq.sym (conv-rm (cong (Var (Δ , A)) (congA[] (⌞idR↑⌟ A))) _)) ⟩
        ⌞ conv (cong (Var (Δ , A)) (congA[] (⌞idR↑⌟ A))) here ⌟V
      ∎
⌞idR↑⌟ A = begin
    π₁ idS
  ≡⟨ sym (idS∘ π₁ idS) ⟩
    idS ∘ π₁ idS
  ≡⟨ cong∘' ⌞idR⌟ refl ⟩
    ⌞ idR ⌟R ∘ π₁ idS
  ≡⟨ ⌞↑R⌟ idR A ⟩
    ⌞ idR ↑R A ⌟R
  ∎
  where open ≡-Reasoning

lookupVar : (ρ : Ren Δ Γ) → Var Γ A → Var Δ (A [ ⌞ ρ ⌟R ])
lookupVar {Δ} {Γ , _} (_,_ ρ x) here = conv (cong (Var Δ) eq) x
  module lkVarEq where
    open  ≡-Reasoning
    eq : {A A' : Ty Γ}{x : Var Δ (A' [ ⌞ ρ ⌟R ])} → A [ ⌞ ρ ⌟R ] ≡ A [ π₁ idS ] [ ⌞ ρ ⌟R , ⌞ x ⌟V ]
    eq {A = A} {x = x} = begin
        A [ ⌞ ρ ⌟R ]
      ≡⟨ congA[] (sym (βπ₁ {σ = ⌞ ρ ⌟R} {t = ⌞ x ⌟V})) ⟩
        A [ π₁ (⌞ ρ ⌟R , ⌞ x ⌟V) ]
      ≡⟨ congA[] (sym (π₁idS∘ (⌞ ρ ⌟R , ⌞ x ⌟V))) ⟩
        A [ π₁ idS ∘ (⌞ ρ ⌟R , ⌞ x ⌟V) ]
      ≡⟨ [∘] A (π₁ idS) (⌞ ρ ⌟R , ⌞ x ⌟V) ⟩
        A [ π₁ idS ] [ ⌞ ρ ⌟R , ⌞ x ⌟V ]
      ∎
lookupVar {Δ} {Γ , _} (_,_ {A = A} ρ x') (there {A = A'} x) = conv (cong (Var Δ) (lkVarEq.eq Γ A ρ x')) (lookupVar ρ x)

-- Several lemmas
⌞lookup⌟ : (ρ : Ren Δ Γ)(x : Var Γ A) → ⌞ x ⌟V [ ⌞ ρ ⌟R ] ≡ ⌞ lookupVar ρ x ⌟V
⌞lookup⌟ {Δ} {Γ , A} (ρ , x) here = ≅-to-≡ $ begin
    π₂ idS [ ⌞ ρ ⌟R , ⌞ x ⌟V ]
  ≡⟨ sym (π₂∘ idS (⌞ ρ ⌟R , ⌞ x ⌟V)) ⟩
    conv (congTmΓ (trans (congA[] (π₁∘ idS (⌞ ρ ⌟R , ⌞ x ⌟V))) ([∘] A (π₁ idS) (⌞ ρ ⌟R , ⌞ x ⌟V))))
         (π₂ (idS ∘ (⌞ ρ ⌟R , ⌞ x ⌟V)))
  ≅⟨ conv-rm (congTmΓ (trans (congA[] (π₁∘ idS (⌞ ρ ⌟R , ⌞ x ⌟V))) ([∘] A (π₁ idS) (⌞ ρ ⌟R , ⌞ x ⌟V)))) _ ⟩
    π₂ (idS ∘ (⌞ ρ ⌟R , ⌞ x ⌟V))
  ≅⟨ HEq.cong π₂ (≡-to-≅ (idS∘ (⌞ ρ ⌟R , ⌞ x ⌟V))) ⟩
    π₂ (⌞ ρ ⌟R , ⌞ x ⌟V)
  ≅⟨ HEq.sym (conv-rm (congTmΓ (congA[] βπ₁)) _) ⟩
    conv (congTmΓ (congA[] βπ₁)) (π₂ (⌞ ρ ⌟R , ⌞ x ⌟V))
  ≅⟨ ≡-to-≅ βπ₂ ⟩
    ⌞ x ⌟V
  ≅⟨ HEq.icong (Var Δ) (lkVarEq.eq Γ A ρ x) ⌞_⌟V (HEq.sym (conv-rm (cong (Var Δ) (lkVarEq.eq Γ A ρ x {A} {_} {x})) _)) ⟩
    ⌞ conv (cong (Var Δ) (lkVarEq.eq Γ A ρ x {A} {_} {x})) x ⌟V
  ∎
  where open ≅-Reasoning
⌞lookup⌟ {Δ} {Γ , A'} (ρ , x') (there {A = A} x) = ≅-to-≡ $ begin
    ⌞ x ⌟V [ π₁ idS ] [ ⌞ ρ ⌟R , ⌞ x' ⌟V ]
  ≡⟨ sym ([∘]tm ⌞ x ⌟V (π₁ idS) (⌞ ρ ⌟R , ⌞ x' ⌟V)) ⟩
    conv (congTmΓ ([∘] A (π₁ idS) (⌞ ρ ⌟R , ⌞ x' ⌟V))) (⌞ x ⌟V [ π₁ idS ∘ (⌞ ρ ⌟R , ⌞ x' ⌟V) ])
  ≅⟨ conv-rm (congTmΓ ([∘] A (π₁ idS) (⌞ ρ ⌟R , ⌞ x' ⌟V))) _ ⟩
    ⌞ x ⌟V [ π₁ idS ∘ (⌞ ρ ⌟R , ⌞ x' ⌟V) ]
  ≅⟨ HEq.cong {A = Sub Δ Γ} {B = λ σ → Tm Δ (A [ σ ])} (⌞ x ⌟V [_]) eq ⟩
    ⌞ x ⌟V [ ⌞ ρ ⌟R ]
  ≅⟨ ≡-to-≅ (⌞lookup⌟ ρ x) ⟩
    ⌞ lookupVar ρ x ⌟V
  ≅⟨ HEq.icong (Var Δ) (lkVarEq.eq Γ A' ρ x' {A} {_} {x'}) ⌞_⌟V (HEq.sym (conv-rm (cong (Var Δ) (lkVarEq.eq Γ A' ρ x')) _)) ⟩
    ⌞ conv (cong (Var Δ) (lkVarEq.eq Γ A' ρ x')) (lookupVar ρ x) ⌟V
  ∎
  where
    open ≅-Reasoning
    eq : π₁ idS ∘ (⌞ ρ ⌟R , ⌞ x' ⌟V) ≅ ⌞ ρ ⌟R
    eq = begin
        π₁ idS ∘ (⌞ ρ ⌟R , ⌞ x' ⌟V)
      ≡⟨ π₁idS∘ (⌞ ρ ⌟R , ⌞ x' ⌟V) ⟩
        π₁ (⌞ ρ ⌟R , ⌞ x' ⌟V)
      ≡⟨ βπ₁ ⟩
        ⌞ ρ ⌟R
      ∎

-- Composition of renamings
_⊙_ : Ren Δ Γ → Ren Θ Δ → Ren Θ Γ
⌞⊙⌟ : (ρ : Ren Δ Γ)(ρ' : Ren Θ Δ) → ⌞ ρ ⌟R ∘ ⌞ ρ' ⌟R ≡ ⌞ ρ ⊙ ρ' ⌟R
∅ ⊙ _ = ∅
_⊙_ {Θ = Θ} (ρ , x) ρ' = (ρ ⊙ ρ') , conv (cong (Var Θ) eqA[]) (lookupVar ρ' x)
  module ⊙Eq where
    open ≡-Reasoning
    eqA[] : A [ ⌞ ρ ⌟R ] [ ⌞ ρ' ⌟R ] ≡ A [ ⌞ ρ ⊙ ρ' ⌟R ]
    eqA[] {A = A} = begin
        A [ ⌞ ρ ⌟R ] [ ⌞ ρ' ⌟R ]
      ≡⟨ sym ([∘] A ⌞ ρ ⌟R ⌞ ρ' ⌟R) ⟩
        A [ ⌞ ρ ⌟R ∘ ⌞ ρ' ⌟R ]
      ≡⟨ congA[] (⌞⊙⌟ ρ ρ') ⟩
        A [ ⌞ ρ ⊙ ρ' ⌟R ]
      ∎
⌞⊙⌟ ∅ ρ' = η∅
⌞⊙⌟ {Δ} {Γ , A} {Θ} (ρ , x) ρ' = ≅-to-≡ $ begin
    (⌞ ρ ⌟R , ⌞ x ⌟V) ∘ ⌞ ρ' ⌟R
  ≡⟨ ,∘ ⟩
    ⌞ ρ ⌟R ∘ ⌞ ρ' ⌟R , conv (congTmΓ (sym ([∘] A ⌞ ρ ⌟R ⌞ ρ' ⌟R))) (⌞ x ⌟V [ ⌞ ρ' ⌟R ])
  ≡⟨ cong,Sub' {A = A} refl (⌞⊙⌟ ρ ρ') eq,r ⟩
    ⌞ ρ ⊙ ρ' ⌟R , ⌞ conv (cong (Var Θ) (⊙Eq.eqA[] ρ x ρ')) (lookupVar ρ' x) ⌟V
  ∎
  where
    open ≅-Reasoning
    eq,r : conv (congTmΓ (congA[] (⌞⊙⌟ ρ ρ'))) (conv (congTmΓ (sym ([∘] A ⌞ ρ ⌟R ⌞ ρ' ⌟R))) (⌞ x ⌟V [ ⌞ ρ' ⌟R ]))
         ≡ ⌞ conv (cong (Var Θ) (⊙Eq.eqA[] ρ x ρ')) (lookupVar ρ' x) ⌟V
    eq,r = ≅-to-≡ $ begin
        conv (congTmΓ (congA[] (⌞⊙⌟ ρ ρ'))) (conv (congTmΓ (sym ([∘] A ⌞ ρ ⌟R ⌞ ρ' ⌟R))) (⌞ x ⌟V [ ⌞ ρ' ⌟R ]))
      ≅⟨ conv-rm (congTmΓ (congA[] (⌞⊙⌟ ρ ρ'))) _ ⟩
        conv (congTmΓ (sym ([∘] A ⌞ ρ ⌟R ⌞ ρ' ⌟R))) (⌞ x ⌟V [ ⌞ ρ' ⌟R ])
      ≅⟨ conv-rm (congTmΓ (sym ([∘] A ⌞ ρ ⌟R ⌞ ρ' ⌟R))) _ ⟩
        ⌞ x ⌟V [ ⌞ ρ' ⌟R ]
      ≅⟨ ≡-to-≅ (⌞lookup⌟ ρ' x) ⟩
        ⌞ lookupVar ρ' x ⌟V
      ≅⟨ HEq.icong (Var Θ) (⊙Eq.eqA[] ρ x ρ') ⌞_⌟V (HEq.sym (conv-rm (cong (Var Θ) (⊙Eq.eqA[] ρ x ρ')) _)) ⟩
        ⌞ conv (cong (Var Θ) (⊙Eq.eqA[] ρ x ρ')) (lookupVar ρ' x) ⌟V
      ∎

-- Reification of terms and substitutions into variables and renamings
DomainDecl : Pdc
DomainDecl .Pdc.PCtx Γ = Σ[ Γ' ∈ Ctx ] Γ ≡ Γ'
DomainDecl .Pdc.PTy (Γ , refl) A = Σ[ A' ∈ Ty Γ ] A ≡ A'
DomainDecl .Pdc.PSub (Γ , refl) (Δ , refl) σ = Σ[ ρ ∈ Ren Γ Δ ] σ ≡ ⌞ ρ ⌟R
DomainDecl .Pdc.PTm (Γ , refl) (A , eq) t = Σ[ x ∈ Var Γ A ] conv (congTmΓ eq) t ≡ ⌞ x ⌟V

Domain : IH DomainDecl
IH._[_]P Domain {PΓ = Γ , refl} {PΔ = Δ , refl} (A , eqA) (ρ , eqρ) = A [ ⌞ ρ ⌟R ] , cong[] refl eqA refl eqρ
Domain .IH.∅Ctx = ∅ , refl
Domain .IH._,Ctx_ (Γ , refl) (A , refl) = (Γ , A) , refl
Domain .IH.∅Sub {PΔ = Δ , refl} = ∅ , refl
IH._,Sub_ Domain {PΔ = Δ , refl} {Γ , refl} {A , refl} (ρ , refl) (x , eqx) = (ρ , x) , cong (⌞ ρ ⌟R ,_) eqx
Domain .IH.PidS {PΔ = Γ , refl} = idR , ⌞idR⌟
Domain .IH._∘P_ {PΓ = Γ , refl} {Δ , refl} {Θ , refl} (ρ , refl) (ρ' , refl) = ρ ⊙ ρ' , ⌞⊙⌟ ρ ρ'
Domain .IH.π₁P {PΔ = Δ , refl} {Γ , refl} {A , refl} ((ρ , x) , refl) = ρ , βπ₁
Domain .IH.PU {PΓ = Γ , refl} = U , refl
Domain .IH.π₂P {PΔ = Δ , refl} {Γ , refl} {A , refl} ((ρ , x) , refl) = x , βπ₂
IH._[_]tP Domain {PΓ = Γ , refl} {A , refl} {Δ , refl} (x , refl) (ρ , refl) = lookupVar ρ x , ⌞lookup⌟ ρ x

open elim DomainDecl Domain

reifyTm : (t : Tm Γ A) → Σ[ x ∈ Var Γ A ] t ≡ ⌞ x ⌟V
reifyTm {Γ} {A} t with ElimCtx Γ | ElimTy A | ElimTm t
... | .Γ , refl | .A , refl | x , eq = x , eq

-- Inductive definition of the normal form
data NeSub (Δ : Ctx) : (Γ : Ctx) → Sub Δ Γ → Set where
  idS : NeSub Δ Δ idS
  π₁  : NeSub Δ (Γ , A) σ → NeSub Δ Γ (π₁ σ)

data NfTm (Δ : Ctx) : Tm Δ A → Set where
  π₂ : NeSub Δ (Γ , A) σ → NfTm Δ {A [ π₁ σ ]} (π₂ σ)

accVar : (x : Var Γ A)(σ : Sub Δ Γ) → Tm Δ (A [ σ ])
accVar here σ = conv (congTmΓ eqTy) (π₂ σ)
  module accVarEq where
    open ≡-Reasoning
    eqTy : A [ π₁ σ ] ≡ A [ π₁ idS ] [ σ ]
    eqTy {A = A} = begin
        A [ π₁ σ ]
      ≡⟨ congA[] (sym (π₁idS∘ σ)) ⟩
        A [ π₁ idS ∘ σ ]
      ≡⟨ [∘] A (π₁ idS) σ ⟩
        A [ π₁ idS ] [ σ ]
      ∎
accVar (there x) σ = conv (congTmΓ (accVarEq.eqTy σ)) (accVar x (π₁ σ))

accVar[]tm : (x : Var Γ A)(σ : Sub Δ Γ)(τ : Sub Θ Δ) → conv (congTmΓ ([∘] A σ τ)) (accVar x (σ ∘ τ)) ≡ accVar x σ [ τ ]
accVar[]tm {Γ , A} {_} {Δ} {Θ} here σ τ = ≅-to-≡ $ begin
    conv (congTmΓ ([∘] (A [ π₁ idS ]) σ τ)) (conv (congTmΓ (accVarEq.eqTy (σ ∘ τ))) (π₂ (σ ∘ τ)))
  ≅⟨ conv-rm (congTmΓ ([∘] (A [ π₁ idS ]) σ τ)) _ ⟩
    conv (congTmΓ (accVarEq.eqTy (σ ∘ τ))) (π₂ (σ ∘ τ))
  ≅⟨ conv~unique (congTmΓ (accVarEq.eqTy (σ ∘ τ)))
                 (congTmΓ (trans (congA[] (π₁∘ σ τ)) ([∘] A (π₁ σ) τ))) _ ⟩
    conv (congTmΓ (trans (congA[] (π₁∘ σ τ)) ([∘] A (π₁ σ) τ))) (π₂ (σ ∘ τ))
  ≅⟨ ≡-to-≅ (π₂∘ σ τ) ⟩
    π₂ σ [ τ ]
  ≅⟨ HEq.icong (Tm Δ) (accVarEq.eqTy σ) (_[ τ ]) (HEq.sym (conv-rm (congTmΓ (accVarEq.eqTy σ)) _)) ⟩
    conv (congTmΓ (accVarEq.eqTy σ)) (π₂ σ) [ τ ]
  ∎
  where open ≅-Reasoning
accVar[]tm {Γ , A'} {_} {Δ} {Θ} (there {A = A} x) σ τ = ≅-to-≡ $ begin
    conv (congTmΓ ([∘] (A [ π₁ idS ]) σ τ)) (conv (congTmΓ (accVarEq.eqTy (σ ∘ τ))) (accVar x (π₁ (σ ∘ τ))))
  ≅⟨ conv-rm (congTmΓ ([∘] (A [ π₁ idS ]) σ τ)) _ ⟩
    conv (congTmΓ (accVarEq.eqTy (σ ∘ τ))) (accVar x (π₁ (σ ∘ τ)))
  ≅⟨ conv-rm (congTmΓ (accVarEq.eqTy (σ ∘ τ))) _ ⟩
    accVar x (π₁ (σ ∘ τ))
  ≅⟨ HEq.cong (accVar x) (≡-to-≅ (π₁∘ σ τ)) ⟩
    accVar x (π₁ σ ∘ τ)
  ≅⟨ HEq.sym (conv-rm (congTmΓ ([∘] A (π₁ σ) τ)) _) ⟩
    conv (congTmΓ ([∘] A (π₁ σ) τ)) (accVar x (π₁ σ ∘ τ))
  ≅⟨ ≡-to-≅ (accVar[]tm x (π₁ σ) τ) ⟩
    accVar x (π₁ σ) [ τ ]
  ≅⟨ HEq.icong (Tm Δ) (accVarEq.eqTy σ) (_[ τ ]) (HEq.sym (conv-rm (congTmΓ (accVarEq.eqTy σ)) _)) ⟩
    conv (congTmΓ (accVarEq.eqTy σ)) (accVar x (π₁ σ)) [ τ ]
  ∎
  where open ≅-Reasoning

nfVar : (x : Var Γ A) → Tm Γ A
nfVar x = conv (congTmΓ ([idS] _)) (accVar x idS)

soundnessNfVar : (x : Var Γ A) → nfVar x ≡ ⌞ x ⌟V
soundnessNfVar {Γ , A'} {A} here = ≅-to-≡ $ begin
    conv (congTmΓ ([idS] A)) (conv (congTmΓ (accVarEq.eqTy idS)) (π₂ idS))
  ≅⟨ conv-rm (congTmΓ ([idS] A)) _ ⟩
    conv (congTmΓ (accVarEq.eqTy idS)) (π₂ idS)
  ≅⟨ conv-rm _ _ ⟩
    π₂ idS
  ∎
  where open ≅-Reasoning
soundnessNfVar {Γ , B} (there {A = A} x) = ≅-to-≡ $ begin
    conv (congTmΓ ([idS] (A [ π₁ idS ]))) (conv (congTmΓ (accVarEq.eqTy idS)) (accVar x (π₁ idS)))
  ≅⟨ conv-rm (congTmΓ ([idS] (A [ π₁ idS ]))) _ ⟩
    conv (congTmΓ (accVarEq.eqTy idS)) (accVar x (π₁ idS))
  ≅⟨ conv-rm (congTmΓ (accVarEq.eqTy idS)) _ ⟩
    accVar x (π₁ idS)
  ≅⟨ HEq.cong (accVar x) (≡-to-≅ (sym (idS∘ π₁ idS))) ⟩
    accVar x (idS ∘ π₁ idS)
  ≅⟨ HEq.sym (conv-rm (congTmΓ ([∘] A idS (π₁ idS))) _) ⟩
    conv (congTmΓ ([∘] A idS (π₁ idS))) (accVar x (idS ∘ π₁ idS))
  ≅⟨ ≡-to-≅ (accVar[]tm x idS (π₁ idS)) ⟩
    accVar x idS [ π₁ idS ]
  ≅⟨ HEq.icong (Tm Γ) ([idS] A) (_[ π₁ {A = B} idS ]) (HEq.sym (conv-rm (congTmΓ ([idS] A)) _)) ⟩
    conv (congTmΓ ([idS] A)) (accVar x idS) [ π₁ idS ]
  ≡⟨ cong (_[ π₁ idS ]) (soundnessNfVar x) ⟩
    ⌞ x ⌟V [ π₁ idS ]
  ∎
  where open ≅-Reasoning

NfTm[accVar] : (x : Var Γ A){σ : Sub Δ Γ} → NeSub Δ Γ σ → NfTm Δ (accVar x σ)
NfTm[accVar] {Γ , A} {_} {Δ} here {σ} nσ = conv (sym eqTy) (π₂ nσ)
  where
    open ≅-Reasoning
    eqTy : NfTm Δ (conv (congTmΓ (accVarEq.eqTy σ)) (π₂ σ)) ≡ NfTm Δ (π₂ σ)
    eqTy = ≅-to-≡ $ begin
        NfTm Δ (conv (congTmΓ (accVarEq.eqTy σ)) (π₂ σ))
      ≅⟨ HEq.icong (Tm Δ) (sym (accVarEq.eqTy σ)) (NfTm Δ) (conv-rm _ _) ⟩
        NfTm Δ (π₂ σ)
      ∎
NfTm[accVar] {Γ , A'} {_} {Δ} (there {A = A} x) {σ} nσ = conv (sym eqTy) (NfTm[accVar] x (π₁ nσ))
  where
    open ≅-Reasoning
    eqTy : NfTm Δ (conv (congTmΓ (accVarEq.eqTy σ)) (accVar x (π₁ σ))) ≡ NfTm Δ (accVar x (π₁ σ))
    eqTy = ≅-to-≡ $ begin
        NfTm Δ (conv (congTmΓ (accVarEq.eqTy σ)) (accVar x (π₁ σ)))
      ≅⟨ HEq.icong (Tm Δ) (sym (accVarEq.eqTy σ)) (NfTm Δ) (conv-rm _ _) ⟩
        NfTm Δ (accVar x (π₁ σ))
      ∎

NfTm[nfVar] : (x : Var Γ A) → NfTm Γ (nfVar x)
NfTm[nfVar] {Γ} {A} x = conv (sym eqTy) (NfTm[accVar] x idS) -- NfTm[accVar] x idS
  where
    open ≅-Reasoning
    eqTy : NfTm Γ (nfVar x) ≡ NfTm Γ (accVar x idS)
    eqTy = ≅-to-≡ $ begin
        NfTm Γ (conv (congTmΓ ([idS] A)) (accVar x idS))
      ≅⟨ HEq.icong (Tm Γ) (sym ([idS] A)) (NfTm Γ) (conv-rm _ _) ⟩
        NfTm Γ (accVar x idS)
      ∎

thm[normalization] : (t : Tm Γ A) → Σ[ t' ∈ Tm Γ A ] t' ≡ t × NfTm Γ t'
thm[normalization] t with reifyTm t
... | x , eq = nfVar x , (trans (soundnessNfVar x) (sym eq) , NfTm[nfVar] x) 
