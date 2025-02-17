module SC.QIIT2.NbE where

open import Prelude
  hiding (_∘_)
open import Data.Product
open import SC.QIIT2.Base
open import SC.QIIT2.Model
open import SC.QIIT2.Elimination

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
_↑R_ {Δ} (_,_ {A = A'} ρ x) A = (ρ ↑R A) , tr (Var (Δ , A)) eq (there x) -- conv eq (there x) 
  module ↑RTy where
    eq : A' [ ⌞ ρ ⌟R ] [ π₁ idS ] ≡ A' [ ⌞ ρ ↑R A ⌟R ]
    eq = trans (sym $ [∘] _ _ _) (cong (A' [_]) (⌞↑R⌟ ρ A))
⌞↑R⌟ ∅ A = η∅
⌞↑R⌟ {Δ} (_,_ {A = A'} ρ x) A = begin
  (⌞ ρ ⌟R , ⌞ x ⌟V) ∘ π₁ idS
    ≡⟨ ,∘ ⟩
  ⌞ ρ ⌟R ∘ π₁ idS , tr (Tm (Δ , A)) (sym $ [∘] _ _ _) ⌞ there x ⌟V -- conv (congTmΓ (sym ([∘] A' ⌞ ρ ⌟R (π₁ idS)))) ⌞ there x ⌟V
    ≡⟨ apd₂ _,_ (⌞↑R⌟ ρ A) eq,r ⟩
  ⌞ ρ ↑R A ⌟R , ⌞ tr (Var (Δ , A)) (↑RTy.eq ρ x A) (there x) ⌟V
    ∎
  where
    open ≡-Reasoning
    eq,r : tr (λ σ → Tm (Δ , A) (A' [ σ ])) (⌞↑R⌟ ρ A) (tr (Tm (Δ , A)) (sym $ [∘] _ _ _) ⌞ there x ⌟V)
           ≡ ⌞ tr (Var (Δ , A)) (↑RTy.eq ρ x A) (there x) ⌟V
    eq,r = begin
      tr (λ σ → Tm (Δ , A) (A' [ σ ])) (⌞↑R⌟ ρ A) (tr (Tm (Δ , A)) (sym $ [∘] _ _ _) ⌞ there x ⌟V)
        ≡⟨ tr-cong (⌞↑R⌟ ρ A) ⟩
      tr (Tm (Δ , A)) (cong (A' [_]) (⌞↑R⌟ ρ A)) (tr (Tm (Δ , A)) (sym $ [∘] _ _ _) ⌞ there x ⌟V)
        ≡⟨ tr² (sym $ [∘] _ _ _) ⟩
      tr (Tm (Δ , A)) (trans (sym $ [∘] _ _ _) (cong (A' [_]) (⌞↑R⌟ ρ A))) ⌞ there x ⌟V
        ≡⟨ tr-nat (Var (Δ , A)) (λ _ x → ⌞ x ⌟V) (↑RTy.eq ρ x A) ⟩
      ⌞ tr (Var (Δ , A)) (↑RTy.eq ρ x A) (there x) ⌟V
        ∎

idR : Ren Δ Δ
⌞idR⌟ : idS ≡ ⌞ idR {Δ} ⌟R
⌞idR↑⌟ : (A : Ty Γ) → π₁ idS ≡ ⌞ idR ↑R A ⌟R
idR {∅} = ∅
idR {Δ , A} = (idR ↑R A) , tr (Var (Δ , A)) eq here
  module idRTy where
    eq : A [ π₁ idS ] ≡ A [ ⌞ idR ↑R A ⌟R ]
    eq = cong (A [_]) (⌞idR↑⌟ A)
⌞idR⌟ {∅} = η∅
⌞idR⌟ {Δ , A} = begin
  idS
    ≡⟨ ηπ ⟩
  π₁ idS , π₂ idS
    ≡⟨ apd₂ _,_ (⌞idR↑⌟ A) eq,r ⟩
  ⌞ idR ↑R A ⌟R , ⌞ tr (Var (Δ , A)) (idRTy.eq Δ A) here ⌟V
    ≡⟨⟩
  ⌞ idR ↑R A  ,  tr (Var (Δ , A)) (idRTy.eq Δ A) here ⌟R
    ∎
  where
    open ≡-Reasoning
    eq,r : tr (λ σ → Tm (Δ , A) (A [ σ ])) (⌞idR↑⌟ A) (π₂ idS) ≡ ⌞ tr (Var (Δ , A)) (idRTy.eq Δ A) here ⌟V
    eq,r = begin
      tr (λ σ → Tm (Δ , A) (A [ σ ])) (⌞idR↑⌟ A) (π₂ idS)
        ≡⟨⟩
      tr (λ σ → Tm (Δ , A) (A [ σ ])) (⌞idR↑⌟ A) ⌞ here ⌟V
        ≡⟨ tr-cong (⌞idR↑⌟ A) ⟩
      tr (Tm (Δ , A)) (cong (A [_]) (⌞idR↑⌟ A)) ⌞ here ⌟V
        ≡⟨ tr-nat (Var (Δ , A)) (λ _ x → ⌞ x ⌟V) (idRTy.eq Δ A) ⟩
      ⌞ tr (Var (Δ , A)) (idRTy.eq Δ A) here ⌟V
        ∎
⌞idR↑⌟ A = begin
    π₁ idS
  ≡⟨ idS∘ π₁ idS ⟨
    idS ∘ π₁ idS
  ≡⟨ cong (_∘ π₁ idS) ⌞idR⌟ ⟩
    ⌞ idR ⌟R ∘ π₁ idS
  ≡⟨ ⌞↑R⌟ idR A ⟩
    ⌞ idR ↑R A ⌟R
  ∎
  where open ≡-Reasoning

lookupVar : (ρ : Ren Δ Γ) → Var Γ A → Var Δ (A [ ⌞ ρ ⌟R ])
lookupVar {Δ} {Γ , _} (_,_ ρ x) here = tr (Var Δ) eq x
  module lkVarEq where
    open  ≡-Reasoning
    eq : {A A' : Ty Γ}{x : Var Δ (A' [ ⌞ ρ ⌟R ])} → A [ ⌞ ρ ⌟R ] ≡ A [ π₁ idS ] [ ⌞ ρ ⌟R , ⌞ x ⌟V ]
    eq {A = A} {x = x} = begin
        A [ ⌞ ρ ⌟R ]
      ≡⟨ cong (A [_]) (βπ₁ {σ = ⌞ ρ ⌟R} {t = ⌞ x ⌟V}) ⟨
        A [ π₁ (⌞ ρ ⌟R , ⌞ x ⌟V) ]
      ≡⟨ cong (A [_]) (π₁idS∘ (⌞ ρ ⌟R , ⌞ x ⌟V)) ⟨
        A [ π₁ idS ∘ (⌞ ρ ⌟R , ⌞ x ⌟V) ]
      ≡⟨ [∘] A (π₁ idS) (⌞ ρ ⌟R , ⌞ x ⌟V) ⟩
        A [ π₁ idS ] [ ⌞ ρ ⌟R , ⌞ x ⌟V ]
      ∎
lookupVar {Δ} {Γ , _} (_,_ {A = A} ρ x') (there {A = A'} x) = tr (Var Δ) (lkVarEq.eq Γ A ρ x') (lookupVar ρ x)

-- Several lemmas
⌞lookup⌟ : (ρ : Ren Δ Γ)(x : Var Γ A) → ⌞ x ⌟V [ ⌞ ρ ⌟R ] ≡ ⌞ lookupVar ρ x ⌟V
⌞lookup⌟ {Δ} {Γ , A} (ρ , x) here = ≅-to-≡ $ begin
  π₂ idS [ ⌞ ρ ⌟R , ⌞ x ⌟V ]
    ≡⟨ π₂∘ idS (⌞ ρ ⌟R , ⌞ x ⌟V) ⟨
  tr TmFam (cong (A [_]) (π₁∘ idS (⌞ ρ ⌟R , ⌞ x ⌟V)) ∙ [∘] _ _ _)
     (π₂ (idS ∘ (⌞ ρ ⌟R , ⌞ x ⌟V)))
    ≅⟨ tr≅ TmFam (cong (A [_]) (π₁∘ idS (⌞ ρ ⌟R , ⌞ x ⌟V)) ∙ [∘] _ _ _) _ ⟩
  π₂ (idS ∘ (⌞ ρ ⌟R , ⌞ x ⌟V))
    ≅⟨ hcong π₂ (≡-to-≅ $ idS∘ _) ⟩
  π₂ (⌞ ρ ⌟R , ⌞ x ⌟V)
    ≅⟨ tr≅ (λ σ → TmFam (A [ σ ])) βπ₁ _ ⟨
  tr (λ σ → TmFam (A [ σ ])) βπ₁ (π₂ (⌞ ρ ⌟R , ⌞ x ⌟V))
    ≅⟨ ≡-to-≅ βπ₂ ⟩
  ⌞ x ⌟V
    ≅⟨ icong (Var Δ) (lkVarEq.eq Γ A ρ x) ⌞_⌟V (HEq.sym (tr≅ (Var Δ) (lkVarEq.eq Γ A ρ x) x)) ⟩
  ⌞ tr (Var Δ) (lkVarEq.eq Γ A ρ x) x ⌟V
    ∎
  where open ≅-Reasoning
⌞lookup⌟ {Δ} {Γ , A'} (ρ , x') (there {A = A} x) = ≅-to-≡ $ begin
  ⌞ x ⌟V [ π₁ idS ] [ ⌞ ρ ⌟R , ⌞ x' ⌟V ]
    ≡⟨ [∘]tm ⌞ x ⌟V (π₁ idS) (⌞ ρ ⌟R , ⌞ x' ⌟V) ⟨
  tr TmFam ([∘] _ _ _) (⌞ x ⌟V [ π₁ idS ∘ (⌞ ρ ⌟R , ⌞ x' ⌟V) ])
    ≅⟨ tr≅ TmFam ([∘] _ _ _) _ ⟩
  ⌞ x ⌟V [ π₁ idS ∘ (⌞ ρ ⌟R , ⌞ x' ⌟V) ]
    ≅⟨ hcong {B = λ σ → Tm Δ (A [ σ ])} (⌞ x ⌟V [_]) (≡-to-≅ eq) ⟩
  ⌞ x ⌟V [ ⌞ ρ ⌟R ]
    ≅⟨ ≡-to-≅ $ ⌞lookup⌟ ρ x ⟩
  ⌞ lookupVar ρ x ⌟V
    ≅⟨ icong (Var Δ) (lkVarEq.eq Γ A' ρ x' {A} {_} {x'}) ⌞_⌟V (HEq.sym (tr≅ (Var Δ) (lkVarEq.eq Γ A' ρ x') _)) ⟩
  ⌞ tr (Var Δ) (lkVarEq.eq Γ A' ρ x') (lookupVar ρ x) ⌟V
    ∎
  where
    open ≅-Reasoning
    eq : π₁ idS ∘ (⌞ ρ ⌟R , ⌞ x' ⌟V) ≡ ⌞ ρ ⌟R
    eq = ≅-to-≡ $ begin
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
_⊙_ {Θ = Θ} (ρ , x) ρ' = (ρ ⊙ ρ') , tr (Var Θ) eqA[] (lookupVar ρ' x)
  module ⊙Eq where
    open ≡-Reasoning
    eqA[] : A [ ⌞ ρ ⌟R ] [ ⌞ ρ' ⌟R ] ≡ A [ ⌞ ρ ⊙ ρ' ⌟R ]
    eqA[] {A = A} = begin
      A [ ⌞ ρ ⌟R ] [ ⌞ ρ' ⌟R ]
        ≡⟨ [∘] _ _ _ ⟨
      A [ ⌞ ρ ⌟R ∘ ⌞ ρ' ⌟R ]
        ≡⟨ cong (A [_]) (⌞⊙⌟ ρ ρ') ⟩
      A [ ⌞ ρ ⊙ ρ' ⌟R ]
        ∎
⌞⊙⌟ ∅ ρ' = η∅
⌞⊙⌟ {Δ} {Γ , A} {Θ} (ρ , x) ρ' = begin
    (⌞ ρ ⌟R , ⌞ x ⌟V) ∘ ⌞ ρ' ⌟R
  ≡⟨ ,∘ ⟩
    ⌞ ρ ⌟R ∘ ⌞ ρ' ⌟R , tr TmFam (sym $ [∘] _ _ _) (⌞ x ⌟V [ ⌞ ρ' ⌟R ])
  ≡⟨ apd₂ _,_ (⌞⊙⌟ ρ ρ') eq,r ⟩ -- cong,Sub' {A = A} refl (⌞⊙⌟ ρ ρ') eq,r
    ⌞ ρ ⊙ ρ' ⌟R , ⌞ tr (Var Θ) (⊙Eq.eqA[] ρ x ρ') (lookupVar ρ' x) ⌟V
  ∎
  where
    open ≡-Reasoning
    eq,r : tr (λ σ → TmFam (A [ σ ])) (⌞⊙⌟ ρ ρ') (tr TmFam (sym $ [∘] _ _ _) (⌞ x ⌟V [ ⌞ ρ' ⌟R ]))
         ≡ ⌞ tr (Var Θ) (⊙Eq.eqA[] ρ x ρ') (lookupVar ρ' x) ⌟V
    eq,r = begin
      tr (λ σ → TmFam (A [ σ ])) (⌞⊙⌟ ρ ρ')
         (tr TmFam (sym $ [∘] _ _ _) (⌞ x ⌟V [ ⌞ ρ' ⌟R ]))
        ≡⟨ tr-cong {P = TmFam} (⌞⊙⌟ ρ ρ') ⟩
      tr TmFam (cong (A [_]) (⌞⊙⌟ ρ ρ'))
         (tr TmFam (sym $ [∘] _ _ _) (⌞ x ⌟V [ ⌞ ρ' ⌟R ]))
        ≡⟨ tr² (sym $ [∘] _ _ _) {cong (A [_]) (⌞⊙⌟ ρ ρ')} ⟩
      tr TmFam (sym ([∘] _ _ _) ∙ cong (A [_]) (⌞⊙⌟ ρ ρ')) (⌞ x ⌟V [ ⌞ ρ' ⌟R ])
        ≡⟨ cong (tr TmFam (sym ([∘] _ _ _) ∙ cong (A [_]) (⌞⊙⌟ ρ ρ')))
                (⌞lookup⌟ ρ' x) ⟩
      tr TmFam (sym ([∘] _ _ _) ∙ cong (A [_]) (⌞⊙⌟ ρ ρ')) ⌞ lookupVar ρ' x ⌟V
        ≡⟨ cong (λ p → tr TmFam p ⌞ lookupVar ρ' x ⌟V) (uip _ (⊙Eq.eqA[] ρ x ρ')) ⟩
      tr TmFam (⊙Eq.eqA[] ρ x ρ') ⌞ lookupVar ρ' x ⌟V
        ≡⟨ tr-nat (Var Θ) (λ _ y → ⌞ y ⌟V) (⊙Eq.eqA[] ρ x ρ') ⟩
      ⌞ tr (Var Θ) (⊙Eq.eqA[] ρ x ρ') (lookupVar ρ' x) ⌟V
        ∎

-- Reification of terms and substitutions into variables and renamings
DomainDecl : Pdc
DomainDecl .Pdc.PCtx Γ = Σ[ Γ' ∈ Ctx ] Γ ≡ Γ'
DomainDecl .Pdc.PTy (Γ , refl) A = Σ[ A' ∈ Ty Γ ] A ≡ A'
DomainDecl .Pdc.PSub (Γ , refl) (Δ , refl) σ = Σ[ ρ ∈ Ren Γ Δ ] σ ≡ ⌞ ρ ⌟R
DomainDecl .Pdc.PTm (Γ , refl) (A , eq) t = Σ[ x ∈ Var Γ A ] tr (Tm Γ) eq t ≡ ⌞ x ⌟V

Domain : IH DomainDecl
IH._[_]P Domain {PΓ = Γ , refl} {PΔ = Δ , refl} (A , refl) (ρ , eqρ) = A [ ⌞ ρ ⌟R ] , cong (A [_]) eqρ
Domain .IH.∅Ctx = ∅ , refl
Domain .IH._,Ctx_ (Γ , refl) (A , refl) = (Γ , A) , refl
Domain .IH.∅Sub {PΔ = Δ , refl} = ∅ , refl
IH._,Sub_ Domain {PΔ = Δ , refl} {Γ , refl} {A , refl} (ρ , refl) (x , eqx) = (ρ , x) , cong (⌞ ρ ⌟R ,_) eqx
Domain .IH.PidS {PΔ = Γ , refl} = idR , ⌞idR⌟
Domain .IH._∘P_ {PΓ = Γ , refl} {Δ , refl} {Θ , refl} (ρ , refl) (ρ' , refl) = ρ ⊙ ρ' , ⌞⊙⌟ ρ ρ'
Domain .IH.π₁P {PΔ = Δ , refl} {Γ , refl} {A , refl} ((ρ , x) , refl) = ρ , βπ₁
Domain .IH.PU {PΓ = Γ , refl} = U , refl
Domain .IH.π₂P {PΔ = Δ , refl} {Γ , refl} {A , refl} ((ρ , x) , refl) = x , sym (tr-cong βπ₁) ∙ βπ₂
IH._[_]tP Domain {PΓ = Γ , refl} {A , refl} {Δ , refl} (x , refl) (ρ , refl) = lookupVar ρ x , ⌞lookup⌟ ρ x

open elim DomainDecl Domain

reifyTm : (t : Tm Γ A) → Σ[ x ∈ Var Γ A ] t ≡ ⌞ x ⌟V
reifyTm {Γ} {A} t with ElimCtx Γ | ElimTy A | ElimTm t
... | .Γ , refl | .A , refl | x , eq = x , eq