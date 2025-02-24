module Theory.SC.QIIRT.NbE where

open import Prelude
  renaming (_,_ to _/_)
  hiding (_∘_)
open import Theory.SC.QIIRT.Syntax
open import Theory.SC.QIIRT.Model
open import Theory.SC.QIIRT.Elimination

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

-- Operations about renamings: lift, identity, and variable lookup
_↑R_ : Ren Δ Γ → (A : Ty Δ) → Ren (Δ , A) Γ
⌞↑R⌟ : (ρ : Ren Δ Γ)(A : Ty Δ) → ⌞ ρ ⌟R ∘ π₁ idS ≡ ⌞ ρ ↑R A ⌟R
∅ ↑R A                        = ∅
_↑R_ {Δ} (_,_ {A = A'} ρ x) A = (ρ ↑R A) , tr (Var (Δ , A)) (cong (A' [_]) (⌞↑R⌟ ρ A)) (there x)
⌞↑R⌟ ∅ A = η∅
⌞↑R⌟ {Δ} (_,_ {A = A'} ρ x) A = begin
  (⌞ ρ ⌟R , ⌞ x ⌟V) ∘ π₁ idS
    ≡⟨ ,∘ ⟩
  ⌞ ρ ⌟R ∘ π₁ idS , ⌞ there x ⌟V
    ≡⟨ apd₂ _,_ (⌞↑R⌟ ρ A) eq,r ⟩
  ⌞ ρ ↑R A ⌟R , ⌞ tr (Var (Δ , A)) (cong (A' [_]) (⌞↑R⌟ ρ A)) (there x) ⌟V
    ∎
  where
    open ≡-Reasoning
    eq,r : tr (λ σ → Tm (Δ , A) (A' [ σ ])) (⌞↑R⌟ ρ A) ⌞ there x ⌟V
         ≡ ⌞ tr (Var (Δ , A)) (cong (A' [_]) (⌞↑R⌟ ρ A)) (there x) ⌟V
    eq,r = begin
      tr (λ σ → Tm (Δ , A) (A' [ σ ])) (⌞↑R⌟ ρ A) ⌞ there x ⌟V
        ≡⟨ tr-cong (⌞↑R⌟ ρ A) ⟩
      tr (Tm (Δ , A)) (cong (A' [_]) (⌞↑R⌟ ρ A)) ⌞ there x ⌟V
        ≡⟨ tr-nat (Var (Δ , A)) (λ _ x → ⌞ x ⌟V) (cong (A' [_]) (⌞↑R⌟ ρ A)) ⟩
      ⌞ tr (Var (Δ , A)) (cong (A' [_]) (⌞↑R⌟ ρ A)) (there x) ⌟V
        ∎
    
idR    : Ren Δ Δ
⌞idR⌟  : idS ≡ ⌞ idR {Δ} ⌟R
⌞idR↑⌟ : (A : Ty Γ) → π₁ idS ≡ ⌞ idR ↑R A ⌟R
idR {∅}       = ∅
idR {Δ , A}   = (idR ↑R A) , tr (Var (Δ , A)) (cong (A [_]) (⌞idR↑⌟ A)) here
⌞idR⌟ {∅}     = η∅
⌞idR⌟ {Δ , A} = begin
  idS
    ≡⟨ η, ⟩
  π₁ idS , π₂ idS
    ≡⟨ apd₂ _,_ (⌞idR↑⌟ A) eq,r ⟩
  ⌞ idR ↑R A ⌟R , ⌞ tr (Var (Δ , A)) (cong (A [_]) (⌞idR↑⌟ A)) here ⌟V
    ≡⟨⟩
  ⌞ idR ↑R A , tr (Var (Δ , A)) (cong (A [_]) (⌞idR↑⌟ A)) here  ⌟R
    ∎
  where
    open ≡-Reasoning
    eq,r : tr (λ σ → Tm (Δ , A) (A [ σ ])) (⌞idR↑⌟ A) (π₂ idS) ≡ ⌞ tr (Var (Δ , A)) (cong (A [_]) (⌞idR↑⌟ A)) here ⌟V
    eq,r = begin
      tr (λ σ → Tm (Δ , A) (A [ σ ])) (⌞idR↑⌟ A) (π₂ idS)
        ≡⟨ tr-cong (⌞idR↑⌟ A) ⟩
      tr (Tm (Δ , A)) (cong (A [_]) (⌞idR↑⌟ A)) ⌞ here ⌟V 
        ≡⟨ tr-nat (Var (Δ , A)) (λ _ x → ⌞ x ⌟V) (cong (A [_]) (⌞idR↑⌟ A)) ⟩
      ⌞ tr (Var (Δ , A)) (cong (A [_]) (⌞idR↑⌟ A)) here ⌟V
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
lookupVar {Δ} {Γ , _} (_,_ {A = A} ρ x)   here              = tr (Var Δ) (cong (A [_]) (sym $ π₁idS∘ (⌞ ρ ⌟R , ⌞ x ⌟V))) x
lookupVar {Δ} {Γ , _} (_,_ {A = A} ρ x') (there {A = A'} x) = tr (Var Δ) (cong (A' [_]) (sym $ π₁idS∘ (⌞ ρ ⌟R , ⌞ x' ⌟V))) (lookupVar ρ x)

-- Several lemmas
⌞lookup⌟ : (ρ : Ren Δ Γ)(x : Var Γ A) → ⌞ x ⌟V [ ⌞ ρ ⌟R ]tm ≡ ⌞ lookupVar ρ x ⌟V
⌞lookup⌟ {Δ} {Γ , A} (ρ , x) here = ≅-to-≡ $ begin
  π₂ idS [ ⌞ ρ ⌟R , ⌞ x ⌟V ]tm
    ≡⟨ π₂∘ (⌞ ρ ⌟R , ⌞ x ⌟V) idS ⟨
  π₂ (idS ∘ (⌞ ρ ⌟R , ⌞ x ⌟V))
    ≅⟨ hcong π₂ (≡-to-≅ $ idS∘ (⌞ ρ ⌟R , ⌞ x ⌟V)) ⟩
  π₂ (⌞ ρ ⌟R , ⌞ x ⌟V)
    ≅⟨ ≡-to-≅ $ π₂, ⟩
  ⌞ x ⌟V
    ≅⟨ icong (Var Δ) (cong (A [_]) (π₁idS∘ (⌞ ρ ⌟R , ⌞ x ⌟V))) ⌞_⌟V (tr≅ _ (cong (A [_]) (sym $ π₁idS∘ (⌞ ρ ⌟R , ⌞ x ⌟V))) _) ⟨
  ⌞ tr (Var Δ) (cong (A [_]) (sym $ π₁idS∘ (⌞ ρ ⌟R , ⌞ x ⌟V))) x ⌟V
    ∎
  where open ≅-Reasoning
⌞lookup⌟ {Δ} {Γ , A'} (ρ , x') (there {A = A} x) = ≅-to-≡ $ begin
  ⌞ x ⌟V [ wk ]tm [ ⌞ ρ ⌟R , ⌞ x' ⌟V ]tm  -- reduced by recursion _[_]t
    ≡⟨ [∘]tm ⟨
  ⌞ x ⌟V [ wk ∘ (⌞ ρ ⌟R , ⌞ x' ⌟V) ]tm  
    ≅⟨ hcong {B = λ σ → Tm Δ (A [ σ ])} (λ σ → ⌞ x ⌟V [ σ ]tm) eq ⟩
  ⌞ x ⌟V [ ⌞ ρ ⌟R ]tm
    ≅⟨ ≡-to-≅ $ ⌞lookup⌟ ρ x ⟩
  ⌞ lookupVar ρ x ⌟V
    ≅⟨ icong (Var Δ) (cong (A [_]) (π₁idS∘ (⌞ ρ ⌟R , ⌞ x' ⌟V))) ⌞_⌟V (tr≅ _ (cong (A [_]) (sym $ π₁idS∘ (⌞ ρ ⌟R , ⌞ x' ⌟V))) _) ⟨
  ⌞ tr (Var Δ) (cong (A [_]) (sym $ π₁idS∘ (⌞ ρ ⌟R , ⌞ x' ⌟V))) (lookupVar ρ x) ⌟V
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
_⊙_ {Θ = Θ} (_,_ {A = A} ρ x) ρ' = (ρ ⊙ ρ') , tr (Var Θ) (cong (A [_]) (⌞⊙⌟ ρ ρ')) (lookupVar ρ' x)
⌞⊙⌟ ∅ ρ' = η∅
⌞⊙⌟ {Δ} {Γ , A} {Θ} (ρ , x) ρ' = begin
  (⌞ ρ ⌟R , ⌞ x ⌟V) ∘ ⌞ ρ' ⌟R
    ≡⟨ ,∘ ⟩
  (⌞ ρ ⌟R ∘ ⌞ ρ' ⌟R) , ⌞ x ⌟V [ ⌞ ρ' ⌟R ]tm
    ≡⟨ apd₂ _,_ (⌞⊙⌟ ρ ρ') eq,r ⟩
  ⌞ ρ ⊙ ρ' ⌟R , ⌞ tr (Var Θ) (cong (A [_]) (⌞⊙⌟ ρ ρ')) (lookupVar ρ' x) ⌟V
    ∎
  where
    open ≡-Reasoning
    eq,r : tr (λ σ → Tm Θ (A [ σ ])) (⌞⊙⌟ ρ ρ') (⌞ x ⌟V [ ⌞ ρ' ⌟R ]tm)
         ≡ ⌞ tr (Var Θ) (cong (A [_]) (⌞⊙⌟ ρ ρ')) (lookupVar ρ' x) ⌟V
    eq,r = begin
      tr (λ σ → Tm Θ (A [ σ ])) (⌞⊙⌟ ρ ρ') (⌞ x ⌟V [ ⌞ ρ' ⌟R ]tm)
        ≡⟨ tr-cong {P = Tm Θ} (⌞⊙⌟ ρ ρ') ⟩
      tr (Tm Θ) (cong (A [_]) (⌞⊙⌟ ρ ρ')) (⌞ x ⌟V [ ⌞ ρ' ⌟R ]tm)
        ≡⟨ cong (tr (Tm Θ) (cong (A [_]) (⌞⊙⌟ ρ ρ'))) (⌞lookup⌟ ρ' x) ⟩
      tr (Tm Θ) (cong (A [_]) (⌞⊙⌟ ρ ρ')) ⌞ lookupVar ρ' x ⌟V
        ≡⟨ tr-nat (Var Θ) (λ _ y → ⌞ y ⌟V) (cong (A [_]) (⌞⊙⌟ ρ ρ')) ⟩
      ⌞ tr (Var Θ) (cong (A [_]) (⌞⊙⌟ ρ ρ')) (lookupVar ρ' x) ⌟V
        ∎

-- Reification of terms and substitutions into variables and renamings
DomainDecl : Pdc
DomainDecl .Pdc.PCtx Γ = Σ[ Γ' ∈ Ctx ] Γ ≡ Γ'
DomainDecl .Pdc.PTy (Γ / refl) A = Σ[ A' ∈ Ty Γ ] A ≡ A'
DomainDecl .Pdc.PSub (Γ / refl) (Δ / refl) σ = Σ[ ρ ∈ Ren Γ Δ ] σ ≡ ⌞ ρ ⌟R
DomainDecl .Pdc.PTm (Γ / refl) (A / eq) t = Σ[ x ∈ Var Γ A ] tr (Tm Γ) eq t ≡ ⌞ x ⌟V

Domain : IH DomainDecl
IH._[_]P Domain {PΓ = Γ / refl} {PΔ = Δ / refl} (A / refl) (ρ / eqρ) = A [ ⌞ ρ ⌟R ] / cong (A [_]) eqρ
Domain .IH.∅Ctx = ∅ / refl
Domain .IH._,Ctx_ (Γ / refl) (A / refl) = (Γ , A) / refl
Domain .IH.∅Sub {PΔ = Δ / refl} = ∅ / refl
IH._,Sub_ Domain {PΔ = Δ / refl} {Γ / refl} {A / refl} (ρ / refl) (x / eqx) = (ρ , x) / cong (⌞ ρ ⌟R ,_) eqx
Domain .IH.PidS {PΔ = Γ / refl} = idR / ⌞idR⌟
Domain .IH._∘P_ {PΓ = Γ / refl} {Δ / refl} {Θ / refl} (ρ / refl) (ρ' / refl) = ρ ⊙ ρ' / ⌞⊙⌟ ρ ρ'
Domain .IH.π₁P {PΔ = Δ / refl} {Γ / refl} {A / refl} ((ρ , x) / refl) = ρ / π₁,
Domain .IH.PU {PΓ = Γ / refl} = U / refl
Domain .IH.PU[] {PΓ = Γ / refl} {Δ / refl} {ρ / refl} = refl
Domain .IH.π₂P {PΔ = Δ / refl} {Γ / refl} {A / refl} ((ρ , x) / refl) = x / cong (λ p → tr (Tm Δ) p (π₂ {A = A} (⌞ ρ ⌟R , ⌞ x ⌟V))) (uip (cong (A [_]) π₁,) refl) ∙ π₂, {σ = ⌞ ρ ⌟R} {t = ⌞ x ⌟V}
Domain .IH._[_]tmP {PΓ = Γ / refl} {A / refl} {Δ / refl} (x / refl) (ρ / refl) = lookupVar ρ x / ⌞lookup⌟ ρ x

open elim DomainDecl Domain

reifyTm : (t : Tm Γ A) → Σ[ x ∈ Var Γ A ] t ≡ ⌞ x ⌟V
reifyTm {Γ} {A} t with ElimCtx Γ | ElimTy A | ElimTm t
... | .Γ / refl | .A / refl | x / eq = x / eq