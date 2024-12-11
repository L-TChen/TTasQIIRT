module SC.QIIT.NbE where

open import Prelude
open import Data.Product
open import SC.QIIT.Base
open Eq.≡-Reasoning

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
⌞↑R⌟ : (ρ : Ren Δ Γ)(A : Ty Δ) → ⌞ ρ ↑R A ⌟R ≡ ⌞ ρ ⌟R ∘ π₁ idS
∅ ↑R A = ∅
_↑R_ {Δ} (_,_ {A = A'} ρ x) A = (ρ ↑R A) , conv (sym eq) (there x) 
  module ↑RTy where
    eqA'[] : A' [ ⌞ ρ ↑R A ⌟R ] Eq.≡ A' [ ⌞ ρ ⌟R ] [ π₁ idS ]
    eqA'[] = trans (congA[] (⌞↑R⌟ ρ A)) ([∘] A' _ _)
    
    eq : Var (Δ , A) (A' [ ⌞ ρ ↑R A ⌟R ]) ≡ Var (Δ , A) (A' [ ⌞ ρ ⌟R ] [ π₁ idS ])
    eq = cong (Var (Δ , A)) eqA'[]
⌞↑R⌟ ∅ A = sym η∅
⌞↑R⌟ {Δ} (_,_ {A = A'} ρ x) A = begin
    ⌞ ρ ↑R A ⌟R , ⌞ conv (sym (↑RTy.eq ρ x A)) (there x) ⌟V
  ≡⟨ cong,Sub' {A = A'} refl (⌞↑R⌟ ρ A) eq,r ⟩
    ⌞ ρ ⌟R ∘ π₁ idS , conv (congTmΓ (sym ([∘] A' ⌞ ρ ⌟R (π₁ idS)))) ⌞ there x ⌟V
  ≡⟨ sym ,∘ ⟩
    ⌞ ρ , x ⌟R ∘ π₁ idS
  ∎
  where
    eq,r : conv (congTmΓ (cong[] refl {A'} refl refl (⌞↑R⌟ ρ A))) ⌞ conv (sym (↑RTy.eq ρ x A)) (there x) ⌟V
           ≡ conv (congTmΓ (sym ([∘] A' ⌞ ρ ⌟R (π₁ idS)))) (⌞ there x ⌟V)
    eq,r = begin
        conv (congTmΓ (cong[] refl {A'} refl refl (⌞↑R⌟ ρ A))) ⌞ conv (sym (↑RTy.eq ρ x A)) (there x) ⌟V
      ≡⟨ cong (conv (congTmΓ (cong[] refl {A'} refl refl (⌞↑R⌟ ρ A)))) 
              (conv-in-func {Y = Var (Δ , A)} (sym (↑RTy.eqA'[] ρ x A)) ⌞_⌟V (sym (↑RTy.eq ρ x A)) (there x)
                            (sym (congTmΓ (↑RTy.eqA'[] ρ x A)))) ⟩
        conv (congTmΓ (cong[] refl {A'} refl refl (⌞↑R⌟ ρ A))) (conv (sym (congTmΓ (↑RTy.eqA'[] ρ x A))) ⌞ there x ⌟V)
      ≡⟨ conv² (sym (congTmΓ (↑RTy.eqA'[] ρ x A))) (congTmΓ (cong[] refl {A'} refl refl (⌞↑R⌟ ρ A))) ⟩
        conv (trans (sym (congTmΓ (↑RTy.eqA'[] ρ x A))) (congTmΓ (cong[] refl {A'} refl refl (⌞↑R⌟ ρ A)))) ⌞ there x ⌟V
      ≡⟨ conv-unique (trans (sym (congTmΓ (↑RTy.eqA'[] ρ x A))) (congTmΓ (cong[] refl {A'} refl refl (⌞↑R⌟ ρ A))))
                        (congTmΓ (sym ([∘] A' ⌞ ρ ⌟R (π₁ idS))))
                        ⌞ there x ⌟V ⟩
        conv (congTmΓ (Eq.sym ([∘] A' ⌞ ρ ⌟R (π₁ idS)))) (⌞ x ⌟V [ π₁ idS ])
      ∎

idR : Ren Δ Δ
⌞idR⌟ : ⌞ idR {Δ} ⌟R ≡ idS
⌞idR↑⌟ : (A : Ty Γ) → ⌞ idR ↑R A ⌟R ≡ π₁ idS
idR {∅} = ∅
idR {Δ , A} = (idR ↑R A) , conv (cong (Var (Δ , A)) (sym eq)) here
  module idRTy where
    eq : A [ ⌞ idR ↑R A ⌟R ] Eq.≡ A [ π₁ idS ]
    eq = congA[] (⌞idR↑⌟ A)
⌞idR⌟ {∅} = sym η∅
⌞idR⌟ {Δ , A} = begin
    ⌞ idR ↑R A , conv (cong (Var (Δ , A)) (sym (idRTy.eq Δ A))) here ⌟R
  ≡⟨⟩
    ⌞ idR ↑R A ⌟R , ⌞ conv (cong (Var (Δ , A)) (sym (idRTy.eq Δ A))) here ⌟V
  ≡⟨ cong,Sub' {A = A} refl (⌞idR↑⌟ A) eq,r ⟩
    π₁ idS , π₂ idS
  ≡⟨ sym ηπ ⟩
    idS
  ∎
  where
    eq' : A [ ⌞ idR ⌟R ∘ π₁ {A = A} idS ] ≡ A [ π₁ idS ]
    eq' = begin
        A [ ⌞ idR ⌟R ∘ π₁ idS ]
      ≡⟨ congA[] (cong∘' ⌞idR⌟ refl) ⟩
        A [ idS ∘ π₁ idS ]
      ≡⟨ [∘] A idS (π₁ idS) ⟩
        A [ idS ] [ π₁ idS ]
      ≡⟨ cong[] refl ([idS] A) refl refl ⟩
        A [ π₁ idS ]
      ∎
    eq,r : conv (congTmΓ (congA[] (⌞idR↑⌟ A))) (⌞ conv (cong (Var (Δ , A)) (sym (idRTy.eq Δ A))) here ⌟V) 
         ≡ π₂ {A = A} idS
    eq,r = begin
        conv (congTmΓ (congA[] (⌞idR↑⌟ A))) ⌞ conv (cong (Var (Δ , A)) (sym (idRTy.eq Δ A))) here ⌟V
      ≡⟨ cong (conv (congTmΓ (congA[] (⌞idR↑⌟ A)))) 
              (conv-in-func {Y = Var (Δ , A)} (sym (idRTy.eq Δ A)) ⌞_⌟V
                              (cong (Var (Δ , A)) (sym (idRTy.eq Δ A)))
                               here
                              (congTmΓ (sym (idRTy.eq Δ A)))) ⟩
        conv (congTmΓ (congA[] (⌞idR↑⌟ A))) (conv (congTmΓ (sym (idRTy.eq Δ A))) (π₂ idS))
      ≡⟨ conv² (congTmΓ (sym (idRTy.eq Δ A)))
               (congTmΓ (congA[] (⌞idR↑⌟ A))) ⟩
        conv (trans (congTmΓ (sym (idRTy.eq Δ A))) (congTmΓ (congA[] (⌞idR↑⌟ A)))) (π₂ idS)
      ≡⟨ conv-unique (trans (congTmΓ (sym (idRTy.eq Δ A))) (congTmΓ (congA[] (⌞idR↑⌟ A))))
                      refl
                     (π₂ idS) ⟩
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

lookupVar : (ρ : Ren Δ Γ) → Var Γ A → Var Δ (A [ ⌞ ρ ⌟R ])
lookupVar {Δ} {Γ , _} (_,_ ρ x) here = conv (cong (Var Δ) (sym eq)) x
  module lkVarEq where
    eq : {A A' : Ty Γ}{x : Var Δ (A' [ ⌞ ρ ⌟R ])} → A [ π₁ idS ] [ ⌞ ρ ⌟R , ⌞ x ⌟V ] ≡ A [ ⌞ ρ ⌟R ]
    eq {A = A} {x = x} = begin
        A [ π₁ idS ] [ ⌞ ρ ⌟R , ⌞ x ⌟V ]
      ≡⟨ sym ([∘] A (π₁ idS) (⌞ ρ ⌟R , ⌞ x ⌟V)) ⟩
        A [ π₁ idS ∘ (⌞ ρ ⌟R , ⌞ x ⌟V) ]
      ≡⟨ congA[] (π₁idS∘ (⌞ ρ ⌟R , ⌞ x ⌟V)) ⟩
        A [ π₁ (⌞ ρ ⌟R , ⌞ x ⌟V) ]
      ≡⟨ congA[] βπ₁ ⟩
        A [ ⌞ ρ ⌟R ]
      ∎
lookupVar {Δ} {Γ , _} (_,_ {A = A} ρ x') (there {A = A'} x) = conv (cong (Var Δ) (sym (lkVarEq.eq Γ A ρ x'))) (lookupVar ρ x)

-- Several lemmas
⌞lookup⌟ : (ρ : Ren Δ Γ)(x : Var Γ A) → ⌞ lookupVar ρ x ⌟V ≡ ⌞ x ⌟V [ ⌞ ρ ⌟R ]
⌞lookup⌟ {Δ} {Γ , A} (ρ , x) here = begin
    ⌞ conv (cong (Var Δ) (sym (lkVarEq.eq Γ A ρ x))) x ⌟V
  ≡⟨ conv-in-func {Y = Var Δ} (sym (lkVarEq.eq Γ A ρ x)) ⌞_⌟V
                      (cong (Var Δ) (sym (lkVarEq.eq Γ A ρ x)))
                       x
                      (congTmΓ (sym (lkVarEq.eq Γ A ρ x))) ⟩
    conv (congTmΓ (sym (lkVarEq.eq Γ A ρ x))) ⌞ x ⌟V
  ≡⟨ cong (conv (congTmΓ (sym (lkVarEq.eq Γ A ρ x)))) (sym (βπ₂ {σ = ⌞ ρ ⌟R} {t = ⌞ x ⌟V})) ⟩
    conv (congTmΓ (sym (lkVarEq.eq Γ A ρ x))) (conv (congTmΓ (congA[] βπ₁)) (π₂ (⌞ ρ ⌟R , ⌞ x ⌟V)))
  ≡⟨ cong (conv (congTmΓ (sym (lkVarEq.eq Γ A ρ x)))) 
          (conv-unique (congTmΓ (congA[] βπ₁)) (cong (λ σ → Tm Δ (A [ σ ])) βπ₁) (π₂ (⌞ ρ ⌟R , ⌞ x ⌟V))) ⟩
    conv (congTmΓ (sym (lkVarEq.eq Γ A ρ x)))
         (conv (cong (λ σ → Tm Δ (A [ σ ])) {!   !}) 
               (π₂ (⌞ ρ ⌟R , ⌞ x ⌟V)))
  ≡⟨ {!   !} ⟩
    {!   !}
⌞lookup⌟ ρ (there x) = {!   !}
-- ⌞lookup⌟ (_,_ {A = U} ρ x) here = begin
--     ⌞ x ⌟V
--   ≡⟨ sym (βπ₂ {σ = ⌞ ρ ⌟R} {⌞ x ⌟V}) ⟩
--     π₂ (⌞ ρ ⌟R , ⌞ x ⌟V)
--   ≡⟨ cong π₂ (sym (idS∘ (⌞ ρ ⌟R , ⌞ x ⌟V))) ⟩
--     π₂ (idS ∘ (⌞ ρ ⌟R , ⌞ x ⌟V))
--   ≡⟨ π₂∘ idS (⌞ ρ ⌟R , ⌞ x ⌟V) ⟩
--     π₂ idS [ ⌞ ρ ⌟R , ⌞ x ⌟V ]tm
--   ≡⟨⟩
--     ⌞ here ⌟V [ ⌞ ρ ⌟R , ⌞ x ⌟V ]tm
--   ∎
-- ⌞lookup⌟ (_,_ {A = U} ρ x') (there {A = U} x) = begin
--     ⌞ lookupVar ρ x ⌟V
--   ≡⟨ ⌞lookup⌟ ρ x ⟩
--     ⌞ x ⌟V [ ⌞ ρ ⌟R ]tm
--   ≡⟨ cong (⌞ x ⌟V [_]tm) (sym (βπ₁ {σ = ⌞ ρ ⌟R} {⌞ x' ⌟V})) ⟩
--     ⌞ x ⌟V [ π₁ (⌞ ρ ⌟R , ⌞ x' ⌟V) ]tm
--   ≡⟨ cong (⌞ x ⌟V [_]tm) (cong π₁ (sym (idS∘ (⌞ ρ ⌟R , ⌞ x' ⌟V)))) ⟩
--     ⌞ x ⌟V [ π₁ (idS ∘ (⌞ ρ ⌟R , ⌞ x' ⌟V)) ]tm
--   ≡⟨ cong (⌞ x ⌟V [_]tm) (π₁∘ idS (⌞ ρ ⌟R , ⌞ x' ⌟V)) ⟩
--     ⌞ x ⌟V [ π₁ idS ∘ (⌞ ρ ⌟R , ⌞ x' ⌟V) ]tm
--   ≡⟨ [∘]tm ⌞ x ⌟V (π₁ idS) (⌞ ρ ⌟R , ⌞ x' ⌟V) ⟩ -- would be "refl" using recursion _[_]t
--     ⌞ x ⌟V [ π₁ idS ]tm [ ⌞ ρ ⌟R , ⌞ x' ⌟V ]tm
--   ≡⟨⟩
--     ⌞ there x ⌟V [ ⌞ ρ ⌟R , ⌞ x' ⌟V ]tm
--   ∎



-- -- Composition of renamings
-- _⊙_ : Ren Δ Γ → Ren Θ Δ → Ren Θ Γ
-- ∅ ⊙ _ = ∅
-- _,_ {A = U} ρ x ⊙ ρ' = (ρ ⊙ ρ') , lookupVar ρ' x

-- ⌞⊙⌟ : (ρ : Ren Δ Γ)(ρ' : Ren Θ Δ) → ⌞ ρ ⊙ ρ' ⌟R ≡ ⌞ ρ ⌟R ∘ ⌞ ρ' ⌟R
-- ⌞⊙⌟ ∅ ρ' = sym η∅
-- ⌞⊙⌟ (_,_ {A = U} ρ x) ρ' = begin 
--     ⌞ ρ ⊙ ρ' ⌟R , ⌞ lookupVar ρ' x ⌟V
--   ≡⟨ cong (_, ⌞ lookupVar ρ' x ⌟V) (⌞⊙⌟ ρ ρ') ⟩
--     (⌞ ρ ⌟R ∘ ⌞ ρ' ⌟R) , ⌞ lookupVar ρ' x ⌟V
--   ≡⟨ cong ((⌞ ρ ⌟R ∘ ⌞ ρ' ⌟R) ,_) (⌞lookup⌟ ρ' x) ⟩ 
--     (⌞ ρ ⌟R ∘ ⌞ ρ' ⌟R) , ⌞ x ⌟V [ ⌞ ρ' ⌟R ]tm
--   ≡⟨ sym (,∘ {A = U} {⌞ ρ ⌟R} {⌞ x ⌟V} {⌞ ρ' ⌟R}) ⟩
--     (⌞ ρ ⌟R , ⌞ x ⌟V) ∘ ⌞ ρ' ⌟R
--   ∎

-- -- Reification of terms and substitutions into variables and renamings
-- ---- This is feasible because the only type is U for now
-- reifyTm : Tm Γ A → Var Γ A
-- reifySub : Sub Δ Γ → Ren Δ Γ
-- reifyTm (π₂ {A = U} σ) with reifySub σ
-- ... | ρ , x = x
-- reifyTm (t [ σ ]tm) with reifyTm t | reifySub σ
-- ... | here  {A = U}   | ρ , x  = x
-- ... | there {A = U} x | ρ , x' = lookupVar ρ x
-- reifySub ∅ = ∅ 
-- reifySub (σ , t) = reifySub σ , reifyTm t
-- reifySub idS = idR
-- reifySub (σ ∘ τ) = reifySub σ ⊙ reifySub τ
-- reifySub (π₁ σ) with reifySub σ
-- ... | ρ , _ = ρ

-- soundnessTm : (t : Tm Γ A) → ⌞ reifyTm t ⌟V ≡ t
-- soundnessSub : (σ : Sub Δ Γ) → ⌞ reifySub σ ⌟R ≡ σ
-- soundnessTm (π₂ {A = U} (σ , t)) with soundnessSub (σ , t)
-- ... | eq = begin
--     ⌞ reifyTm t ⌟V
--   ≡⟨ sym (βπ₂ {σ = ⌞ reifySub σ ⌟R} {⌞ reifyTm t ⌟V}) ⟩
--     π₂ (⌞ reifySub σ ⌟R , ⌞ reifyTm t ⌟V)
--   ≡⟨ cong π₂ eq ⟩
--     π₂ (σ , t)
--   ∎
-- soundnessTm (π₂ {A = U} idS) = refl
-- soundnessTm (π₂ {Δ} {A = U} (σ ∘ τ)) with reifySub σ | soundnessSub σ
-- ... | ρ , x | ⌞ρ⌟,⌞x⌟≡σ with soundnessSub τ
-- ... | eq = begin
--     ⌞ lookupVar (reifySub τ) x ⌟V
--   ≡⟨ ⌞lookup⌟ (reifySub τ) x ⟩
--     ⌞ x ⌟V [ ⌞ reifySub τ ⌟R ]tm
--   ≡⟨ cong (⌞ x ⌟V [_]tm) eq ⟩
--     ⌞ x ⌟V [ τ ]tm
--   ≡⟨ cong (_[ τ ]tm) (sym (βπ₂ {σ = ⌞ ρ ⌟R} {⌞ x ⌟V})) ⟩
--     π₂ (⌞ ρ ⌟R , ⌞ x ⌟V) [ τ ]tm
--   ≡⟨ cong (λ y → π₂ y [ τ ]tm) ⌞ρ⌟,⌞x⌟≡σ ⟩
--     π₂ σ [ τ ]tm
--   ≡⟨ sym (π₂∘ σ τ) ⟩
--     π₂ (σ ∘ τ)
--   ∎
-- soundnessTm (π₂ {Δ} {A = U} (π₁ σ)) with reifySub σ | soundnessSub σ
-- ... | (ρ , x) , x' | eq = begin
--     ⌞ x ⌟V
--   ≡⟨ sym (βπ₂ {σ = ⌞ ρ ⌟R} {⌞ x ⌟V}) ⟩
--     π₂ (⌞ ρ ⌟R , ⌞ x ⌟V)
--   ≡⟨ cong π₂ (sym (βπ₁ {σ = ⌞ ρ ⌟R , ⌞ x ⌟V} {⌞ x' ⌟V})) ⟩
--     π₂ (π₁ ((⌞ ρ ⌟R , ⌞ x ⌟V) , ⌞ x' ⌟V))
--   ≡⟨ cong (λ y → π₂ (π₁ y)) eq ⟩
--     π₂ (π₁ σ)
--   ∎
-- soundnessTm (t [ σ ]tm) with reifyTm t | reifySub σ | soundnessTm t | soundnessSub σ
-- ... | here {A = U} | ρ , x | eqTm | eqSub = begin
--     ⌞ x ⌟V
--   ≡⟨ sym (βπ₂ {σ = ⌞ ρ ⌟R} {⌞ x ⌟V}) ⟩
--     π₂ (⌞ ρ ⌟R , ⌞ x ⌟V)
--   ≡⟨ cong π₂ eqSub ⟩
--     π₂ σ
--   ≡⟨ cong π₂ (sym (idS∘ σ)) ⟩
--     π₂ (idS ∘ σ)
--   ≡⟨ π₂∘ idS σ ⟩
--     π₂ idS [ σ ]tm
--   ≡⟨ cong (_[ σ ]tm) eqTm ⟩
--     t [ σ ]tm
--   ∎
-- ... | there {A = U} x | ρ , x' | eqTm | eqSub = begin
--     ⌞ lookupVar ρ x ⌟V
--   ≡⟨ ⌞lookup⌟ ρ x ⟩
--     ⌞ x ⌟V [ ⌞ ρ ⌟R ]tm
--   ≡⟨ cong (⌞ x ⌟V [_]tm) (sym (βπ₁ {σ = ⌞ ρ ⌟R} {⌞ x' ⌟V})) ⟩
--     ⌞ x ⌟V [ π₁ (⌞ ρ ⌟R , ⌞ x' ⌟V) ]tm
--   ≡⟨ cong (λ y → ⌞ x ⌟V [ π₁ y ]tm) eqSub ⟩
--     ⌞ x ⌟V [ π₁ σ ]tm
--   ≡⟨ cong (⌞ x ⌟V [_]tm) (sym (π₁idS∘ σ)) ⟩ -- would be "cong (⌞ x ⌟V [_]t) (sym (π₁idS∘ σ))" using recursion _[_]t
--     ⌞ x ⌟V [ π₁ idS ∘ σ ]tm
--   ≡⟨ [∘]tm ⌞ x ⌟V (π₁ idS) σ ⟩ -- would be "refl" using recursion _[_]t
--     ⌞ x ⌟V [ π₁ idS ]tm [ σ ]tm
--   ≡⟨ cong (_[ σ ]tm) eqTm ⟩
--     t [ σ ]tm
--   ∎
-- soundnessSub ∅ = refl
-- soundnessSub (σ , t) = begin
--     ⌞ reifySub σ ⌟R , ⌞ reifyTm t ⌟V
--   ≡⟨ cong (⌞ reifySub σ ⌟R ,_) (soundnessTm t) ⟩
--     ⌞ reifySub σ ⌟R , t
--   ≡⟨ cong (_, t) (soundnessSub σ) ⟩
--     σ , t
--   ∎
-- soundnessSub idS = ⌞idR⌟
-- soundnessSub (σ ∘ τ) = begin
--     ⌞ reifySub σ ⊙ reifySub τ ⌟R
--   ≡⟨ ⌞⊙⌟ (reifySub σ) (reifySub τ) ⟩
--     ⌞ reifySub σ ⌟R ∘ ⌞ reifySub τ ⌟R
--   ≡⟨ cong (_∘ ⌞ reifySub τ ⌟R) (soundnessSub σ) ⟩
--     σ ∘ ⌞ reifySub τ ⌟R
--   ≡⟨ cong (σ ∘_) (soundnessSub τ) ⟩
--     σ ∘ τ
--   ∎
-- soundnessSub (π₁ σ) with reifySub σ | soundnessSub σ
-- ... | ρ , x | eq = begin
--     ⌞ ρ ⌟R
--   ≡⟨ sym (βπ₁ {σ = ⌞ ρ ⌟R} {⌞ x ⌟V}) ⟩
--     π₁ (⌞ ρ ⌟R , ⌞ x ⌟V)
--   ≡⟨ cong π₁ eq ⟩
--     π₁ σ
--   ∎

-- -- Inductive definition of the normal form
-- data NeSub (Δ : Ctx) : (Γ : Ctx) → Sub Δ Γ → Set where
--   idS : NeSub Δ Δ idS
--   π₁  : NeSub Δ (Γ , A) σ → NeSub Δ Γ (π₁ σ)

-- data NfTm (Δ : Ctx) : Tm Δ A → Set where
--   π₂ : NeSub Δ (Γ , A) σ → NfTm Δ {A [ π₁ σ ]} (π₂ σ)

-- test : vs {B = B'} (vs {B = B} (vz {Γ} {U})) ≡ π₂ (π₁ (π₁ idS)) -- π₂ (π₁ (π₁ idS))
-- test {Γ} {B} {B'} =
--   begin
--     π₂ idS [ π₁ idS ]tm [ π₁ idS ]tm
--   ≡⟨ cong (_[ π₁ idS ]tm) (sym (π₂∘ idS (π₁ idS))) ⟩
--     π₂ (idS ∘ π₁ idS) [ π₁ idS ]tm
--   ≡⟨ cong (_[ π₁ idS ]tm) (cong π₂ (idS∘ (π₁ idS))) ⟩
--     π₂ (π₁ idS) [ π₁ idS ]tm
--   ≡⟨ sym (π₂∘ (π₁ idS) (π₁ idS)) ⟩
--     π₂ (π₁ idS ∘ π₁ idS)
--   ≡⟨ cong π₂ (sym (π₁∘ idS (π₁ idS))) ⟩
--     π₂ (π₁ (idS ∘ π₁ idS))
--   ≡⟨ cong (λ y → π₂ (π₁ y)) (idS∘ (π₁ idS)) ⟩
--     π₂ (π₁ (π₁ idS))
--   ∎

-- reflectVar : (x : Var Γ A) → Σ[ B ∈ Ty Γ ] Σ[ t ∈ Tm Γ B ] Σ[ p ∈ A ≡ B ] tr (Tm Γ) p ⌞ x ⌟V ≡ t × NfTm Γ t
-- reflectVar {Γ , U} here = U , π₂ idS , refl , refl , π₂ idS
-- reflectVar {Γ , U} (there x) with reflectVar x 
-- ... | B , .(π₂ σ) , refl , ⌞x⌟≡t , π₂ {A = U} {σ} nσ = U , π₂ {Γ , U} {! π₁ σ  !} , {!   !}  