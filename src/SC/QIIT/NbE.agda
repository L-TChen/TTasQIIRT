module SC.QIIT.NbE where

open import Prelude
open import Data.Product
open import SC.QIIT.Base
open Eq.≡-Reasoning
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
  ≡⟨ conv² (congTmΓ (congA[] βπ₁)) (congTmΓ (sym (lkVarEq.eq Γ A ρ x))) ⟩
    conv (trans (congTmΓ (congA[] βπ₁)) (congTmΓ (Eq.sym (lkVarEq.eq Γ A ρ x)))) (π₂ (⌞ ρ ⌟R , ⌞ x ⌟V))
  ≡⟨ conv-unique (trans (congTmΓ (congA[] βπ₁)) (congTmΓ (Eq.sym (lkVarEq.eq Γ A ρ x))))
                 (congTmΓ eqA[])
                 (π₂ (⌞ ρ ⌟R , ⌞ x ⌟V)) ⟩
    conv (congTmΓ eqA[]) (π₂ (⌞ ρ ⌟R , ⌞ x ⌟V))
  ≡⟨ eq ⟩
    π₂ idS [ ⌞ ρ ⌟R , ⌞ x ⌟V ]
  ∎
  module ⌞lookup⌟Eq where
    eqA[] : {A : Ty Γ} → A [ π₁ (⌞ ρ ⌟R , ⌞ x ⌟V) ] ≡ A [ π₁ idS ] [ ⌞ ρ ⌟R , ⌞ x ⌟V ]
    eqA[] {A = A} = begin
        A [ π₁ (⌞ ρ ⌟R , ⌞ x ⌟V) ]
      ≡⟨ congA[] (sym (π₁idS∘ (⌞ ρ ⌟R , ⌞ x ⌟V))) ⟩
        A [ π₁ idS ∘ (⌞ ρ ⌟R , ⌞ x ⌟V) ]
      ≡⟨ [∘] A (π₁ idS) (⌞ ρ ⌟R , ⌞ x ⌟V) ⟩
        A [ π₁ idS ] [ ⌞ ρ ⌟R , ⌞ x ⌟V ]
      ∎
    eq : conv (congTmΓ eqA[]) (π₂ (⌞ ρ ⌟R , ⌞ x ⌟V)) ≡ π₂ idS [ ⌞ ρ ⌟R , ⌞ x ⌟V ]
    eq = begin
        conv (congTmΓ eqA[]) (π₂ (⌞ ρ ⌟R , ⌞ x ⌟V))
      ≡⟨ cong (conv (congTmΓ eqA[])) (sym (apd' π₂ (idS∘ (⌞ ρ ⌟R , ⌞ x ⌟V)))) ⟩
        conv (congTmΓ eqA[]) (conv (cong (λ z → Tm Δ (A [ π₁ z ])) (idS∘ (⌞ ρ ⌟R , ⌞ x ⌟V))) (π₂ (idS ∘ (⌞ ρ ⌟R , ⌞ x ⌟V))))
      ≡⟨ conv² (cong (λ z → Tm Δ (A [ π₁ z ])) (idS∘ (⌞ ρ ⌟R , ⌞ x ⌟V))) (congTmΓ eqA[]) ⟩
        conv (trans (cong (λ z → Tm Δ (A [ π₁ z ])) (idS∘ (⌞ ρ ⌟R , ⌞ x ⌟V))) (congTmΓ eqA[])) (π₂ (idS ∘ (⌞ ρ ⌟R , ⌞ x ⌟V)))
      ≡⟨ conv-unique (trans (cong (λ z → Tm Δ (A [ π₁ z ])) (idS∘ (⌞ ρ ⌟R , ⌞ x ⌟V))) (congTmΓ eqA[]))
                        (congTmΓ (trans (congA[] (π₁∘ idS (⌞ ρ ⌟R , ⌞ x ⌟V))) ([∘] A (π₁ idS) (⌞ ρ ⌟R , ⌞ x ⌟V))))
                        (π₂ (idS ∘ (⌞ ρ ⌟R , ⌞ x ⌟V))) ⟩
        conv (congTmΓ (trans (congA[] (π₁∘ idS (⌞ ρ ⌟R , ⌞ x ⌟V))) ([∘] A (π₁ idS) (⌞ ρ ⌟R , ⌞ x ⌟V))))
                 (π₂ (idS ∘ (⌞ ρ ⌟R , ⌞ x ⌟V)))
      ≡⟨ π₂∘ idS (⌞ ρ ⌟R , ⌞ x ⌟V) ⟩
        π₂ idS [ ⌞ ρ ⌟R , ⌞ x ⌟V ]
      ∎
⌞lookup⌟ {Δ} {Γ , A'} (ρ , x') (there {A = A} x) = begin
    ⌞ conv (cong (Var Δ) (sym (lkVarEq.eq Γ A' ρ x'))) (lookupVar ρ x) ⌟V
  ≡⟨ conv-in-func {Y = Var Δ} (sym (lkVarEq.eq Γ A' ρ x')) 
                               ⌞_⌟V
                              (cong (Var Δ) (sym (lkVarEq.eq Γ A' ρ x')))
                              (lookupVar ρ x) 
                              (congTmΓ (sym (lkVarEq.eq Γ A' ρ x'))) ⟩
    conv (congTmΓ (sym (lkVarEq.eq Γ A' ρ x'))) ⌞ lookupVar ρ x ⌟V
  ≡⟨ cong (conv (congTmΓ (sym (lkVarEq.eq Γ A' ρ x')))) (⌞lookup⌟ ρ x) ⟩
    conv (congTmΓ (sym (lkVarEq.eq Γ A' ρ x'))) (⌞ x ⌟V [ ⌞ ρ ⌟R ])
  ≡⟨ conv-unique (congTmΓ (sym (lkVarEq.eq Γ A' ρ x')))
                 (trans (congTmΓ (congA[] (Eq.sym βπ₁))) (congTmΓ (⌞lookup⌟Eq.eqA[] Γ A' ρ x')))
                 (⌞ x ⌟V [ ⌞ ρ ⌟R ]) ⟩
    conv (trans (congTmΓ (congA[] (Eq.sym βπ₁))) (congTmΓ (⌞lookup⌟Eq.eqA[] Γ A' ρ x'))) (⌞ x ⌟V [ ⌞ ρ ⌟R ])
  ≡⟨ sym (conv² (congTmΓ (congA[] (sym βπ₁))) (congTmΓ (⌞lookup⌟Eq.eqA[] Γ A' ρ x'))) ⟩
    conv (congTmΓ (⌞lookup⌟Eq.eqA[] Γ A' ρ x')) (conv (congTmΓ (congA[] (sym βπ₁))) (⌞ x ⌟V [ ⌞ ρ ⌟R ]))
  ≡⟨ cong (conv (congTmΓ (⌞lookup⌟Eq.eqA[] Γ A' ρ x'))) 
          (cong[]tm refl {A} refl {⌞ x ⌟V} refl refl (sym (βπ₁ {σ = ⌞ ρ ⌟R} {t = ⌞ x' ⌟V}))) ⟩
    conv (congTmΓ (⌞lookup⌟Eq.eqA[] Γ A' ρ x')) (⌞ x ⌟V [ π₁ (⌞ ρ ⌟R , ⌞ x' ⌟V) ])
  ≡⟨ conv-unique (congTmΓ (⌞lookup⌟Eq.eqA[] Γ A' ρ x'))
                 (trans (congTmΓ (congA[] (cong π₁ (sym (idS∘ (⌞ ρ ⌟R , ⌞ x' ⌟V)))))) (congTmΓ eqTy))
                 (⌞ x ⌟V [ π₁ (⌞ ρ ⌟R , ⌞ x' ⌟V) ]) ⟩
    conv (trans (congTmΓ (congA[] (cong π₁ (sym (idS∘ (⌞ ρ ⌟R , ⌞ x' ⌟V)))))) (congTmΓ eqTy))
         (⌞ x ⌟V [ π₁ (⌞ ρ ⌟R , ⌞ x' ⌟V) ])
  ≡⟨ sym (conv² (congTmΓ (congA[] (cong π₁ (sym (idS∘ (⌞ ρ ⌟R , ⌞ x' ⌟V)))))) (congTmΓ eqTy)) ⟩
    conv (congTmΓ eqTy) (conv (congTmΓ (congA[] (cong π₁ (sym (idS∘ (⌞ ρ ⌟R , ⌞ x' ⌟V)))))) (⌞ x ⌟V [ π₁ (⌞ ρ ⌟R , ⌞ x' ⌟V) ]))
  ≡⟨ cong (conv (congTmΓ eqTy)) (cong[]tm refl {A} refl {⌞ x ⌟V} refl refl (cong π₁ (sym (idS∘ (⌞ ρ ⌟R , ⌞ x' ⌟V))))) ⟩
    conv (congTmΓ eqTy) (⌞ x ⌟V [ π₁ (idS ∘ (⌞ ρ ⌟R , ⌞ x' ⌟V)) ])
  ≡⟨ conv-unique (congTmΓ eqTy) (trans (congTmΓ (congA[] (π₁∘ idS (⌞ ρ ⌟R , ⌞ x' ⌟V)))) (congTmΓ ([∘] A (π₁ idS) (⌞ ρ ⌟R , ⌞ x' ⌟V))))
                 (⌞ x ⌟V [ π₁ (idS ∘ (⌞ ρ ⌟R , ⌞ x' ⌟V)) ]) ⟩
    conv (trans (congTmΓ (congA[] (π₁∘ idS (⌞ ρ ⌟R , ⌞ x' ⌟V)))) (congTmΓ ([∘] A (π₁ idS) (⌞ ρ ⌟R , ⌞ x' ⌟V))))
         (⌞ x ⌟V [ π₁ (idS ∘ (⌞ ρ ⌟R , ⌞ x' ⌟V)) ])
  ≡⟨ sym (conv² (congTmΓ (congA[] (π₁∘ idS (⌞ ρ ⌟R , ⌞ x' ⌟V)))) (congTmΓ ([∘] A (π₁ idS) (⌞ ρ ⌟R , ⌞ x' ⌟V)))) ⟩
    conv (congTmΓ ([∘] A (π₁ idS) (⌞ ρ ⌟R , ⌞ x' ⌟V))) 
         (conv (congTmΓ (congA[] (π₁∘ idS (⌞ ρ ⌟R , ⌞ x' ⌟V))))
               (⌞ x ⌟V [ π₁ (idS ∘ (⌞ ρ ⌟R , ⌞ x' ⌟V)) ]))
  ≡⟨ cong (conv (congTmΓ ([∘] A (π₁ idS) (⌞ ρ ⌟R , ⌞ x' ⌟V))))
          (cong[]tm refl {A} refl {⌞ x ⌟V} refl refl (π₁∘ idS (⌞ ρ ⌟R , ⌞ x' ⌟V))) ⟩
    conv (congTmΓ ([∘] A (π₁ idS) (⌞ ρ ⌟R , ⌞ x' ⌟V))) (⌞ x ⌟V [ π₁ idS ∘ (⌞ ρ ⌟R , ⌞ x' ⌟V) ])
  ≡⟨ [∘]tm ⌞ x ⌟V (π₁ idS) (⌞ ρ ⌟R , ⌞ x' ⌟V) ⟩
    ⌞ x ⌟V [ π₁ idS ] [ ⌞ ρ ⌟R , ⌞ x' ⌟V ]
  ≡⟨⟩
    ⌞ there x ⌟V [ ⌞ ρ ⌟R , ⌞ x' ⌟V ]
  ∎
  where
    eqTy : A [ π₁ (idS ∘ (⌞ ρ ⌟R , ⌞ x' ⌟V)) ] ≡ A [ π₁ idS ] [ ⌞ ρ ⌟R , ⌞ x' ⌟V ]
    eqTy = begin
        A [ π₁ (idS ∘ (⌞ ρ ⌟R , ⌞ x' ⌟V)) ]
      ≡⟨ congA[] (π₁∘ idS (⌞ ρ ⌟R , ⌞ x' ⌟V)) ⟩
        A [ π₁ idS ∘ (⌞ ρ ⌟R , ⌞ x' ⌟V) ]
      ≡⟨ [∘] A (π₁ idS) (⌞ ρ ⌟R , ⌞ x' ⌟V) ⟩
        A [ π₁ idS ] [ ⌞ ρ ⌟R , ⌞ x' ⌟V ]
      ∎

-- Composition of renamings
_⊙_ : Ren Δ Γ → Ren Θ Δ → Ren Θ Γ
⌞⊙⌟ : (ρ : Ren Δ Γ)(ρ' : Ren Θ Δ) → ⌞ ρ ⊙ ρ' ⌟R ≡ ⌞ ρ ⌟R ∘ ⌞ ρ' ⌟R
∅ ⊙ _ = ∅
_⊙_ {Θ = Θ} (ρ , x) ρ' = (ρ ⊙ ρ') , conv (cong (Var Θ) (sym eqA[])) (lookupVar ρ' x)
  module ⊙Eq where
    eqA[] : A [ ⌞ ρ ⊙ ρ' ⌟R ] ≡ A [ ⌞ ρ ⌟R ] [ ⌞ ρ' ⌟R ]
    eqA[] {A = A} = begin
        A [ ⌞ ρ ⊙ ρ' ⌟R ]
      ≡⟨ congA[] (⌞⊙⌟ ρ ρ') ⟩
        A [ ⌞ ρ ⌟R ∘ ⌞ ρ' ⌟R ]
      ≡⟨ [∘] A ⌞ ρ ⌟R ⌞ ρ' ⌟R ⟩
        A [ ⌞ ρ ⌟R ] [ ⌞ ρ' ⌟R ]
      ∎
⌞⊙⌟ ∅ ρ' = sym η∅
⌞⊙⌟ {Δ} {Γ , A} {Θ} (ρ , x) ρ' = begin
    ⌞ ρ ⊙ ρ' ⌟R , ⌞ conv (cong (Var Θ) (sym (⊙Eq.eqA[] ρ x ρ'))) (lookupVar ρ' x) ⌟V
  ≡⟨ cong,Sub' {A = A} refl (⌞⊙⌟ ρ ρ') eq,R ⟩
    ⌞ ρ ⌟R ∘ ⌞ ρ' ⌟R , conv (congTmΓ (sym ([∘] A ⌞ ρ ⌟R ⌞ ρ' ⌟R))) (⌞ x ⌟V [ ⌞ ρ' ⌟R ])
  ≡⟨ sym (,∘ {σ = ⌞ ρ ⌟R} {t = ⌞ x ⌟V} {τ = ⌞ ρ' ⌟R}) ⟩
    (⌞ ρ ⌟R , ⌞ x ⌟V) ∘ ⌞ ρ' ⌟R
  ∎
  where
    eq,R : conv (congTmΓ (congA[] (⌞⊙⌟ ρ ρ'))) ⌞ conv (cong (Var Θ) (sym (⊙Eq.eqA[] ρ x ρ'))) (lookupVar ρ' x) ⌟V
         ≡ conv (congTmΓ (sym ([∘] A ⌞ ρ ⌟R ⌞ ρ' ⌟R))) (⌞ x ⌟V [ ⌞ ρ' ⌟R ])
    eq,R = begin
        conv (congTmΓ (congA[] (⌞⊙⌟ ρ ρ'))) ⌞ conv (cong (Var Θ) (sym (⊙Eq.eqA[] ρ x ρ'))) (lookupVar ρ' x) ⌟V
      ≡⟨ cong (conv (congTmΓ (congA[] (⌞⊙⌟ ρ ρ'))))
              (conv-in-func {Y = Var Θ} (sym (⊙Eq.eqA[] ρ x ρ')) ⌞_⌟V 
                            (cong (Var Θ) (sym (⊙Eq.eqA[] ρ x ρ')))
                            (lookupVar ρ' x)
                            (congTmΓ (sym (⊙Eq.eqA[] ρ x ρ')))) ⟩
        conv (congTmΓ (congA[] (⌞⊙⌟ ρ ρ'))) (conv (congTmΓ (sym (⊙Eq.eqA[] ρ x ρ'))) ⌞ lookupVar ρ' x ⌟V)
      ≡⟨ conv² (congTmΓ (sym (⊙Eq.eqA[] ρ x ρ'))) (congTmΓ (congA[] (⌞⊙⌟ ρ ρ'))) ⟩
        conv (trans (congTmΓ (sym (⊙Eq.eqA[] ρ x ρ'))) (congTmΓ (congA[] (⌞⊙⌟ ρ ρ')))) ⌞ lookupVar ρ' x ⌟V
      ≡⟨ conv-unique (trans (congTmΓ (sym (⊙Eq.eqA[] ρ x ρ'))) (congTmΓ (congA[] (⌞⊙⌟ ρ ρ'))))
                     (congTmΓ (Eq.sym ([∘] A ⌞ ρ ⌟R ⌞ ρ' ⌟R)))
                     ⌞ lookupVar ρ' x ⌟V ⟩
        conv (congTmΓ (sym ([∘] A ⌞ ρ ⌟R ⌞ ρ' ⌟R))) ⌞ lookupVar ρ' x ⌟V
      ≡⟨ cong (conv (congTmΓ (sym ([∘] A ⌞ ρ ⌟R ⌞ ρ' ⌟R)))) (⌞lookup⌟ ρ' x) ⟩
        conv (congTmΓ (sym ([∘] A ⌞ ρ ⌟R ⌞ ρ' ⌟R))) (⌞ x ⌟V [ ⌞ ρ' ⌟R ])
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
Domain .IH.PidS {PΔ = Γ , refl} = idR , sym ⌞idR⌟
Domain .IH._∘P_ {PΓ = Γ , refl} {Δ , refl} {Θ , refl} (ρ , refl) (ρ' , refl) = ρ ⊙ ρ' , sym (⌞⊙⌟ ρ ρ')
Domain .IH.π₁P {PΔ = Δ , refl} {Γ , refl} {A , refl} ((ρ , x) , refl) = ρ , βπ₁
Domain .IH.PU {PΓ = Γ , refl} = U , refl
Domain .IH.π₂P {PΔ = Δ , refl} {Γ , refl} {A , refl} ((ρ , x) , refl) = x , βπ₂
IH._[_]tP Domain {PΓ = Γ , refl} {A , refl} {Δ , refl} (x , refl) (ρ , refl) = lookupVar ρ x , sym (⌞lookup⌟ ρ x)

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
accVar here σ = conv (congTmΓ (sym eqTy)) (π₂ σ) -- π₂ σ
  module accVarEq where
    eqTy : A [ π₁ idS ] [ σ ] ≡ A [ π₁ σ ]
    eqTy {A = A} = begin
        A [ π₁ idS ] [ σ ]
      ≡⟨ sym ([∘] A (π₁ idS) σ) ⟩
        A [ π₁ idS ∘ σ ]
      ≡⟨ congA[] (π₁idS∘ σ) ⟩
        A [ π₁ σ ]
      ∎
accVar (there x) σ = conv (congTmΓ (sym (accVarEq.eqTy σ))) (accVar x (π₁ σ))

accVar[]tm : (x : Var Γ A)(σ : Sub Δ Γ)(τ : Sub Θ Δ) → conv (congTmΓ (sym ([∘] A σ τ))) (accVar x σ [ τ ]) ≡ accVar x (σ ∘ τ)
accVar[]tm {Γ , A} {_} {Δ} {Θ} here σ τ = begin
    conv (congTmΓ (sym ([∘] (A [ π₁ idS ]) σ τ))) (conv (congTmΓ (sym (accVarEq.eqTy σ))) (π₂ σ) [ τ ])
  ≡⟨ cong (conv (congTmΓ (sym ([∘] (A [ π₁ idS ]) σ τ)))) 
          (conv-in-func {Y = Tm Δ} (sym (accVarEq.eqTy σ)) 
                        (_[ τ ])
                        (congTmΓ (sym (accVarEq.eqTy σ)))
                        (π₂ σ) (congTmΓ (cong (_[ τ ]) (sym (accVarEq.eqTy σ))))) ⟩
    conv (congTmΓ (sym ([∘] (A [ π₁ idS ]) σ τ)))
         (conv (congTmΓ (cong (_[ τ ]) (sym (accVarEq.eqTy σ))))
               (π₂ σ [ τ ]))
  ≡⟨ conv² (congTmΓ (cong (_[ τ ]) (sym (accVarEq.eqTy σ)))) (congTmΓ (sym ([∘] (A [ π₁ idS ]) σ τ))) ⟩
    conv (trans (congTmΓ (cong (_[ τ ]) (sym (accVarEq.eqTy σ)))) (congTmΓ (sym ([∘] (A [ π₁ idS ]) σ τ))))
         (π₂ σ [ τ ])
  ≡⟨ cong (conv (trans (congTmΓ (cong (_[ τ ]) (sym (accVarEq.eqTy σ)))) (congTmΓ (sym ([∘] (A [ π₁ idS ]) σ τ)))))
          (sym (π₂∘ σ τ)) ⟩
    conv  (trans (congTmΓ (cong (_[ τ ]) (sym (accVarEq.eqTy σ)))) (congTmΓ (sym ([∘] (A [ π₁ idS ]) σ τ))))
          (conv (congTmΓ (trans (congA[] (π₁∘ σ τ)) ([∘] A (π₁ σ) τ))) (π₂ (σ ∘ τ)))
  ≡⟨ conv² (congTmΓ (trans (congA[] (π₁∘ σ τ)) ([∘] A (π₁ σ) τ)))
           (trans (congTmΓ (cong (_[ τ ]) (sym (accVarEq.eqTy σ)))) (congTmΓ (sym ([∘] (A [ π₁ idS ]) σ τ)))) ⟩
    conv (trans (congTmΓ (trans (congA[] (π₁∘ σ τ)) ([∘] A (π₁ σ) τ)))
                (trans (congTmΓ (cong (_[ τ ]) (sym (accVarEq.eqTy σ))))
                       (congTmΓ (sym ([∘] (A [ π₁ idS ]) σ τ)))))
         (π₂ (σ ∘ τ))
  ≡⟨ conv-unique (trans (congTmΓ (trans (congA[] (π₁∘ σ τ)) ([∘] A (π₁ σ) τ)))
                        (trans (congTmΓ (cong (_[ τ ]) (sym (accVarEq.eqTy σ))))
                               (congTmΓ (sym ([∘] (A [ π₁ idS ]) σ τ)))))
                 (congTmΓ (sym (accVarEq.eqTy (σ ∘ τ))))
                 (π₂ (σ ∘ τ)) ⟩
    conv (congTmΓ (sym (accVarEq.eqTy (σ ∘ τ)))) (π₂ (σ ∘ τ))
  ∎
accVar[]tm {Γ , A'} {_} {Δ} {Θ} (there {A = A} x) σ τ = begin
    conv (congTmΓ (sym ([∘] (A [ π₁ idS ]) σ τ)))
         (conv (congTmΓ (sym (accVarEq.eqTy σ))) (accVar x (π₁ σ)) [ τ ])
  ≡⟨ cong (conv (congTmΓ (sym ([∘] (A [ π₁ idS ]) σ τ))))
          (conv-in-func {Y = Tm Δ}
                        (sym (accVarEq.eqTy σ))
                        (_[ τ ])
                        (congTmΓ (sym (accVarEq.eqTy σ))) (accVar x (π₁ σ))
                        (congTmΓ (cong (_[ τ ]) (sym (accVarEq.eqTy σ))))) ⟩
    conv (congTmΓ (sym ([∘] (A [ π₁ idS ]) σ τ)))
         (conv (congTmΓ (cong (_[ τ ]) (sym (accVarEq.eqTy σ))))
               (accVar x (π₁ σ) [ τ ]))
  ≡⟨ conv² (congTmΓ (cong (_[ τ ]) (sym (accVarEq.eqTy σ))))
           (congTmΓ (sym ([∘] (A [ π₁ idS ]) σ τ))) ⟩
    conv (trans (congTmΓ (cong (_[ τ ]) (sym (accVarEq.eqTy σ))))
                (congTmΓ (sym ([∘] (A [ π₁ idS ]) σ τ))))
         (accVar x (π₁ σ) [ τ ])
  ≡⟨ conv-unique (trans (congTmΓ (cong (_[ τ ]) (sym (accVarEq.eqTy σ))))
                           (congTmΓ (sym ([∘] (A [ π₁ idS ]) σ τ))))
                 (trans (congTmΓ (sym ([∘] A (π₁ σ) τ))) (congTmΓ eqTy))
                 (accVar x (π₁ σ) [ τ ]) ⟩
    conv (trans (congTmΓ (sym ([∘] A (π₁ σ) τ))) (congTmΓ eqTy)) (accVar x (π₁ σ) [ τ ])
  ≡⟨ sym (conv² (congTmΓ (sym ([∘] A (π₁ σ) τ))) (congTmΓ eqTy)) ⟩
    conv (congTmΓ eqTy) (conv (congTmΓ (sym ([∘] A (π₁ σ) τ))) (accVar x (π₁ σ) [ τ ]))
  ≡⟨ cong (conv (congTmΓ eqTy)) (accVar[]tm x (π₁ σ) τ) ⟩
    conv (congTmΓ eqTy) (accVar x (π₁ σ ∘ τ))
  ≡⟨ conv-unique (congTmΓ eqTy)
                 (trans (cong (λ z → Tm Θ (A [ z ])) (sym (π₁∘ σ τ)))
                        (congTmΓ (sym (accVarEq.eqTy (σ ∘ τ)))))
                 (accVar x (π₁ σ ∘ τ)) ⟩
    conv (trans (cong (λ z → Tm Θ (A [ z ])) (sym (π₁∘ σ τ)))
                (congTmΓ (sym (accVarEq.eqTy (σ ∘ τ)))))
         (accVar x (π₁ σ ∘ τ))
  ≡⟨ sym (conv² (cong (λ z → Tm Θ (A [ z ])) (sym (π₁∘ σ τ))) (congTmΓ (sym (accVarEq.eqTy (σ ∘ τ))))) ⟩
    conv (congTmΓ (sym (accVarEq.eqTy (σ ∘ τ))))
         (conv (cong (λ z → Tm Θ (A [ z ])) (sym (π₁∘ σ τ)))
               (accVar x (π₁ σ ∘ τ)))
  ≡⟨ cong (conv (congTmΓ (sym (accVarEq.eqTy (σ ∘ τ))))) (apd' (accVar x) (sym (π₁∘ σ τ))) ⟩
    conv (congTmΓ (sym (accVarEq.eqTy (σ ∘ τ)))) (accVar x (π₁ (σ ∘ τ)))
  ∎
  where
    eqTy : A [ π₁ σ ∘ τ ] ≡ A [ π₁ idS ] [ σ ∘ τ ]
    eqTy = begin
        A [ π₁ σ ∘ τ ]
      ≡⟨ congA[] (cong∘' (sym (π₁idS∘ σ)) refl) ⟩
        A [ (π₁ idS ∘ σ) ∘ τ ]
      ≡⟨ congA[] assocS ⟩
        A [ π₁ idS ∘ σ ∘ τ ]
      ≡⟨ [∘] A (π₁ idS) (σ ∘ τ) ⟩
        A [ π₁ idS ] [ σ ∘ τ ]
      ∎

nfVar : (x : Var Γ A) → Tm Γ A
nfVar x = conv (congTmΓ ([idS] _)) (accVar x idS)

soundnessNfVar : (x : Var Γ A) → ⌞ x ⌟V ≡ nfVar x
soundnessNfVar {Γ , A'} {A} here = sym (begin
    conv (congTmΓ ([idS] A)) (conv (congTmΓ (sym (accVarEq.eqTy idS))) (π₂ idS))
  ≡⟨ conv² (congTmΓ (sym (accVarEq.eqTy idS))) (congTmΓ ([idS] A)) ⟩
    conv (trans (congTmΓ (sym (accVarEq.eqTy idS))) (congTmΓ ([idS] (A' [ π₁ idS ])))) (π₂ idS)
  ≡⟨ conv-unique (trans (congTmΓ (sym (accVarEq.eqTy idS))) (congTmΓ ([idS] (A' [ π₁ idS ]))))
                  refl
                 (π₂ idS) ⟩
    π₂ idS
  ∎)
soundnessNfVar {Γ , B} (there {A = A} x) = begin
    ⌞ x ⌟V [ π₁ idS ]
  ≡⟨ cong (_[ π₁ idS ]) (soundnessNfVar x) ⟩
    conv (congTmΓ ([idS] A)) (accVar x idS) [ π₁ idS ]
  ≡⟨ conv-in-func {Y = Tm Γ}
                  ([idS] A)
                  (_[ π₁ idS ])
                  (congTmΓ ([idS] A))
                  (accVar x idS)
                  (congTmΓ (cong (_[ π₁ idS ]) ([idS] A))) ⟩
    conv (congTmΓ (cong (_[ π₁ idS ]) ([idS] A))) (accVar x idS [ π₁ idS ])
  ≡⟨ conv-unique (congTmΓ (cong (_[ π₁ idS ]) ([idS] A)))
                 (trans (congTmΓ (Eq.sym ([∘] A idS (π₁ idS)))) (congTmΓ (congA[] (idS∘ π₁ idS))))
                 (accVar x idS [ π₁ idS ]) ⟩
    conv (trans (congTmΓ (Eq.sym ([∘] A idS (π₁ idS)))) (congTmΓ (congA[] (idS∘ π₁ idS))))
         (accVar x idS [ π₁ idS ])
  ≡⟨ sym (conv² (congTmΓ (Eq.sym ([∘] A idS (π₁ idS)))) (congTmΓ (congA[] (idS∘ π₁ idS)))) ⟩
    conv (congTmΓ (congA[] (idS∘ π₁ idS)))
         (conv (congTmΓ (Eq.sym ([∘] A idS (π₁ idS))))
               (accVar x idS [ π₁ idS ]))
  ≡⟨ cong (conv (congTmΓ (congA[] (idS∘ (π₁ idS))))) (accVar[]tm x idS (π₁ {A = B} idS)) ⟩
    conv (congTmΓ (congA[] (idS∘ π₁ idS))) (accVar x (idS ∘ π₁ idS))
  ≡⟨ conv-unique (congTmΓ (congA[] (idS∘ π₁ idS)))
                 (cong (λ z → Tm (Γ , B) (A [ z ])) (idS∘ π₁ idS)) 
                 (accVar x (idS ∘ π₁ idS)) ⟩
    conv (cong (λ z → Tm (Γ , B) (A [ z ])) (idS∘ π₁ idS)) (accVar x (idS ∘ π₁ idS))
  ≡⟨ apd' (accVar x) (idS∘ π₁ idS) ⟩
    accVar x (π₁ idS)
  ≡⟨ conv-unique refl
                (trans (congTmΓ (sym (accVarEq.eqTy idS))) (congTmΓ ([idS] (A [ π₁ idS ]))))
                (accVar x (π₁ idS)) ⟩
    conv (trans (congTmΓ (sym (accVarEq.eqTy idS))) (congTmΓ ([idS] (A [ π₁ idS ])))) (accVar x (π₁ idS))
  ≡⟨ sym (conv² (congTmΓ (sym (accVarEq.eqTy idS))) (congTmΓ ([idS] (A [ π₁ idS ])))) ⟩
    conv (congTmΓ ([idS] (A [ π₁ idS ]))) (conv (congTmΓ (sym (accVarEq.eqTy idS))) (accVar x (π₁ idS)))
  ∎

NfTm[accVar] : (x : Var Γ A){σ : Sub Δ Γ} → NeSub Δ Γ σ → NfTm Δ (accVar x σ)
NfTm[accVar] {Γ , A} {_} {Δ} here {σ} nσ = conv (sym eqTy) (π₂ nσ)
  where
    eqTy : NfTm Δ (conv (congTmΓ (sym (accVarEq.eqTy σ))) (π₂ σ)) ≡ NfTm Δ (π₂ σ)
    eqTy = begin
        NfTm Δ (conv (congTmΓ (Eq.sym (accVarEq.eqTy σ))) (π₂ σ))
      ≡⟨ conv-in-func {Y = Tm Δ} (sym (accVarEq.eqTy σ)) (NfTm Δ) (congTmΓ (sym (accVarEq.eqTy σ))) (π₂ σ) refl ⟩
        NfTm Δ (π₂ σ)
      ∎
NfTm[accVar] {Γ , A'} {_} {Δ} (there {A = A} x) {σ} nσ = conv (sym eqTy) (NfTm[accVar] x (π₁ nσ))
  where
    eqTy : NfTm Δ (conv (congTmΓ (Eq.sym (accVarEq.eqTy σ))) (accVar x (π₁ σ))) ≡ NfTm Δ (accVar x (π₁ σ))
    eqTy = begin
        NfTm Δ (conv (congTmΓ (sym (accVarEq.eqTy σ))) (accVar x (π₁ σ)))
      ≡⟨ conv-in-func {Y = Tm Δ} (sym (accVarEq.eqTy σ)) (NfTm Δ) (congTmΓ (sym (accVarEq.eqTy σ))) (accVar x (π₁ σ)) refl ⟩
        NfTm Δ (accVar x (π₁ σ))
      ∎

NfTm[nfVar] : (x : Var Γ A) → NfTm Γ (nfVar x)
NfTm[nfVar] {Γ} {A} x = conv (sym eqTy) (NfTm[accVar] x idS) -- NfTm[accVar] x idS
  where
    eqTy : NfTm Γ (nfVar x) ≡ NfTm Γ (accVar x idS)
    eqTy = begin
        NfTm Γ (conv (congTmΓ ([idS] A)) (accVar x idS))
      ≡⟨ conv-in-func {Y = Tm Γ} ([idS] A) (NfTm Γ) (congTmΓ ([idS] A)) (accVar x idS) refl ⟩
        NfTm Γ (accVar x idS)
      ∎

thm[normalization] : (t : Tm Γ A) → Σ[ t' ∈ Tm Γ A ] t ≡ t' × NfTm Γ t'
thm[normalization] t with reifyTm t
... | x , eq = nfVar x , (trans eq (soundnessNfVar x) , NfTm[nfVar] x)