open import Prelude
  hiding (Bool)

module Theory.SC+Pi+B.QIIRT-tyOf.Model.Term where

open import Theory.SC+Pi+B.QIIRT-tyOf.Syntax
open import Theory.SC.QIIRT-tyOf.Model
open import Theory.SC+Pi+B.QIIRT-tyOf.Model

TermM : Motive
TermM = record
  { Ctx  = Ctx
  ; Ty   = Ty
  ; Sub  = Sub
  ; Tm   = Tm
  ; tyOf = tyOf
  ; Sub-is-set = Sub-is-set
  ; Ty-is-set = Ty-is-set
  ; Tm-is-set = Tm-is-set
  }

TermIsSC : IsSC TermM
TermIsSC = record
  { ∅       = ∅
  ; _,C_    = _,_
  ; _[_]T   = _[_]
  ; _[_]t   = _[_]
  ; tyOf[]  = refl
  ; ∅S      = ∅
  ; _,_∶[_] = _,_∶[_]
  ; idS     = idS
  ; _∘_     = _∘_
  ; π₁      = π₁
  ; π₂      = π₂
  ; tyOfπ₂  = tyOfπ₂
  ; idS∘_   = idS∘_
  ; _∘idS   = _∘idS
  ; assocS  = assocS
  ; [idS]T  = [idS]T
  ; [∘]T    = [∘]T
  ; ,∘      = ,∘
  ; ηπ      = ηπ
  ; η∅      = η∅
  ; βπ₁     = βπ₁
  ; βπ₂     = λ {Γ} {Δ} {A} σ t p
    → βπ₂ σ t p (cong (A [_]) (βπ₁ σ t p) ∙ sym p)
  ; [idS]t  = [idS]t
  ; [∘]t    = [∘]t
  ; U       = U
  ; U[]     = U[]
  ; tyOf[]≡U = λ {σ = σ} p
    → cong (λ A → A [ σ ]) p ∙ U[]
  }


TermSC : SC _ _ _ _
TermSC = record { mot = TermM ; isSC = TermIsSC }

TermPi : Pi TermSC
TermPi .Pi.Π       = Π
TermPi .Pi.app     = app
TermPi .Pi.tyOfapp = λ _ → refl
TermPi .Pi.abs     = abs
TermPi .Pi.tyOfabs = refl
TermPi .Pi.Π[] {_} {_} {A} σ B =
  Π[] σ B ∙ cong (λ p → Π (A [ σ ]) (B [ (σ ∘ π₁ idS) , π₂ idS ∶[ p ] ] )) (Ty-is-set _ _ _ _)
TermPi .Pi.abs[] σ t =
  abs[] σ t ∙ cong (λ τ → abs (t [ (σ ∘ π₁ idS) , π₂ idS ∶[ τ ] ])) (Ty-is-set _ _ _ _)
TermPi .Pi.Πβ = Πβ
TermPi .Pi.Πη = Πη

{-# TERMINATING #-}
TermBool : 𝓑 TermSC
TermBool .𝓑.𝔹      = 𝔹
TermBool .𝓑.𝔹[]    = 𝔹[]
TermBool .𝓑.tt     = tt
TermBool .𝓑.ff     = ff
TermBool .𝓑.tyOftt = [idS]T
TermBool .𝓑.tyOfff = [idS]T
TermBool .𝓑.tt[]   = tt[]
TermBool .𝓑.ff[]   = ff[]
TermBool .𝓑.elim𝔹  = elim𝔹
TermBool .𝓑.tyOfelim𝔹 P t pt u pu b pb = refl
TermBool .𝓑.elim𝔹[] {σ = σ} P t pt u pu b pb pt₂ pu₂ pb₂ p =
  --  (2025-08-30): I haven't investiaged why this case does not pass
  -- the termination checker.
    elim𝔹[] P t pt u pu b pb pt₂' pu₂' pb₂ p'
    ∙ λ i → elim𝔹 (P [ (σ ∘ π₁ idS) , π₂ idS ∶[ Ty-is-set _ _ 𝔹[]₂ p₁ i ] ])
      (t [ σ ]) (isOfHLevel→isOfHLevelDep 1
         {B = λ p → tyOf (t [ σ ]) ≡ (P [ (σ ∘ π₁ idS) , π₂ idS ∶[ p ] ] [ idS , tt ∶[ tyOftt ] ])}
             (λ p → Ty-is-set _ _)
             pt₂' pt₂ (Ty-is-set _ _ 𝔹[]₂ p₁) i)
      (u [ σ ]) (isOfHLevel→isOfHLevelDep 1
        {B = λ p → tyOf (u [ σ ]) ≡ (P [ (σ ∘ π₁ idS) , π₂ idS ∶[ p ] ] [ idS , ff ∶[ tyOfff ] ])}
      (λ p → Ty-is-set _ _) pu₂' pu₂ (Ty-is-set _ _ 𝔹[]₂ p₁) i)
      (b [ σ ]) pb₂
    where
      pt₂' = pt₂ ∙ cong {B = λ v → Ty _} (λ z → P [ (σ ∘ π₁ idS) , π₂ idS ∶[ z ] ] [ idS , tt ∶[ [idS]T ] ]) (Ty-is-set _ _ _ _)
      pu₂' = pu₂ ∙ cong {B = λ v → Ty _} (λ z → P [ (σ ∘ π₁ idS) , π₂ idS ∶[ z ] ] [ idS , ff ∶[ [idS]T ] ]) (Ty-is-set _ _ _ _)
      p' =     p ∙ cong {B = λ v → Ty _} (λ z → P [ (σ ∘ π₁ idS) , π₂ idS ∶[ z ] ] [ idS , b [ σ ] ∶[ pb₂ ] ]) (Ty-is-set _ _ _ _)
      p₁ =
        𝔹 [ π₁ idS ]
          ≡⟨ refl ⟩
        𝔹 [ π₁ idS ]
          ≡⟨ 𝔹[] (π₁ idS) ⟩
        𝔹
          ≡⟨ sym $ 𝔹[] (σ ∘ π₁ idS) ⟩
        𝔹 [ σ ∘ π₁ idS ]
          ∎

      p₂ = pt₂ ∙ (λ j → P [ (σ ∘ π₁ idS) , π₂ idS ∶[ Ty-is-set _ _ p₁ 𝔹[]₂ j ] ] [ idS , tt ∶[ [idS]T ] ])


Term : SC+Pi+B _ _ _ _
Term = record { 𝒞  = TermSC ; 𝒫i = TermPi ; ℬ  = TermBool}
