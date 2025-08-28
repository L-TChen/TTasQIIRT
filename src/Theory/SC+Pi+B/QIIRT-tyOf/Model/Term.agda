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
  }

TermSC : SC _ _ _ _
TermSC = record { mot = TermM ; isSC = TermIsSC }

TermPi : Pi TermSC
TermPi = record
  { Π = Π
  ; app = app
  ; tyOfapp = λ _ → refl
  ; abs = abs
  ; tyOfabs = refl
  ; Π[] =  λ {A = A} σ B →
    Π[] σ B ∙ cong (λ τ → Π (A [ σ ]) (B [ (σ ∘ π₁ idS) , π₂ idS ∶[ τ ] ])) (UIP _ _) 
  ; abs[] = λ σ t →
    abs[] σ t ∙ cong (λ τ → abs (t [ (σ ∘ π₁ idS) , π₂ idS ∶[ τ ] ])) (UIP _ _)
  ; Πβ = Πβ
  ; Πη = Πη
  }

TermBool : 𝓑 TermSC
TermBool = record
  { 𝔹   = 𝔹
  ; 𝔹[] = 𝔹[]
  ; tt = tt
  ; ff = ff
  ; tyOftt = [idS]T
  ; tyOfff = [idS]T
  ; tt[] = tt[]
  ; ff[] = ff[]
  ; elim𝔹 = elim𝔹
  ; tyOfelim𝔹 = λ P t pt u pu b pb → refl
  ; elim𝔹[] = λ {σ = σ} P t pt u pu b pb pt₂ pu₂ pb₂ p →
    let p₁ = step-≡ (𝔹 [ π₁ idS ])
            (step-≡ (𝔹 [ π₁ idS ])
             (step-≡ 𝔹 (𝔹 [ σ ∘ π₁ idS ] ∎) (λ i₂ → 𝔹[] (σ ∘ π₁ idS) (~ i₂)))
             (𝔹[] (π₁ idS)))
            (λ _ → 𝔹 [ π₁ idS ]) 
        p₂ = pt₂ ∙
          (λ i₁ →
             P [
             (σ ∘ π₁ idS) , π₂ idS ∶[
             UIP
             (step-≡ (𝔹 [ π₁ idS ])
              (step-≡ (𝔹 [ π₁ idS ])
               (step-≡ 𝔹 (𝔹 [ σ ∘ π₁ idS ] ∎) (λ i₂ → 𝔹[] (σ ∘ π₁ idS) (~ i₂)))
               (𝔹[] (π₁ idS)))
              (λ _ → 𝔹 [ π₁ idS ]))
             𝔹[]₂ i₁
             ]
             ]
             [ idS , tt ∶[ [idS]T ] ])
    in
    elim𝔹[] P t pt u pu b pb
      (pt₂ ∙ cong (λ p → P [ (σ ∘ π₁ idS) , π₂ idS ∶[ p ] ] [ idS , tt ∶[ [idS]T ] ]) (UIP _ _))
      (pu₂ ∙ cong (λ p → P [ (σ ∘ π₁ idS) , π₂ idS ∶[ p ] ] [ idS , ff ∶[ [idS]T ] ]) (UIP _ _))
    pb₂ (p ∙ cong (λ p → P [ (σ ∘ π₁ idS) , π₂ idS ∶[ p ] ] [ idS , b [ σ ] ∶[ pb₂ ] ]) (UIP _ _)) ∙
    λ i → elim𝔹 (P [ (σ ∘ π₁ idS) , π₂ idS ∶[ UIP 𝔹[]₂ p₁ i ] ])
      (t [ σ ]) {!isOfHLevel→isOfHLevelDep 1 {B = λ p → tyOf (t [ σ ]) ≡ (P [ (σ ∘ π₁ idS) , π₂ idS ∶[ p ] ] [ idS , tt ∶[ tyOftt ] ])} {!!} {!!} {!!} {!!} i !}
      (u [ σ ]) {!!} (b [ σ ]) pb₂
  }

Term : SC+Pi+B _ _ _ _
Term = record
  { 𝒞  = TermSC
  ; 𝒫i = TermPi
  ; ℬ  = TermBool
  }
