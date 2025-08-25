open import Prelude

open import Theory.SC+El+Pi+B.QIIRT-tyOf.Model

module Theory.SC+El+Pi+B.QIIRT-tyOf.Rec (M : SC+El+Pi+B ℓ₁ ℓ₂ ℓ₃ ℓ₄) where

open SC+El+Pi+B M

import Theory.SC+El+Pi+B.QIIRT-tyOf.Syntax as S
open S.Var

recCtx  : S.Ctx → Ctx
{-# TERMINATING #-}
recTy   : S.Ty Γ → Ty (recCtx Γ)
recTm   : S.Tm Γ → Tm (recCtx Γ)
recSub  : S.Sub Γ Δ → Sub (recCtx Γ) (recCtx Δ)
recTyOf : (t : S.Tm Γ) → S.tyOf t ≡ A → tyOf (recTm t) ≡ recTy A

recCtx S.∅ = ∅
recCtx (Γ S., A) = recCtx Γ ,C recTy A

recTm⟨π₂idS⟩≡π₂idS
  : recTm (S.π₂ {A = A} S.idS) ≡  π₂ idS
recTm⟨t[σ]⟩=recTmt[recSubσ]t
  : recTm (t S.[ σ ]) ≡ recTm t [ recSub σ ]t

recTy (A S.[ σ ]) = recTy A [ recSub σ ]T
recTy S.U         = U
recTy (S.[idS]T {A = A} i) = [idS]T {A = recTy A} i
recTy (S.[∘]T A σ τ i)     = [∘]T (recTy A) (recSub σ) (recSub τ) i
recTy (S.U[] {σ = σ} i)    = U[] {σ = recSub σ} i

recTy (S.El u p)  = El (recTm u) (recTyOf u p)
recTy (S.Π A B)   = Π (recTy A) (recTy B)
recTy (S.El[] τ u p q i)  =
  {!El[] (recSub τ) (recTm u) (recTyOf u p) i!}
  where
    foo : (tyOf[] ∙ cong (λ z → z [ recSub τ ]T) (recTyOf u p) ∙ U[])
      ≡ {!recTyOf (u Foo.[ τ ]t) q!}
    foo = {!!}
-- (El[] (recSub τ) (recTm u) (recTyOf u p) {!(cong tyOf (recTm⟨t[σ]⟩=recTmt[recSubσ]t {t = u} {σ = τ})) ∙ recTyOf (u [ τ ]) q!}) i
recTy (S.El[]₂ u pu pu' i) = {!!}
recTy (S.Π[] i) = {!!}

recTy S.𝔹         = 𝔹
recTy (S.𝔹[] {σ = σ} i) =
  𝔹[] {σ = recSub σ} i
recTy (S.𝔹[]₂ i) = {!!}

recTy (S.El𝕓 i) = {!!}
recTy (S.tyOfπ a pa b pb i) = {!!}
recTy (S.Elπ a pa b pb i) = {!!}
-- recTy (S.Ty-is-set A A₁ x y i i₁) = {!!}

recSub⟨π₁,⟩≡π₁,
  : (σ : S.Sub Γ Δ) (A : S.Ty Δ) (p : S.tyOf t ≡ A S.[ σ ])
  → recTy A [ π₁ (recSub σ , recTm t ∶[ recTyOf t p ]) ]T
  ≡ recTy A [ recSub (S.π₁ (σ S., t ∶[ p ])) ]T
  
recTm (t S.[ σ ])       = recTm t [ recSub σ ]t
recTm (S.π₂ σ)          = π₂ (recSub σ)
recTm (S.βπ₂ {A = A} σ t p _ i) = 
  βπ₂ (recSub σ) (recTm t) (recTyOf t p) i
recTm (S.[idS]t t i)    = [idS]t (recTm t) i
recTm (S.[∘]t t σ τ i)  = [∘]t (recTm t) (recSub σ) (recSub τ) i

recTm (S.app t p)   = app (recTm t) (recTyOf t p)
recTm (S.abs t)     = abs (recTm t)
recTm (S.abs[] t i) = {!!}
recTm (S.Πβ t i)    = {!!}
recTm (S.Πη t p i)  = {!!}

recTm S.tt = tt
recTm S.ff = ff
recTm (S.elim𝔹 P t u pt pu pt₂ pu₂) =
  elim𝔹 (recTy P) (recTm t) (recTm u) {!recTyOf t pt!} {!!} {!!} {!!}
recTm (S.tt[] i) = {!!}
recTm (S.ff[] i) = {!!}
recTm (S.elim𝔹[] P t t₁ pt pu t₂ pb pt₂ pu₂ pb₂ x i) = {!!}

recTm S.𝕓              = 𝕓
recTm (S.π t pt u pu) =
  π (recTm t) (recTyOf t pt) (recTm u) (recTyOf u pu)
recTm (S.𝕓[] i) = {!!}
recTm (S.π[] t pa t₁ pb pa' pb' i) = {!!}

recSub S.∅              = ∅S
recSub (σ S., t ∶[ p ]) = recSub σ , recTm t ∶[ recTyOf t p ]
recSub S.idS            = idS
recSub (τ S.∘ σ)        = recSub τ ∘ recSub σ
recSub (S.π₁ σ)         = π₁ (recSub σ)
recSub (S.βπ₁ σ t p i)  = βπ₁ (recSub σ) (recTm t) (recTyOf t p) i
recSub ((S.idS∘ σ) i)   = (idS∘ recSub σ) i
recSub ((σ S.∘idS) i)   = (recSub σ ∘idS) i
recSub (S.assocS σ τ γ i) = assocS (recSub σ) (recSub τ) (recSub γ) i
recSub (S.η∅ σ i) = η∅ (recSub σ) i
recSub (S.ηπ {Γ} {Δ} {A} σ i) =
   (ηπ (recSub σ)
   ∙ cong (π₁ (recSub σ) , π₂ (recSub σ) ∶[_]) (UIP (tyOfπ₂ (recSub σ)) (recTyOf (S.π₂ σ) (S.tyOfπ₂ σ)))) i
 
recSub (S.,∘ {A = A} τ t σ p q i) =
  (,∘ (recSub τ) (recTm t) (recSub σ) (recTyOf t p) (recTyOf (t S.[ σ ]) q)) i

recSub⟨π₁,⟩≡π₁, _ _ _ = refl

recTyOf {A = A} (t S.[ σ ]) p =
  tyOf[] ∙ cong _[ recSub σ ]T (recTyOf t refl) ∙ cong recTy p
  
recTyOf {A = A} (S.π₂ {Γ} {Δ} {B} σ) p =
  tyOfπ₂ (recSub σ) ∙ cong recTy p
recTyOf {A = A} (S.app t pt) p =
  tyOfapp {t = recTm t} (recTyOf t pt) ∙ cong recTy p
recTyOf {A = A} (S.abs {_} {B} t)   p =
  tyOfabs ∙ {!!}
recTyOf {A = A} S.tt        p =
  tyOftt ∙ sym [idS]T ∙ cong recTy p
recTyOf {A = A} S.ff        p =
  tyOfff ∙ sym [idS]T ∙ cong recTy p
recTyOf {A = A} (S.elim𝔹 P t u pt pu t₂ pt₂) p =
  {!!} ∙ cong recTy p
recTyOf {A = A} S.𝕓 p = tyOf𝕓  ∙ cong recTy p
recTyOf {A = A} (S.π t pa u pb) p =
  tyOfπ (recTm t) (recTyOf t pa) (recTm u) (recTyOf u pb) ∙ cong recTy p

recTyOf {A = A} (S.βπ₂ σ t p₁ q i) = 
  isProp→PathP {B = λ i → S.tyOf (S.βπ₂ σ t p₁ q i) ≡ A → tyOf (recTm (S.βπ₂ σ t p₁ q i)) ≡ recTy A}
  (λ j → isPropΠ λ _ → UIP) (recTyOf (S.βπ₂ σ t p₁ q i0)) (recTyOf (S.βπ₂ σ t p₁ q i1)) i 
recTyOf {A = A} (S.[idS]t t i) =
  isProp→PathP
    {B = λ i → S.tyOf (S.[idS]t t i) ≡ A → tyOf (recTm (S.[idS]t t i)) ≡ recTy A}
    (λ j → isPropΠ λ _ → UIP)
    (recTyOf (S.[idS]t t i0))
    (recTyOf (S.[idS]t t i1)) i 
recTyOf {A = A} (S.[∘]t t σ τ i) = 
  isProp→PathP {B = λ i → S.tyOf (S.[∘]t t σ τ i) ≡ A → tyOf (recTm (S.[∘]t t σ τ i)) ≡ recTy A}
  (λ j → isPropΠ λ _ → UIP) (recTyOf (S.[∘]t t σ τ i0)) (recTyOf (S.[∘]t t σ τ i1)) i 

recTyOf {A = A} (S.abs[] t i) = {!!}
recTyOf {A = A} (S.Πβ t i) = {!!}
recTyOf {A = A} (S.Πη t p i) = {!!}
recTyOf {A = A} (S.tt[] i) = {!!}
recTyOf {A = A} (S.ff[] i) = {!!}
recTyOf {A = A} (S.elim𝔹[] P t u pt pu t₂ pb pt₂ pu₂ pb₂ x i) =
  {!!}
recTyOf {A = A} (S.𝕓[] i) = {!!}
recTyOf {A = A} (S.π[] t pa t₁ pb pa' pb' i) = {!!}

recTm⟨π₂idS⟩≡π₂idS = refl
recTm⟨t[σ]⟩=recTmt[recSubσ]t = refl
