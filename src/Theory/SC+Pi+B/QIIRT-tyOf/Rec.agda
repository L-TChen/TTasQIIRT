{-# OPTIONS --lossy-unification #-}
{-
  Agda does not support interleaved function definitions, so we add
  equations that are needed between definitions and defined
  afterwards.
-}
open import Prelude

open import Theory.SC+Pi+B.QIIRT-tyOf.Model

module Theory.SC+Pi+B.QIIRT-tyOf.Rec (M : SC+Pi+B ℓ₁ ℓ₂ ℓ₃ ℓ₄) where
-- module Theory.SC+Pi+B.QIIRT-tyOf.Rec (M : SC+Pi+B ℓ ℓ ℓ ℓ) where

open SC+Pi+B M

import Theory.SC+Pi+B.QIIRT-tyOf.Syntax as S
open S.Var

{-
data Tag : Set where
  ctx ty sub tm tyof : Tag

tyOfRec : Tag → Set ℓ
{-# TERMINATING #-}
rec : (t : Tag) → tyOfRec t

tyOfRec ctx  = S.Ctx → Ctx
tyOfRec ty   = {Γ : S.Ctx} → S.Ty Γ → Ty (rec ctx Γ)
tyOfRec tm   = {Γ : S.Ctx} → S.Tm Γ → Tm (rec ctx Γ)
tyOfRec sub  = {Γ Δ : S.Ctx} → S.Sub Γ Δ → Sub (rec ctx Γ) (rec ctx Δ)
tyOfRec tyof = {Γ : S.Ctx} → {A : S.Ty Γ} → (t : S.Tm Γ)
  → S.tyOf t ≡ A → tyOf (rec tm t) ≡ rec ty A

rec ctx S.∅              = ∅
rec ctx (Γ S., A)        = rec ctx Γ ,C rec ty A
rec ty (A S.[ σ ])          = (rec ty A) [ rec sub σ ]T
rec sub S.∅              = ∅S
rec sub (σ S., t ∶[ p ]) = rec sub σ , rec tm t ∶[ rec tyof t p ]
rec sub S.idS            = idS
rec sub (σ S.∘ τ) = rec sub σ ∘ rec sub τ
rec sub (S.π₁ σ)  = π₁ (rec sub σ)
rec sub (S.βπ₁ σ t p i) = βπ₁ (rec sub σ) (rec tm t) {! rec tyof t p !} i
rec sub ((S.idS∘ σ) i) = (idS∘ rec sub σ) i
rec sub ((σ S.∘idS) i) = (rec sub σ ∘idS) i
rec sub (S.assocS σ σ₁ σ₂ i) = assocS (rec sub σ) (rec sub σ₁) (rec sub σ₂) i
rec sub (S.,∘ σ t σ₁ p q i) = {!!}
-- ,∘ (rec sub σ) (rec tm t) (rec sub σ₁) (rec tyOf t p) {!rec tyOf ? q!} {!!}
rec sub (S.η∅ σ i) = {!!}
rec sub (S.ηπ σ i) = {!!}
rec ty (S.[idS]T {Γ} {A} i) = [idS]T {rec ctx Γ} {rec ty A} i
rec ty (S.[∘]T A σ τ i) = [∘]T (rec ty A) (rec sub σ) (rec sub τ) i
rec ty S.U              = U
rec ty (S.U[] {Γ} {Δ} {σ} i) = U[] {rec ctx Γ} {rec ctx Δ} {rec sub σ} i
rec ty (S.Π A B)        = Π (rec ty A) (rec ty B)
rec ty (S.Π[] σ A i)    = {! Π[] (rec sub σ) (rec ty A) i !}
rec ty S.𝔹              = 𝔹
rec ty (S.𝔹[] σ i)      = 𝔹[] (rec sub σ) i
rec ty (S.𝔹[]₂ i)       = {!!}
rec tm (t S.[ σ ]) = rec tm t [ rec sub σ ]t
rec tm (S.π₂ σ)    = π₂ (rec sub σ)
rec tm (S.βπ₂ σ t p q i) = βπ₂ (rec sub σ) (rec tm t) {! rec tyof t p !} i
rec tm (S.[idS]t t i) = [idS]t (rec tm t) i
rec tm (S.[∘]t t σ τ i) = [∘]t (rec tm t) (rec sub σ) (rec sub τ) i
rec tm (S.app {Γ} {A} t B pt) = app (rec tm t) (rec ty B) {! rec tyof {Γ} {S.Π A B} t pt!} -- (rec tyOf {Γ} {S.Π A B} t pt) 
rec tm (S.abs t)       = abs (rec tm t)
rec tm (S.abs[] σ t i) = abs[] (rec sub σ) (rec tm t) i
rec tm (S.Πβ t pt i) = {!!}
rec tm (S.Πη t pt i) = {!!}
rec tm S.tt = tt
rec tm S.ff = ff
rec tm (S.tt[] σ i) = tt[] (rec sub σ) i
rec tm (S.ff[] σ i) = ff[] (rec sub σ) i
rec tm (S.elim𝔹[] P t pt t₁ pu t₂ pb pt₂ pu₂ pb₂ p i) = {!!}

rec tyof (t S.[ σ ]) pt = {!!} -- tyOf[] ∙ cong _[ rec sub σ ]T (rec tyOf t refl) ∙ cong rec ty pt
rec tyof (S.π₂ σ) pt    = {!!}
rec tyof (S.βπ₂ σ t p q i) pt = {!!}
rec tyof (S.[idS]t t i) pt = {!!}
rec tyof (S.[∘]t t σ τ i) pt = {!!}
rec tyof (S.app t B pt₁) pt = {!!}
rec tyof (S.abs t) pt = {!!}
rec tyof (S.abs[] σ t i) pt = {!!}
rec tyof (S.Πβ t pt₁ i) pt = {!!}
rec tyof (S.Πη t pt₁ i) pt = {!!}
rec tyof S.tt pt = {!!} -- tyOftt ∙ sym [idS]T ∙ cong (rec ty) pt
rec tyof S.ff pt = {!!}
rec tyof (S.tt[] σ i) pt = {!!}
rec tyof (S.ff[] σ i) pt = {!!}
rec tyof (S.elim𝔹 P t pt₁ t₁ pu t₂ x) pt = {!!}
rec tyof (S.elim𝔹[] P t pt₁ t₁ pu t₂ pb pt₂ pu₂ pb₂ p i) pt = {!!}
rec tm (S.elim𝔹 P t pt u pu b pb) =
  elim𝔹 {!!} -- (rec ty P)
    (rec tm t) (rec tyof t pt ∙ {!!}) -- cong (λ p → (rec ty P) [ idS , tt ∶[ p ] ]T) {!!})
    (rec tm u) (rec tyof u pu ∙ {!!})
    (rec tm b) (rec tyof b pb ∙ {! refl !}) 
    
recCtx  = rec ctx
recSub  = rec sub
recTy   = rec ty
recTm   = rec tm
recTyOf = rec tyof 
-}

recCtx  : S.Ctx → Ctx
{-# TERMINATING #-}
recTy   : S.Ty Γ → Ty (recCtx Γ)
recTm   : S.Tm Γ → Tm (recCtx Γ)
recSub  : S.Sub Γ Δ → Sub (recCtx Γ) (recCtx Δ)
recTyOf : (t : S.Tm Γ) → S.tyOf t ≡ A → tyOf (recTm t) ≡ recTy A

recCtx S.∅ = ∅
recCtx (Γ S., A) = recCtx Γ ,C recTy A

recTy (A S.[ σ ])          = recTy A [ recSub σ ]T
recTy S.U                  = U
recTy (S.[idS]T {A = A} i) = [idS]T {A = recTy A} i
recTy (S.[∘]T A σ τ i)     = [∘]T (recTy A) (recSub σ) (recSub τ) i
recTy (S.U[] {σ = σ} i)    = U[] {σ = recSub σ} i

recTy (S.Π A B)    = Π (recTy A) (recTy B)
recTy (S.Π[] σ B i) = Π[] (recSub σ) (recTy B) i

recTy S.𝔹         = 𝔹
recTy (S.𝔹[] σ i) = 𝔹[] (recSub σ) i
recTy (S.𝔹[]₂ {τ = τ} i) = (𝔹[] (π₁ idS) ∙ sym (𝔹[] (recSub τ))) i
-- recTy (S.Ty-is-set A A₁ x y i i₁) = {!!}

private
  recSubidS≡idS
    : recSub {Γ} S.idS ≡ idS

  recSub,≡,Sub
    : (σ : S.Sub Γ Δ) (t : S.Tm Γ) (p : S.tyOf t ≡ A S.[ σ ]) (q : tyOf (recTm t) ≡ recTy A [ recSub σ ]T)
    → recSub (σ S., t ∶[ p ]) ≡ (recSub σ) , (recTm t) ∶[ q ]

  recSub,₁
    : (p : S.tyOf (S.π₂ S.idS) ≡ S.𝔹 S.[ σ S.∘ S.π₁ S.idS ])
      (q : tyOf (π₂ idS) ≡ recTy S.𝔹 [ recSub σ ∘ π₁ idS ]T)
    → recSub {Γ S., S.𝔹} {Δ S., S.𝔹} ((σ S.∘ S.π₁ S.idS) S., S.π₂ S.idS ∶[ p ])
      ≡ (recSub σ ∘ π₁ idS) , π₂ idS ∶[ q ]

  recSub,₂
    : (σ : S.Sub Γ Δ) (b : S.Tm Δ) (p : S.tyOf (b S.[ σ ]) ≡ S.𝔹 S.[ S.idS ]) (q : tyOf (recTm b [ recSub σ ]t) ≡ 𝔹 [ idS ]T) 
    → recSub (S.idS S., b S.[ σ ] ∶[ p ]) ≡ (idS , recTm b [ recSub σ ]t ∶[ q ])

  recSubidS,t≡idS,Subt
    : (t : S.Tm Γ) (p : S.tyOf t ≡ A S.[ S.idS ]) (q : tyOf (recTm t) ≡ recTy A [ idS ]T)
    → recSub (S.idS S., t ∶[ p ])
    ≡ idS , recTm t ∶[ q ]

  recSub↑𝔹
    : (σ : S.Sub Γ Δ)
    → recSub (σ S.↑𝔹) ≡ recSub σ ↑𝔹

  recTyP[↑𝔹]ff≡
    : (P : S.Ty (Γ S., S.𝔹)) (q : tyOf (recTm S.ff) ≡ (recTy S.𝔹 [ idS ]T))
    → recTy (P S.[ σ S.↑𝔹 ]) [ idS , recTm S.ff ∶[ q ] ]T
      ≡ (recTy P [ recSub σ ↑𝔹 ]T) [ idS , ff ∶[ tyOfff ] ]T

  recTyP[↑𝔹]tt≡
    : (P : S.Ty (Γ S., S.𝔹)) (q : tyOf (recTm S.tt) ≡ (recTy S.𝔹 [ idS ]T))
    → recTy (P S.[ σ S.↑𝔹 ]) [ idS , recTm S.tt ∶[ q ] ]T
      ≡ (recTy P [ recSub σ ↑𝔹 ]T) [ idS , tt ∶[ tyOftt ] ]T

  recTmabs[]
    :  (σ : S.Sub Γ Δ) (t : S.Tm (Δ S., A))
    → recTm (S.abs t) [ recSub σ ]t
    ≡ recTm (S.abs (t S.[ σ S.↑ A ]))

recTm (t S.[ σ ])       = recTm t [ recSub σ ]t
recTm (S.π₂ σ)          = π₂ (recSub σ)
recTm (S.βπ₂ σ t p _ i) = 
  βπ₂ (recSub σ) (recTm t) (recTyOf t p) i
recTm (S.[idS]t t i)    = [idS]t (recTm t) i
recTm (S.[∘]t t σ τ i)  = [∘]t (recTm t) (recSub σ) (recSub τ) i

recTm (S.app t B p)   = app (recTm t) (recTy B) (recTyOf t p)
recTm (S.abs t)     = abs (recTm t)
recTm (S.abs[] {A = A} σ t i) = recTmabs[] σ t i
{- (
  abs (recTm t) [ recSub σ ]t
    ≡⟨ abs[] (recSub σ) (recTm t) ⟩
  abs (recTm t [ recSub σ ↑ recTy A ]t)
    ≡⟨ (λ i → abs (recTm t [ recSub↑≡↑recSub σ A (~ i) ]t)) ⟩ -- supposed to be definitional
  abs (recTm t [ recSub (σ S.↑ A) ]t)
    ∎) i
-}

recTm (S.Πβ {Γ} {A = A} t p i) = (
  app (abs (recTm t)) (recTy (S.tyOf t)) (recTyOf (S.abs t) p)
    ≡⟨ cong₂ (app (abs (recTm t))) (sym $ recTyOf t refl ) 
       (isOfHLevel→isOfHLevelDep 1 {B = λ B → tyOf (abs (recTm t)) ≡ Π (recTy A) B}
       (λ _ → UIP)
       (recTyOf (S.abs t) p) tyOfabs (sym $ recTyOf t refl))
     ⟩

  app (abs (recTm t)) (tyOf (recTm t)) tyOfabs
    ≡⟨ Πβ (recTm t) tyOfabs ⟩
  recTm t 
    ∎) i  

recTm (S.Πη t p i) = Πη (recTm t) (recTyOf t p) i

recTm S.tt = tt
recTm S.ff = ff
recTm (S.elim𝔹 P t pt u pu b pb) =
  elim𝔹 (recTy P)
    (recTm t) (recTyOf t pt ∙ cong (recTy P [_]T) (recSubidS,t≡idS,Subt S.tt S.[idS]T tyOftt))
    (recTm u) (recTyOf u pu ∙ cong (recTy P [_]T) (recSubidS,t≡idS,Subt S.ff S.[idS]T tyOfff))
    (recTm b) (recTyOf b pb ∙ cong (𝔹 [_]T) recSubidS≡idS)
    -- `recSub idS` is strictly equal to `idS`, but this equation is only introduced later
    -- and Agda cannot unfold at this point in order to type check.
recTm (S.tt[] σ i) = tt[] (recSub σ) i
recTm (S.ff[] σ i) = ff[] (recSub σ) i
recTm (S.elim𝔹[] {Δ} {Γ} {σ} P t pt u pu b pb pt₂ pu₂ pb₂ p i) = (
  elim𝔹 (recTy P) (recTm t) pt'' (recTm u) pu'' (recTm b) pb'' [ recSub σ ]t

    ≡⟨ elim𝔹[] {σ = recSub σ} (recTy P) (recTm t) pt'' (recTm u)  pu''
      (recTm b) pb'' (pt' ∙ recTyP[↑𝔹]tt≡ P tyOftt) (pu' ∙ recTyP[↑𝔹]ff≡ P tyOfff) pb' pp ⟩

  elim𝔹 (recTy P [ recSub σ ↑𝔹 ]T)
    (recTm t [ recSub σ ]t) (pt' ∙ recTyP[↑𝔹]tt≡ P tyOftt)
    (recTm u [ recSub σ ]t) (pu' ∙ recTyP[↑𝔹]ff≡ P tyOfff)
    (recTm b [ recSub σ ]t) pb'

    ≡⟨ (λ i → elim𝔹 (recTy P [ recSub↑𝔹 σ (~ i) ]T)
        (recTm t [ recSub σ ]t) (isOfHLevel→isOfHLevelDep 1
          {B = λ τ → tyOf (recTm t [ recSub σ ]t) ≡ (recTy P [ τ ]T) [ idS , tt ∶[ tyOftt ] ]T}
          (λ _ → UIP) (pt' ∙ recTyP[↑𝔹]tt≡ P tyOftt) pt' (sym $ recSub↑𝔹 σ) i)
          -- dependent UIP
        (recTm u [ recSub σ ]t) (isOfHLevel→isOfHLevelDep 1
          {B = λ τ → tyOf (recTm u [ recSub σ ]t) ≡ (recTy P [ τ ]T) [ idS , ff ∶[ tyOfff ] ]T}
          (λ _ → UIP) (pu' ∙ recTyP[↑𝔹]ff≡ P tyOfff) pu' (sym $ recSub↑𝔹 σ) i)
          -- dependent UIP
        (recTm b [ recSub σ ]t) pb') 
     ⟩

  elim𝔹 (recTy P [ recSub (σ S.↑𝔹) ]T)
    (recTm t [ recSub σ ]t) pt'
    (recTm u [ recSub σ ]t) pu'
    (recTm (b S.[ σ ])) pb'

    ≡⟨⟩
  recTm (S.elim𝔹 (P S.[ σ S.↑𝔹 ]) (t S.[ σ ]) pt₂ (u S.[ σ ]) pu₂ (b S.[ σ ]) pb₂)
    ∎
    ) i
  where
    pt'' = recTyOf t pt ∙ cong (recTy P [_]T) (recSubidS,t≡idS,Subt S.tt S.[idS]T tyOftt)
    pu'' = recTyOf u pu ∙ cong (recTy P [_]T) (recSubidS,t≡idS,Subt S.ff S.[idS]T tyOfff)
    pb'' = recTyOf b pb ∙ cong (𝔹 [_]T) recSubidS≡idS
    pt' = recTyOf (t S.[ σ ]) pt₂ ∙ (λ j → recTy (P S.[ σ S.↑𝔹 ]) [ recSubidS,t≡idS,Subt S.tt S.[idS]T tyOftt j ]T)
    pu' = recTyOf (u S.[ σ ]) pu₂ ∙ (λ j → recTy (P S.[ σ S.↑𝔹 ]) [ recSubidS,t≡idS,Subt S.ff S.[idS]T tyOfff j ]T)
    pb' = recTyOf (b S.[ σ ]) pb₂ ∙ (λ j → 𝔹 [ recSubidS≡idS j ]T)
    q = step-≡ (tyOf (π₂ idS))
          (step-≡ (𝔹 [ π₁ idS ]T)
            (step-≡ 𝔹 ((𝔹 [ recSub σ ∘ π₁ idS ]T) ∎)
            (sym (𝔹[] (recSub σ ∘ π₁ idS))))
          (𝔹[] (π₁ idS)))
        (tyOfπ₂ idS)
    pp : recTy P [ idS , recTm b ∶[ pb'' ] ]T [ recSub σ ]T ≡
         recTy P [ (recSub σ ∘ π₁ idS) , π₂ idS ∶[ q ] ]T [ idS , recTm b [ recSub σ ]t ∶[ pb' ] ]T
-- the proof should just follow from the definition of `rec`
    pp  = 
      recTy P [ idS , recTm b ∶[ _ ] ]T [ recSub σ ]T

        ≡⟨ (λ i → recTy P [ recSubidS,t≡idS,Subt b pb pb'' (~ i) ]T [ recSub σ ]T) ⟩

      recTy P [ recSub (S.idS S., b ∶[ _ ]) ]T [ recSub σ ]T

        ≡⟨ cong recTy p ⟩

      recTy (P S.[ (σ S.∘ S.π₁ S.idS) S., S.π₂ S.idS ∶[ _ ] ] S.[ S.idS S., b S.[ σ ] ∶[ _ ] ])

        ≡⟨⟩

      ((recTy P) [ recSub ((σ S.∘ S.π₁ S.idS) S., S.π₂ S.idS ∶[ S.𝔹[]₂ ]) ]T) [ recSub (S.idS S., b S.[ σ ] ∶[ pb₂ ]) ]T

        ≡⟨ (λ i → recTy P [ recSub,₁ S.𝔹[]₂ q i ]T [ recSub,₂ σ b pb₂ pb' i ]T) ⟩
        
      recTy P [ (recSub σ ∘ π₁ idS) , π₂ idS ∶[ q ] ]T [ idS , recTm b [ recSub σ ]t ∶[ pb' ] ]T

        ∎


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

recTyOf {A = A} (t S.[ σ ]) p =
  tyOf[] ∙ cong _[ recSub σ ]T (recTyOf t refl) ∙ cong recTy p

recTyOf {A = A} (S.π₂ {Γ} {Δ} {B} σ) p =
  tyOfπ₂ (recSub σ) ∙ cong recTy p
recTyOf {A = A} (S.app t B pt) p =
  tyOfapp {t = recTm t} (recTyOf t pt) ∙ cong recTy p
recTyOf {A = C} (S.abs {_} {A} t) p =
  (tyOfabs ∙ cong (Π (recTy A)) (recTyOf t refl)) ∙ cong recTy p
recTyOf {A = A} S.tt        p =
  tyOftt ∙ sym [idS]T ∙ cong recTy p
recTyOf {A = A} S.ff        p =
  tyOfff ∙ sym [idS]T ∙ cong recTy p
recTyOf {A = A} (S.elim𝔹 P t pt u pu t₂ pt₂) p =
  tyOfelim𝔹 (recTy P) (recTm t) _ (recTm u) _ (recTm t₂) _
  ∙ cong (recTy P [_]T) (cong (idS , recTm t₂ ∶[_]) (UIP _ _))
  ∙ cong recTy p

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

-- The following coherence proofs may be further simplified.
recTyOf {A = A} (S.abs[] σ t i) =
  isProp→PathP {B = (λ i → S.tyOf (S.abs[] σ t i) ≡ A → tyOf (recTm (S.abs[] σ t i)) ≡ recTy A)}
  (λ _ → isPropΠ λ _ → UIP) (recTyOf (S.abs[] σ t i0)) (recTyOf (S.abs[] σ t i1)) i
recTyOf {A = A} (S.Πβ t p i) =
  isProp→PathP {B = (λ i → S.tyOf (S.Πβ t p i) ≡ A → tyOf (recTm (S.Πβ t p i)) ≡ recTy A)}
  (λ _ → isPropΠ λ _ → UIP) (recTyOf (S.Πβ t p i0)) (recTyOf (S.Πβ t p i1)) i
recTyOf {A = A} (S.Πη t p i) = 
  isProp→PathP {B = (λ i → S.tyOf (S.Πη t p i) ≡ A → tyOf (recTm (S.Πη t p i)) ≡ recTy A)}
  (λ _ → isPropΠ λ _ → UIP) (recTyOf (S.Πη t p i0)) (recTyOf (S.Πη t p i1)) i
recTyOf {A = A} (S.tt[] σ i) =
  isProp→PathP {B = (λ i → S.tyOf (S.tt[] σ i) ≡ A → tyOf (recTm (S.tt[] σ i)) ≡ recTy A)}
  (λ _ → isPropΠ λ _ → UIP) (recTyOf (S.tt[] σ i0)) (recTyOf (S.tt[] σ i1)) i
recTyOf {A = A} (S.ff[] σ i) =
  isProp→PathP {B = (λ i → S.tyOf (S.ff[] σ i) ≡ A → tyOf (recTm (S.ff[] σ i)) ≡ recTy A)}
  (λ _ → isPropΠ λ _ → UIP) (recTyOf (S.ff[] σ i0)) (recTyOf (S.ff[] σ i1)) i
recTyOf {A = A} (S.elim𝔹[] P t u pt pu t₂ pb pt₂ pu₂ pb₂ x i) =
  isProp→PathP {B = (λ i → S.tyOf (S.elim𝔹[] P t u pt pu t₂ pb pt₂ pu₂ pb₂ x  i)
    ≡ A → tyOf (recTm (S.elim𝔹[] P t u pt pu t₂ pb pt₂ pu₂ pb₂ x i)) ≡ recTy A)}
  (λ _ → isPropΠ λ _ → UIP) (recTyOf (S.elim𝔹[] P t u pt pu t₂ pb pt₂ pu₂ pb₂ x i0)) (recTyOf (S.elim𝔹[] P t u pt pu t₂ pb pt₂ pu₂ pb₂ x i1)) i

-- the following are definitions that need strict equations given above 
recTmabs[] σ t = abs[] (recSub σ) (recTm t)

recSubidS≡idS = refl

recSub,₁ p q = 
  cong (_ , _ ∶[_]) (UIP (recTyOf _ p) q)
recSub,₂ σ b p q =
  cong (_ , _ ∶[_]) (UIP (recTyOf _ p) q)

recSub,≡,Sub σ t p q =
  cong (recSub σ , recTm t ∶[_]) (UIP (recTyOf t p) q)

recSubidS,t≡idS,Subt t p q =
  cong (idS , recTm t ∶[_]) (UIP _ _)

recSub↑𝔹 σ = 
  recSub (σ S.↑𝔹)
    ≡⟨  (λ i → (recSub σ ∘ π₁ idS) , π₂ idS ∶[ UIP (tyOfπ₂ idS ∙ (𝔹[] (π₁ idS)) ∙ (sym (𝔹[] (recSub σ ∘ π₁ idS)))) 𝔹[]₂ i ]) ⟩
  recSub σ ↑𝔹
    ∎

recTyP[↑𝔹]ff≡ {σ = σ} P q =
  recTy (P S.[ σ S.↑𝔹 ]) [ idS , recTm S.ff ∶[ q ] ]T
    ≡⟨ (λ i → recTy P [ recSub↑𝔹 σ i ]T [ idS , ff ∶[ q ] ]T) ⟩
  (recTy P [ recSub σ ↑𝔹 ]T) [ idS , ff ∶[ q ] ]T
    ≡⟨ (λ i → (recTy P [ recSub σ ↑𝔹 ]T) [ idS , ff ∶[ UIP q tyOfff i ] ]T) ⟩ 
  (recTy P [ recSub σ ↑𝔹 ]T) [ idS , ff ∶[ tyOfff ] ]T
    ∎

recTyP[↑𝔹]tt≡ {σ = σ} P q =
  recTy (P S.[ σ S.↑𝔹 ]) [ idS , recTm S.tt ∶[ q ] ]T
    ≡⟨ (λ i → recTy P [ recSub↑𝔹 σ i ]T [ idS , tt ∶[ q ] ]T) ⟩
  (recTy P [ recSub σ ↑𝔹 ]T) [ idS , tt ∶[ q ] ]T
    ≡⟨ (λ i → (recTy P [ recSub σ ↑𝔹 ]T) [ idS , tt ∶[ UIP q tyOftt i ] ]T) ⟩ 
  (recTy P [ recSub σ ↑𝔹 ]T) [ idS , tt ∶[ tyOftt ] ]T
    ∎
