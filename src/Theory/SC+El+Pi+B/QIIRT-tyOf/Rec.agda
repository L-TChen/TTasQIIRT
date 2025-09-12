{-# OPTIONS --lossy-unification #-}
{-
  Agda does not support interleaved function definitions, so we add
  equations that are needed between definitions and defined
  afterwards.
-}
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

recTy[]T
  : (σ : S.Sub Γ Δ) (A : S.Ty Δ)
  → recTy (A S.[ σ ]) ≡ recTy A [ recSub σ ]T
recTm[]t
  : (σ : S.Sub Γ Δ) (t : S.Tm Δ)
  → recTm (t S.[ σ ]) ≡ recTm t [ recSub σ ]t
recTyOf[]t
  : (σ : S.Sub Γ Δ) (t : S.Tm Δ) (p : S.tyOf (t S.[ σ ]) ≡ S.U)
  → PathP (λ i → tyOf (recTm[]t σ t i) ≡ recTy S.U)
    (recTyOf (t S.[ σ ]) p)
    (tyOf[] ∙ cong _[ recSub σ ]T (recTyOf t refl) ∙ subst (λ A → A ≡ recTy S.U) (recTy[]T σ (S.tyOf t)) (cong recTy p))

recTy (A S.[ σ ]) = recTy A [ recSub σ ]T
recTy S.U         = U
recTy (S.[idS]T {A = A} i) = [idS]T {A = recTy A} i
recTy (S.[∘]T A σ τ i)     = [∘]T (recTy A) (recSub σ) (recSub τ) i
recTy (S.U[] {σ = σ} i)    = U[] {σ = recSub σ} i

recTy (S.El u p)  = El (recTm u) (recTyOf u p)
recTy (S.Π A B)   = Π (recTy A) (recTy B)
recTy (S.El[] τ u p q i)  = 
  (El (recTm u) (recTyOf u p) [ recSub τ ]T
    ≡⟨ El[] (recSub τ) (recTm u) (recTyOf u p) ⟩
  El (recTm u [ recSub τ ]t) (tyOf[]≡U (recTyOf u p))
    ≡⟨ cong (El (recTm u [ recSub τ ]t)) (UIP _ _) ⟩
  El (recTm u [ recSub τ ]t)
    (tyOf[] ∙ (λ j → recTyOf u (λ _ → S.tyOf u) j [ recSub τ ]T) ∙ (λ j → recTy (q j)))
    ∎) i  
recTy (S.El[]₂ {Δ} {Γ} {σ} u pu pu' i) = (
  recTy ((S.El (u S.[ σ ]) pu') S.[ S.π₁ {A = S.El (u S.[ σ ]) pu'} S.idS ])
    ≡⟨⟩
  El (recTm (u S.[ σ ])) (recTyOf (u S.[ σ ]) pu') [ recSub (S.π₁ {A = S.El (u S.[ σ ]) pu'} S.idS) ]T

    ≡⟨ {!!} ⟩

  tyOf (π₂ idS)

    ≡⟨ {!El[]₂ {σ = recSub σ} (recTm u) (recTyOf u pu) !} ⟩
    -- Even this cannot be accepted, as their implicit arguments are different.
    --
    -- Goal: tyOf (π₂ idS) ≡
    --   (El (recTm u) (recTyOf u pu) [ recSub σ ∘ π₁ idS ]T)
    -- Have: tyOf (π₂ idS) ≡
    --   (El (recTm u) (recTyOf u pu) [ recSub σ ∘ π₁ idS ]T)

  El (recTm u) (recTyOf u pu) [ recSub σ ∘ π₁ idS ]T
    ∎) i  

recTy (S.Π[] σ B i) = Π[] (recSub σ) (recTy B) i

recTy S.𝔹         = 𝔹
recTy (S.𝔹[] σ i) = 𝔹[] (recSub σ) i
recTy (S.𝔹[]₂ {τ = τ} i) = (𝔹[] (π₁ idS) ∙ sym (𝔹[] (recSub τ))) i
recTy (S.El𝕓 Γ i) = (cong (El 𝕓) (UIP (tyOf𝕓 ∙ refl) _) ∙ El𝕓 _) i
recTy (S.tyOfπ a pa b pb i) = U
recTy (S.Elπ a pa b pb i) = (
  El (recTm (S.π a pa b pb))
    (recTyOf (S.π a pa b pb) (S.tyOfπ a pa b pb))
    ≡⟨ {! (λ i → El {!π (recTm a) (recTyOf a pa) (recTm b) (recTyOf b pb)!} (UIP {!!} {!!} i)) !} ⟩

  El (π (recTm a) (recTyOf a pa) (recTm b) (recTyOf b pb))
    (tyOfπ (recTm a) (recTyOf a pa) (recTm b) (recTyOf b pb))

    ≡⟨ Elπ (recTm a) (recTyOf a pa) (recTm b) (recTyOf b pb) ⟩

  Π (recTy (S.El a pa)) (recTy (S.El b pb))
    ∎
  ) i
-- recTy (S.Ty-is-set A A₁ x y i i₁) = {!!}

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
  → recSub (S.idS S., b S.[ σ ] ∶[ p ])
  ≡ (idS , recTm b [ recSub σ ]t ∶[ q ])

recSubidS,t≡idS,Subt
  : (t : S.Tm Γ) (p : S.tyOf t ≡ A S.[ S.idS ]) (q : tyOf (recTm t) ≡ recTy A [ idS ]T)
  → recSub (S.idS S., t ∶[ p ])
  ≡ idS , recTm t ∶[ q ]

recSub↑≡↑recSub
  : (σ : S.Sub Γ Δ) (A : S.Ty Δ)
  → recSub (σ S.↑ A) ≡ recSub σ ↑ recTy A

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

recTm (t S.[ σ ])       = recTm t [ recSub σ ]t
recTm (S.π₂ σ)          = π₂ (recSub σ)
recTm (S.βπ₂ {A = A} σ t p _ i) = 
  βπ₂ (recSub σ) (recTm t) (recTyOf t p) i
recTm (S.[idS]t t i)    = [idS]t (recTm t) i
recTm (S.[∘]t t σ τ i)  = [∘]t (recTm t) (recSub σ) (recSub τ) i

recTm (S.app t B p)   = app (recTm t) (recTy B) (recTyOf t p)
recTm (S.abs t)     = abs (recTm t)
recTm (S.abs[] {A = A} σ t i) = (
  abs (recTm t) [ recSub σ ]t
    ≡⟨ abs[] (recSub σ) (recTm t) ⟩
  abs (recTm t [ recSub σ ↑ recTy A ]t)
    ≡⟨ (λ i → abs (recTm t [ recSub↑≡↑recSub σ A (~ i) ]t)) ⟩ -- supposed to be definitional
  abs (recTm t [ recSub (σ S.↑ A) ]t)
    ∎) i

recTm (S.Πβ {Γ} {A = A} t p i) = (
  app (abs (recTm t)) (recTy (S.tyOf t)) (recTyOf (S.abs t) p)
    ≡⟨ cong₂ (app (abs (recTm t))) (sym $ recTyOf t refl )
      (toPathP (UIP _ _)) ⟩
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
  recTm (S.elim𝔹 P t pt u pu b pb) [ recSub σ ]t

    ≡⟨⟩

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
  recTm (S.elim𝔹 (P S.[ σ S.↑𝔹 ]) (t S.[ σ ]) pt₂ (u S.[ σ ])
    pu₂ (b S.[ σ ]) pb₂)
    ∎) i
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

recTm S.𝕓             = 𝕓
recTm (S.π t pt u pu) =
  π (recTm t) (recTyOf t pt) (recTm u) (recTyOf u pu)
recTm (S.𝕓[] σ i) = 𝕓[] (recSub σ) i
recTm (S.π[] {σ = σ} t pt u pu pt' pu' i) = {! (
-- This requires `El₂` to be done first
  π (recTm t) (recTyOf t pt) (recTm u) (recTyOf u pu) [ recSub σ ]t
    ≡⟨ π[] (recTm t) (recTyOf t pt) (recTm u) (recTyOf u pu) (recTyOf (t S.[ σ ]) pt')
      {!tyOf (recTm u [ recSub σ ↑El ]t) !}
 (cong tyOf (cong (recTm u [_]t) {!cong (λ p → (recSub σ ∘ π₁ idS) , π₂ idS ∶[ p ]) (UIP _ _)!}) ∙ {!!})
      ⟩
  π (recTm t [ recSub σ ]t) (recTyOf (t S.[ σ ]) pt') (recTm u [ recSub σ ↑El ]t)
    {!!} 
    ≡⟨ {!!} ⟩
  π (recTm t [ recSub σ ]t) (recTyOf (t S.[ σ ]) pt') (recTm u [ recSub (σ S.↑El) ]t)
    (recTyOf (u S.[ σ S.↑El ]) pu')
    ∎) !} i

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
recTyOf {A = A} (S.𝕓[] σ i) =
  isProp→PathP {B = (λ i → S.tyOf (S.𝕓[] σ i) ≡ A → tyOf (recTm (S.𝕓[] σ i)) ≡ recTy A)}
  (λ _ → isPropΠ λ _ → UIP) (recTyOf (S.𝕓[] σ i0)) (recTyOf (S.𝕓[] σ i1)) i
recTyOf {A = A} (S.π[] t pa u pu pt' pu' i) =
  isProp→PathP {B = (λ i → S.tyOf (S.π[] t pa u pu pt' pu' i) ≡ A
    → tyOf (recTm (S.π[] t pa u pu pt' pu' i)) ≡ recTy A)}
  (λ _ → isPropΠ λ _ → UIP) (recTyOf (S.π[] t pa u pu pt' pu' i0)) (recTyOf (S.π[] t pa u pu pt' pu' i1)) i

-- the following are definitions that need strict equations given above 
recTy[]T σ A = refl
recTm[]t σ t = refl
recTyOf[]t σ t p = UIP _ _

recSubidS≡idS = refl

recSubidS,t≡idS,Subt t p q =
  cong (idS , recTm t ∶[_]) (UIP _ _)

recSub,₁ p q = 
  cong (_ , _ ∶[_]) (UIP (recTyOf _ p) q)
recSub,₂ σ b p q =
  cong (_ , _ ∶[_]) (UIP (recTyOf _ p) q)

recSub,≡,Sub σ t p q =
  cong (recSub σ , recTm t ∶[_]) (UIP (recTyOf t p) q)


recSub↑≡↑recSub σ A = refl

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
