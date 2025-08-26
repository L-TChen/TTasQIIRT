{-
  Agda does not support interleaved function definitions, so we add
  equations that are needed in between definitions and defined
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

recTm⟨π₂idS⟩≡π₂idS
  : recTm (S.π₂ {A = A} S.idS) ≡  π₂ idS
recTm⟨t[σ]⟩=recTmt[recSubσ]t
  : recTm (t S.[ σ ]) ≡ recTm t [ recSub σ ]t
recTmπ=πrecTm
  : (a : S.Tm Γ) (pa : S.tyOf a ≡ S.U) (pa' : tyOf (recTm a) ≡ U)
  → (b : S.Tm (Γ S., S.El a pa)) (pb : S.tyOf b ≡ S.U) 
  → (b' : Tm (recCtx Γ ,C El (recTm a) pa'))
    (b=b' : PathP (λ p → Tm (recCtx Γ ,C El (recTm a) {!recTm b!})) {!!} b')
  → (pb' : tyOf b' ≡ U)
  → recTm (S.π a pa b pb) ≡ π (recTm a) pa' b' pb'

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
recTy (S.El[]₂ {Δ} {Γ} {σ} u pu pu' i) =   (
  recTy ((S.El (u S.[ σ ]) pu') S.[ S.π₁ {A = S.El (u S.[ σ ]) pu'} S.idS ])
    ≡⟨⟩
  El (recTm (u S.[ σ ])) (recTyOf (u S.[ σ ]) pu') [ recSub (S.π₁ {A = S.El (u S.[ σ ]) pu'} S.idS) ]T
    ≡⟨⟩
  {!!} -- El {!!} {!!} [ recSub (S.π₁ {A = S.El (u S.[ σ ]) pu'} S.idS) ]T
    ≡⟨ {!!} ⟩ 
  El (recTm u) (recTyOf u pu) [ recSub σ ∘ π₁ idS ]T
    ∎) i  

recTy {Γ} (S.Π[] {Δ} {A} {B} {_} {σ} i) = 
  Π[] {_} {recTy A} {recTy B} {_} {recSub σ} i

recTy S.𝔹         = 𝔹
recTy (S.𝔹[] {σ = σ} i) =
  𝔹[] {σ = recSub σ} i
recTy (S.𝔹[]₂ {τ = τ} i) = 
  (𝔹 [ π₁ idS ]T
    ≡⟨ 𝔹[] ⟩
  𝔹
    ≡⟨ sym 𝔹[] ⟩
  𝔹 [ recSub τ ]T
    ∎) i
recTy (S.El𝕓 i) = (
  El 𝕓 (tyOf𝕓 ∙ (λ _ → U))
    ≡⟨ cong (El 𝕓) (UIP _ _) ⟩
  El 𝕓 tyOf𝕓
    ≡⟨ El𝕓 ⟩
  𝔹 ∎
  ) i
recTy (S.tyOfπ a pa b pb i) = U
recTy (S.Elπ a pa b pb i) = (
  El (recTm (S.π a pa b pb))
    (recTyOf (S.π a pa b pb) (S.tyOfπ a pa b pb))
    ≡⟨ (λ i → El {!π (recTm a) (recTyOf a pa) (recTm b) (recTyOf b pb)!} (UIP {!!} {!!} i)) ⟩
  El (π (recTm a) (recTyOf a pa) (recTm b) (recTyOf b pb))
    (tyOfπ (recTm a) (recTyOf a pa) (recTm b) (recTyOf b pb))
    ≡⟨ Elπ (recTm a) (recTyOf a pa) (recTm b) (recTyOf b pb) ⟩
  Π (recTy (S.El a pa)) (recTy (S.El b pb))
    ∎
   ) i
-- recTy (S.Ty-is-set A A₁ x y i i₁) = {!!}

recSub⟨π₁,⟩≡π₁,
  : (σ : S.Sub Γ Δ) (A : S.Ty Δ) (p : S.tyOf t ≡ A S.[ σ ])
  → recTy A [ π₁ (recSub σ , recTm t ∶[ recTyOf t p ]) ]T
  ≡ recTy A [ recSub (S.π₁ (σ S., t ∶[ p ])) ]T
  
recSubidS≡idS
  : recSub {Γ} S.idS ≡ idS
recSubidS,t≡idS,Subt
  : (t : S.Tm Γ) (p : S.tyOf t ≡ A S.[ S.idS ]) (q : tyOf (recTm t) ≡ recTy A [ idS ]T)
  → recSub (S.idS S., t ∶[ p ])
  ≡ idS , recTm t ∶[ q ]
  
recTm (t S.[ σ ])       = recTm t [ recSub σ ]t
recTm (S.π₂ σ)          = π₂ (recSub σ)
recTm (S.βπ₂ {A = A} σ t p _ i) = 
  βπ₂ (recSub σ) (recTm t) (recTyOf t p) i
recTm (S.[idS]t t i)    = [idS]t (recTm t) i
recTm (S.[∘]t t σ τ i)  = [∘]t (recTm t) (recSub σ) (recSub τ) i

recTm (S.app t p)   = app (recTm t) (recTyOf t p)
recTm (S.abs t)     = abs (recTm t)
recTm (S.abs[] {A = A} {σ = σ} t i) = {!
  (abs (recTm t) [ recSub σ ]t
    ≡⟨ {!!} ⟩
  abs (recTm t [ recSub (σ S.↑ A) ]t)
    ∎) i
  !}
recTm (S.Πβ t i)    = {! (
  app (abs (recTm t)) (tyOfabs ∙ {!!})
    ≡⟨ (λ i → app (abs (recTm t)) (UIP {!!} {!λ j → tyOfabs j!} i)) ⟩
  app (abs (recTm t)) tyOfabs
    ≡⟨ Πβ (recTm t) ⟩
  recTm t 
    ∎) i  
  !}
recTm (S.Πη t p i)  = {!!}

recTm S.tt = tt
recTm S.ff = ff
recTm (S.elim𝔹 P t u pt pu b pb) =
  elim𝔹 (recTy P) (recTm t) (recTm u)
    (recTyOf t pt ∙ cong (recTy P [_]T) (recSubidS,t≡idS,Subt S.tt S.[idS]T tyOftt))
    (recTyOf u pu ∙ cong (recTy P [_]T) ((recSubidS,t≡idS,Subt S.ff S.[idS]T tyOfff)))
    (recTm b) (recTyOf b pb ∙ cong (𝔹 [_]T) recSubidS≡idS)
recTm (S.tt[] i) = tt[] i
recTm (S.ff[] i) = ff[] i
recTm (S.elim𝔹[] P t t₁ pt pu t₂ pb pt₂ pu₂ pb₂ x i) = {!!}

recTm S.𝕓             = 𝕓
recTm (S.π t pt u pu) =
  π (recTm t) (recTyOf t pt) (recTm u) (recTyOf u pu)
recTm (S.𝕓[] {σ = σ} i) = 𝕓[] {σ = recSub σ} i
recTm (S.π[] {σ = σ} t pt u pu pt' pu' i) =
  (π[] (recTm t) (recTyOf t pt) (recTm u) (recTyOf u pu)
    (recTyOf (t S.[ σ ]) pt')
    {!!} -- (cong (λ p → tyOf (recTm u [ (recSub σ ∘ π₁ idS) , π₂ idS ∶[ p ] ]t)) (UIP _ _) ∙ recTyOf {!!} pu')
  ∙ {!!}) i

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
recTyOf {A = C} (S.abs {_} {A} t) p =
  (tyOfabs ∙ cong (Π (recTy A)) (recTyOf t refl)) ∙ cong recTy p
recTyOf {A = A} S.tt        p =
  tyOftt ∙ sym [idS]T ∙ cong recTy p
recTyOf {A = A} S.ff        p =
  tyOfff ∙ sym [idS]T ∙ cong recTy p
recTyOf {A = A} (S.elim𝔹 P t u pt pu t₂ pt₂) p =
  tyOfelim𝔹 (recTy P) (recTm t) (recTm u) _ _ (recTm t₂) _
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
recTmπ=πrecTm a pa pa' b pb b' b=b' pb' i =
  π (recTm a) (UIP (recTyOf a pa) pa' i) (b=b' i) {! !}
  -- dependent UIP
recSubidS≡idS = refl
recSubidS,t≡idS,Subt t p q =
  cong (idS , recTm t ∶[_]) (UIP _ _)
