open import Prelude

open import Theory.SC.QIIRT-tyOf.Model

module Theory.SC.QIIRT-tyOf.Rec (C : SC ℓ₁ ℓ₂ ℓ₃ ℓ₄) where
-- module Theory.SC.QIIRT-tyOf.Rec (C : SC ℓ ℓ ℓ ℓ) where

open SC C

import Theory.SC.QIIRT-tyOf.Syntax as S
open S.Var

{-
data Tag : Set where
  ctx tm ty tyof sub : Tag

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
rec ty (S.U[] {Γ} {Δ} {σ} i) = U[] {rec ctx Γ} {rec ctx Δ} {rec sub σ} i
rec ty (A S.[ σ ])       = (rec ty A) [ rec sub σ ]T
rec ty (S.[idS]T {Γ} {A} i) = [idS]T {rec ctx Γ} {rec ty A} i
rec ty (S.[∘]T A σ τ i)     = [∘]T (rec ty A) (rec sub σ) (rec sub τ) i
rec ty S.U                  = U
rec tm (t S.[ σ ])          = rec tm t [ rec sub σ ]t
rec tm (S.π₂ σ)             = π₂ (rec sub σ)
rec tm (S.βπ₂ σ t p q i)    = βπ₂ (rec sub σ) (rec tm t) {! rec tyof t p !} i
rec tm (S.[idS]t t i) = [idS]t (rec tm t) i
rec tm (S.[∘]t t σ τ i) = [∘]t (rec tm t) (rec sub σ) (rec sub τ) i
rec tyof (t S.[ σ ]) pt = {!!} -- tyOf[] ∙ cong _[ rec sub σ ]T (rec tyof t refl) ∙ cong (rec ty) pt
rec tyof (S.π₂ σ) pt    = {!!}
rec tyof (S.βπ₂ σ t p q i) pt = {!!}
rec tyof (S.[idS]t t i) pt = {!!}
rec tyof (S.[∘]t t σ τ i) pt = {!!}
rec sub S.∅              = ∅S
rec sub S.idS            = idS
rec sub (σ S.∘ τ) = rec sub σ ∘ rec sub τ
rec sub (S.π₁ σ)  = π₁ (rec sub σ)
rec sub (S.βπ₁ σ t p i)      = βπ₁ (rec sub σ) (rec tm t) {! rec tyof t p !} i
rec sub ((S.idS∘ σ) i)       = (idS∘ rec sub σ) i
rec sub ((σ S.∘idS) i)       = (rec sub σ ∘idS) i
rec sub (S.assocS σ σ₁ σ₂ i) = assocS (rec sub σ) (rec sub σ₁) (rec sub σ₂) i
rec sub (S.,∘ σ t σ₁ p q i)  = {!!}
-- ,∘ (rec sub σ) (rec tm t) (rec sub σ₁) (rec tyOf t p) {!rec tyOf ? q!} {!!}
rec sub (S.η∅ σ i) = {!!}
rec sub (S.ηπ σ i) = {!!}
rec sub (S._,_∶[_] {Γ} {Δ} {A} σ t p) = _,_∶[_] {rec ctx Γ} {rec ctx Δ} {rec ty A} (rec sub σ) (rec tm t) {! rec tyof t p !}

recCtx  = rec ctx
recSub  = rec sub
recTy   = rec ty
recTm   = rec tm
recTyOf = rec tyof
-}

recCtx  : S.Ctx → Ctx
recTy   : S.Ty Γ → Ty (recCtx Γ)
recTm   : S.Tm Γ → Tm (recCtx Γ)
recSub  : S.Sub Γ Δ → Sub (recCtx Γ) (recCtx Δ)
-- recTyOf : (t : S.Tm Γ) → S.tyOf t ≡ A → tyOf (recTm t) ≡ recTy A
recTyOf : (t : S.Tm Γ) → tyOf (recTm t) ≡ recTy (S.tyOf t)

recCtx S.∅ = ∅
recCtx (Γ S., A) = recCtx Γ ,C recTy A

recTy (A S.[ σ ]) = recTy A [ recSub σ ]T
recTy S.U         = U
recTy (S.[idS]T {A = A} i) = [idS]T {A = recTy A} i
recTy (S.[∘]T A σ τ i)     = [∘]T (recTy A) (recSub σ) (recSub τ) i
recTy (S.U[] {σ = σ} i)    = U[] {σ = recSub σ} i
recTy (S.Ty-is-set A B p q i j) =
  isSet→SquareP (λ _ _ → Ty-is-set) (λ i → recTy (p i)) (λ i → recTy (q i)) refl refl i j

recTm (t S.[ σ ])       = recTm t [ recSub σ ]t
recTm (S.π₂ σ)          = π₂ (recSub σ)
recTm (S.βπ₂ {A = A} σ t p _ i) =
  {!!} -- βπ₂ (recSub σ) (recTm t) (recTyOf t p) i
recTm (S.[idS]t t i)    = [idS]t (recTm t) i
recTm (S.[∘]t t σ τ i)  = [∘]t (recTm t) (recSub σ) (recSub τ) i
recTm (S.Tm-is-set t u p q i j) =
  Tm-is-set (recTm t) (recTm u) (cong recTm p) (cong recTm q) i j

recSub S.∅              = ∅S
recSub (σ S., t ∶[ p ]) = recSub σ , recTm t ∶[ {!recTyOf t ?!} ] -- recTyOf t p
recSub S.idS            = idS
recSub (τ S.∘ σ)        = recSub τ ∘ recSub σ
recSub (S.π₁ σ)         = π₁ (recSub σ)
recSub (S.βπ₁ σ t p i)  = βπ₁ (recSub σ) (recTm t) {!recTyOf t !} i -- (recTyOf t p) i
recSub ((S.idS∘ σ) i)   = (idS∘ recSub σ) i
recSub ((σ S.∘idS) i)   = (recSub σ ∘idS) i
recSub (S.assocS σ τ γ i) = assocS (recSub σ) (recSub τ) (recSub γ) i
recSub (S.η∅ σ i) = η∅ (recSub σ) i
recSub (S.ηπ {Γ} {Δ} {A} σ i) =
   (ηπ (recSub σ) ∙ cong (π₁ (recSub σ) , π₂ (recSub σ) ∶[_])
                        (Ty-is-set _ _ (tyOfπ₂ (recSub σ))
                                      (tyOfπ₂ (recSub σ) ∙ (λ i₁ → recTy A [ π₁ (recSub σ) ]T)))) i 
recSub (S.,∘ {A = A} τ t σ p q i) =
  {!!} -- ,∘ (recSub τ) (recTm t) (recSub σ) (recTyOf t p) (recTyOf (t S.[ σ ]) q) i
-- -- The following fails to pass the termination checker in SetModel.agda
-- --      (recSub τ , recTm t ∶[ recTyOf t p ]) ∘ recSub σ
-- --        ≡⟨ ,∘ (recSub τ) (recTm t) (recSub σ) (recTyOf t p) ⟩
-- --      (recSub τ ∘ recSub σ) , recTm t [ recSub σ ]t ∶[ _ ]
-- --       ≡[ i ]⟨ ((recSub τ ∘ recSub σ) , recTm t [ recSub σ ]t ∶[ Tyᴬ-is-set _ _ (step-≡ (tyOfᴬ (recTm t [ recSub σ ]t))
-- --                                                           (≡⟨⟩-syntax (tyOfᴬ (recTm t) [ recSub σ ]T)
-- --                                                            (step-≡ ((recTy A [ recSub τ ]T) [ recSub σ ]T)
-- --                                                             ((recTy A [ recSub τ ∘ recSub σ ]T) ∎)
-- --                                                             ([∘]T (recTy A) (recSub σ) (recSub τ)))
-- --                                                            (λ i₁ → recTyOf t p i₁ [ recSub σ ]T))
-- --                                                           tyOf[]) (recTyOf (t [ σ ]) q) i ]) ⟩
-- --      (recSub τ ∘ recSub σ) , recTm t [ recSub σ ]t ∶[ recTyOf (t [ σ ]) q ]
-- --        ∎
recSub (S.Sub-is-set σ σ' p q i j) =
  isSet→SquareP (λ _ _ → Sub-is-set) (λ i → recSub (p i)) (λ i → recSub (q i)) refl refl i j

recTyOf (t S.[ σ ])        = 
   tyOf[] ∙ (λ i → (recTyOf t) i [ recSub σ ]T)
recTyOf (S.π₂ σ)           = tyOfπ₂ (recSub σ)
recTyOf (S.βπ₂ σ t p₁ q i) =
-- Ideally we shouldn't have to deal with these coherence proofs as they should hold in set-level cubical type theory.
  isProp→PathP {B =  λ i → tyOf (recTm (S.βπ₂ σ t p₁ q i)) ≡ recTy (S.tyOf (S.βπ₂ σ t p₁ q i))} ((λ _ → Ty-is-set _ _)) (tyOfπ₂ (recSub σ , recTm t ∶[ _ ])) (recTyOf t) i
recTyOf (S.[idS]t t i) = {!!}
recTyOf (S.[∘]t t σ τ i) = {!!}
recTyOf (S.Tm-is-set t t₁ x y i i₁) = {!!}
-- recTyOf {A = A} (t S.[ σ ]) p =
--   tyOf[] ∙ cong _[ recSub σ ]T (recTyOf t refl) ∙ cong recTy p
-- 
-- recTyOf {A = A} (S.π₂ {Γ} {Δ} {B} σ) p = tyOfπ₂ (recSub σ) ∙ cong recTy p
--  tyOf (recTm (S.π₂ σ))
--    ≡⟨ tyOfπ₂ (recSub σ) ⟩
--  recTy B [ π₁ (recSub σ) ]T
--    ≡[ i ]⟨ recTy (p i) ⟩
--  recTy A
--    ∎

--recTyOf {A = A} (S.βπ₂ σ t p₁ q i) =
--  isProp→PathP {B = λ i → S.tyOf (S.βπ₂ σ t p₁ q i) ≡ A → tyOf {! recTm (S.βπ₂ σ t p₁ q i) !} ≡ recTy A}
--  (λ j → isPropΠ (λ _ → Ty-is-set _ _)) {! recTyOf (S.π₂ (σ S., t ∶[ p₁ ])) !} (recTyOf t) i -- (recTyOf (S.βπ₂ σ t p₁ q i1)) i
--recTyOf {A = A} (S.[idS]t t i) =
--  isProp→PathP
--    {B = λ i → S.tyOf (S.[idS]t t i) ≡ A → tyOf {! recTm (S.[idS]t t i) !} ≡ recTy A}
--    (λ j → isPropΠ λ _ → Ty-is-set _ _)
--    (recTyOf t) -- (recTyOf (S.[idS]t t i0))
--    (λ (p : (S.tyOf t S.[ S.idS ] ≡ A)) → {!tyOf[] ∙ cong _[ idS ]T (recTyOf t refl) ∙ ?!} ) i
--    -- (recTyOf (S.[idS]t t i1)) i
--recTyOf {A = A} (S.[∘]t t σ τ i) = {!!}
----  isProp→PathP {B = λ i → S.tyOf (S.[∘]t t σ τ i) ≡ A → tyOf (recTm (S.[∘]t t σ τ i)) ≡ recTy A}
----  (λ j → isPropΠ λ _ → Ty-is-set _ _) (recTyOf (S.[∘]t t σ τ i0)) (recTyOf (S.[∘]t t σ τ i1)) i
--recTyOf {A = A} (S.Tm-is-set t u p q i j) =
-- isSet→SquareP
--   {A = λ i j → S.tyOf (S.Tm-is-set t u p q i j) ≡ A → tyOf {!recTm (S.Tm-is-set t u p q i j)!} ≡ recTy A}
--   (λ i j → isSetΠ λ _ → isProp→isSet (Ty-is-set (tyOf {! recTm (S.Tm-is-set t u p q i j)!}) (recTy A)))
--   (λ j → recTyOf (p j))
--   (λ j → recTyOf (q j))
--   (λ j → recTyOf t)
--   (λ j → recTyOf u) i j
