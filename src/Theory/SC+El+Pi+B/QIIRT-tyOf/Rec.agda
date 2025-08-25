{-# OPTIONS --hidden-argument-puns #-}
open import Prelude

open import Theory.SC+El+Pi+B.QIIRT-tyOf.Model

module Theory.SC+El+Pi+B.QIIRT-tyOf.Rec (M : SC+El+Pi+B ℓ₁ ℓ₂ ℓ₃ ℓ₄) where

open SC+El+Pi+B M

import Theory.SC+El+Pi+B.QIIRT-tyOf.Syntax as S
open S.Var

-- recCtx  : S.Ctx → Ctx
-- recTy   : S.Ty Γ → Ty (recCtx Γ)
-- recTm   : S.Tm Γ → Tm (recCtx Γ)
-- recSub  : S.Sub Γ Δ → Sub (recCtx Γ) (recCtx Δ)
-- recTyOf : (t : S.Tm Γ) → S.tyOf t ≡ A → tyOf (recTm t) ≡ recTy A

-- recCtx S.∅       = ∅
-- recCtx (Γ S., A) = recCtx Γ ,C recTy A

-- recTm⟨π₂idS⟩≡π₂idS           : recTm (S.π₂ {A = A} S.idS) ≡ π₂ idS
-- recTm⟨t[σ]⟩=recTmt[recSubσ]t : recTm (t S.[ σ ]) ≡ recTm t [ recSub σ ]t

-- recTy (A S.[ σ ]) = recTy A [ recSub σ ]T
-- recTy (S.[idS]T i) = {!!}
-- recTy (S.[∘]T A σ τ i) = {!!}
-- recTy S.U = {!!}
-- recTy (S.U[] i) = {!!}
-- -- recTy 𝔹         = 𝔹
-- -- recTy U         = U
-- -- recTy (S.El u p)  = El (recTm u) (recTyOf u p)
-- -- recTy (S.Π A B)   = Π (recTy A) (recTy B)
-- -- recTy (S.[idS]T {A = A} i) = [idS]T {A = recTy A} i
-- -- recTy (S.[∘]T A σ τ i)     = [∘]T (recTy A) (recSub σ) (recSub τ) i
-- -- recTy (S.U[] {σ = σ} i)    = U[] {σ = recSub σ} i
-- -- recTy (S.El[] τ u p q i)   = {!El[] (recSub τ) (recTm u) (recTyOf u p) i!}
-- --  where
-- --   foo : (tyOf[] ∙ cong (λ z → z [ recSub τ ]T) (recTyOf u p) ∙ U[]) ≡ {!recTyOf (u Foo.[ τ ]t) q!}
-- --   foo = {!!}
-- -- -- (El[] (recSub τ) (recTm u) (recTyOf u p) {!(cong tyOf (recTm⟨t[σ]⟩=recTmt[recSubσ]t {t = u} {σ = τ})) ∙ recTyOf (u [ τ ]) q!}) i
-- -- recTy (El[]₂ u pu pu' i) = {!!}
-- -- recTy (Π[] i) = {!!}
-- -- recTy (𝔹[] {σ = σ} i) = 𝔹[] {σ = recSub σ} i
-- -- recTy (𝔹[]₂ {Γ = Γ} {Δ} {τ = τ} i) = {!!} -- ({!cong tyOf (recTm⟨π₂idS⟩≡π₂idS {{!Γ!}} {A = 𝔹})!} ∙ 𝔹[]₂ {τ = recSub τ}) i
-- -- recTy (El𝕓 i) = {!!}
-- -- recTy (tyOfπ a pa b pb i) = {!!}
-- -- recTy (Elπ a pa b pb i) = {!!}
-- -- recTy (Ty-is-set A A₁ x y i i₁) = {!!}

-- -- recSub ∅             = ∅S
-- -- recSub (σ , t ∶[ p ]) = recSub σ , recTm t ∶[ recTyOf t p ]
-- -- recSub idS            = idS
-- -- recSub (τ ∘ σ)        = recSub τ ∘ recSub σ
-- -- recSub (π₁ σ)         = π₁ (recSub σ)
-- -- recSub (βπ₁ σ t p i)  = {!!}
-- -- recSub ((idS∘ σ) i)   = {!!}
-- -- recSub ((σ ∘idS) i)   = {!!}
-- -- recSub (assocS σ σ₁ σ₂ i) = {!!}
-- -- recSub (,∘ σ t σ₁ p q i)  = {!!}
-- -- recSub (η∅ σ i) = {!!}
-- -- recSub (ηπ σ i) = {!!}


-- -- recTm (t [ σ ]) = recTm t [ recSub σ ]t
-- -- recTm (π₂ σ)    = π₂ (recSub σ)
-- -- recTm (app t x) = {!!}
-- -- recTm (abs t)   = {!!}
-- -- recTm tt        = {!!}
-- -- recTm ff        = {!!}
-- -- recTm (elim𝔹 P t t₁ x x₁ t₂ x₂) = {!!}
-- -- recTm 𝕓 = {!!}
-- -- recTm (π t pa t₁ pb) = {!!}
-- -- recTm (βπ₂ σ t p q i) = {!!}
-- -- recTm ([idS]t t i) = {!!}
-- -- recTm ([∘]t t σ τ i) = {!!}
-- -- recTm (abs[] t i) = {!!}
-- -- recTm (Πβ t i) = {!!}
-- -- recTm (Πη t p i) = {!!}
-- -- recTm (tt[] i) = {!!}
-- -- recTm (ff[] i) = {!!}
-- -- recTm (elim𝔹[] P t t₁ pt pu t₂ pb pt₂ pu₂ pb₂ x i) = {!!}
-- -- recTm (𝕓[] i) = {!!}
-- -- recTm (π[] t pa t₁ pb pa' pb' i) = {!!}

-- -- recTm⟨π₂idS⟩≡π₂idS = refl
-- -- recTm⟨t[σ]⟩=recTmt[recSubσ]t = refl

-- -- recTyOf t p = {!!}
