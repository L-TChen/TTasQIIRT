module Theory.SC+El+Pi+B.QIIRT-tyOf.Elim where

open import Prelude
open import Agda.Primitive

open import Theory.SC+El+Pi+B.QIIRT-tyOf.Syntax

-- Recursor

module _ {ℓ ℓ' ℓ'' ℓ'''}
         (Ctxᴬ : Set ℓ)
         (Tyᴬ : Ctxᴬ → Set ℓ')
         (Subᴬ : Ctxᴬ → Ctxᴬ → Set ℓ'')
         (Tmᴬ : Ctxᴬ → Set ℓ''')
         (tyOfᴬ : {Γᴬ : Ctxᴬ} → Tmᴬ Γᴬ → Tyᴬ Γᴬ)
 where

 record Ctxᴹ : Set (ℓ ⊔ ℓ' ⊔ ℓ'' ⊔ ℓ''') where
  field
    ∅ᴹ : Ctxᴬ
    _,ᴹ_ : (Γ : Ctxᴬ) (Aᴹ : Tyᴬ Γ) → Ctxᴬ
{-
 record Tyᴹ : Set (ℓ ⊔ ℓ' ⊔ ℓ'' ⊔ ℓ''') where
  field
      _[_]ᴹ : (A : Tyᴬ Δ) (σ : Subᴬ Γ Δ)
         → Tyᴬ Γ
      [idS]Tᴹ
        : A ≡ A [ idS ]
      [∘]Tᴹ
        : (A : Tyᴬ Θ) (σ : Subᴬ Γ Δ) (τ : Subᴬ Δ Θ)
        → A [ τ ]ᴹ [ σ ]ᴹ ≡ A [ τ ∘ σ ]ᴹ
      Uᴹ
        : Tyᴬ Γ
      U[]ᴹ
        : U [ σ ]ᴹ ≡ U
      Elᴹ
        : (u : Tmᴬ Γ) (p : tyOf u ≡ U)
        → Tyᴬ Γ
      El[]ᴹ
        : (τ : Subᴬ Γ Δ) (u : Tmᴬ Δ) (p : tyOf u ≡ U) (q : tyOf (u [ τ ]t) ≡ U)
        → (El u p) [ τ ]ᴹ ≡ El (u [ τ ]t) q
      El[]₂ᴹ
        : (u : Tmᴬ Δ) (pu : tyOf u ≡ U)(puᴹ : tyOf (u [ σ ]t) ≡ U)
        → tyOf (π₂ {Γ , El (u [ σ ]t) puᴹ} idS) ≡ El u pu [ σ ∘ π₁ idS ]ᴹ
      Πᴹ
        : (A : Tyᴬ Γ) (B : Tyᴬ (Γ , A))
        → Tyᴬ Γ
      Π[]ᴹ
        : (Π A B) [ σ ]ᴹ ≡ Π (A [ σ ]ᴹ) (B [ σ ↑ A ]ᴹ)
      𝔹ᴹ
        : Tyᴬ Γ
      𝔹[]ᴹ
        : 𝔹 [ σ ]ᴹ ≡ 𝔹
      𝔹[]₂ᴹ
        : tyOf (π₂ {Γ , 𝔹} idS) ≡ 𝔹 [ τ ]ᴹ
      El𝕓ᴹ
        : El {Γ} 𝕓 tyOf𝕓 ≡ 𝔹
      tyOfπᴹ
        : (a : Tmᴬ Γ) (pa : tyOf a ≡ U) (b : Tmᴬ (Γ , El a pa)) (pb : tyOf b ≡ U)
        → tyOf (π a pa b pb) ≡ U
      Elπᴹ
        : (a : Tmᴬ Γ) (pa : tyOf a ≡ U)
        → (b : Tmᴬ (Γ , El a pa)) (pb : tyOf b ≡ U)
        → El (π a pa b pb) (tyOfπ a pa b pb) ≡ Π (El a pa) (El b pb)
      Tyᴬ-is-set : isSet (Tyᴬ Γ)
-}
module _ {ℓ ℓ' ℓ'' ℓ'''}
         (Ctxᴬ : Set ℓ)
         (Tyᴬ : Ctxᴬ → Set ℓ')
         (Subᴬ : Ctxᴬ → Ctxᴬ → Set ℓ'')
         (Tmᴬ : Ctxᴬ → Set ℓ''')
         (tyOfᴬ : {Γᴬ : Ctxᴬ} → Tmᴬ Γᴬ → Tyᴬ Γᴬ)
         (Ctxᵐ : Ctxᴹ Ctxᴬ Tyᴬ Subᴬ Tmᴬ tyOfᴬ)
 where

  open Ctxᴹ Ctxᵐ


  recCtx : Ctx → Ctxᴬ
  recTy : {Γ : Ctx} → Ty Γ → Tyᴬ (recCtx Γ)
  recTm : {Γ : Ctx} → Tm Γ → Tmᴬ (recCtx Γ)
  recSub : {Γ Δ : Ctx} → Sub Γ Δ → Subᴬ (recCtx Γ) (recCtx Δ)
  recTyOf : {Γ : Ctx} → (t : Tm Γ) → tyOfᴬ (recTm t) ≡ recTy (tyOf t)

  recCtx ∅' = ∅ᴹ
  recCtx (Γ , A) = recCtx Γ ,ᴹ recTy A

  recTy (A [ σ ]) = {!recSub σ!}
  recTy 𝔹' = {!!}
  recTy U' = {!!}
  recTy (El' u p) = {!!}
  recTy (Π' A B) = {!!}
  recTy ([idS]T' i) = {!!}
  recTy ([∘]T' A σ τ i) = {!!}
  recTy (U[]' i) = {!!}
  recTy (El[]' τ u p q i) = {!!}
  recTy (El[]₂' u pu pu' i) = {!!}
  recTy (Π[]' i) = {!!}
  recTy (𝔹[]' i) = {!!}
  recTy (𝔹[]₂' i) = {!!}
  recTy (El𝕓' i) = {!!}
  recTy (tyOfπ' a pa b pb i) = {!!}
  recTy (Elπ' a pa b pb i) = {!!}
  recTy (Ty-is-set A A₁ x y i i₁) = {!!}

  recTm t = {!!}

  recSub σ = {!!}

  recTyOf t = {!!}
