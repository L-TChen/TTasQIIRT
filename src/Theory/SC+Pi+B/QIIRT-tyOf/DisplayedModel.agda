{-# OPTIONS --hidden-argument-puns --lossy-unification #-}

open import Prelude

open import Theory.SC+Pi+B.QIIRT-tyOf.Model
open import Theory.SC.QIIRT-tyOf.DisplayedModel

module Theory.SC+Pi+B.QIIRT-tyOf.DisplayedModel
  (M : SC+Pi+B ℓ₁' ℓ₂' ℓ₃' ℓ₄') where

private
  module S = SC+Pi+B M

open S hiding (module Var)
open S.Var hiding (C)

module _ (𝒞∙ : SC∙ 𝒞 ℓ₁ ℓ₂ ℓ₃ ℓ₄) where
  open SC∙ 𝒞∙
  open Var

  record Pi∙ : Set (ℓ-suc (ℓ₁' ⊔ ℓ₂' ⊔ ℓ₃' ⊔ ℓ₄' ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)) where
    field
      Π∙
        : (A∙ : Ty∙ Γ∙ A) (B∙ : Ty∙ (Γ∙ ,∙ A∙) B)
        → Ty∙ Γ∙ (Π A B)
      app∙
        : (t∙ : Tm∙ Γ∙ t) (B∙ : Ty∙ (Γ∙ ,∙ A∙) B)
        → (pt∙ : tyOf∙ t∙ ≡Ty[ pt ] Π∙ A∙ B∙)
        → Tm∙ (Γ∙  ,∙ A∙) (app t B pt)
      tyOfapp
        : {Γ∙ : Ctx∙ Γ} {A∙ : Ty∙ Γ∙ A}
        → (t∙ : Tm∙ Γ∙ t) (B∙ : Ty∙ (Γ∙ ,∙ A∙) B)
        → (pt∙ : tyOf∙ t∙ ≡Ty[ pt ] Π∙ A∙ B∙)
        → tyOf∙ (app∙ t∙ B∙ pt∙)
        ≡Ty[ tyOfapp pt ] B∙
      abs∙
        : (t∙ : Tm∙ (Γ∙  ,∙ A∙) t)
        → Tm∙ Γ∙ (abs t)
      tyOfabs∙
        : tyOf∙ (abs∙ t∙)
        ≡Ty[ tyOfabs ] Π∙ A∙ (tyOf∙ t∙)
      Π[]∙
        : (σ∙ : Sub∙ Γ∙ Δ∙ σ) (B∙ : Ty∙ (Δ∙ ,∙ A∙) B)
        → (Π∙ A∙ B∙) [ σ∙ ]T∙ ≡Ty[ Π[] σ B ]
        Π∙ (A∙ [ σ∙ ]T∙) (B∙ [ σ∙ ↑∙ A∙ ]T∙)
      abs[]∙
        : (σ∙ : Sub∙ Γ∙ Δ∙ σ) (t∙ : Tm∙ (Δ∙ ,∙ A∙) t)
        → abs∙ t∙ [ σ∙ ]t∙
        ≡Tm[ abs[] σ t ] abs∙ (t∙ [ σ∙ ↑∙ A∙ ]t∙)
      Πβ
        : {Γ∙ : Ctx∙ Γ} {A∙ : Ty∙ Γ∙ A}
        → (t∙ : Tm∙ (Γ∙ ,∙ A∙) t) (pt∙ : tyOf∙ (abs∙ t∙) ≡Ty[ pt ] Π∙ A∙ (tyOf∙ t∙))
        → app∙ (abs∙ t∙) _ pt∙ ≡Tm[ Πβ t pt ] t∙
      Πη∙
        : {Γ∙ : Ctx∙ Γ} {A∙ : Ty∙ Γ∙ A} {B∙ : Ty∙ (Γ∙ ,∙ A∙) B}
        → (t∙ : Tm∙ Γ∙ t) (pt∙ : tyOf∙ t∙ ≡Ty[ pt ] Π∙ A∙ B∙)
        → abs∙ (app∙ t∙ B∙ pt∙) ≡Tm[ Πη t pt ] t∙

  record Bool∙
    : Set (ℓ-suc (ℓ₁' ⊔ ℓ₂' ⊔ ℓ₃' ⊔ ℓ₄' ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)) where

    field
      𝔹∙
        : Ty∙ Γ∙ 𝔹
      𝔹[]∙
        : (σ∙ : Sub∙ Γ∙ Δ∙ σ)
        → 𝔹∙ [ σ∙ ]T∙ ≡Ty[ 𝔹[] σ ] 𝔹∙
      tt∙
        : Tm∙ Γ∙ tt
      ff∙
        : Tm∙ Γ∙ ff
      tyOftt∙
        : tyOf∙ {Γ∙ = Γ∙} tt∙ ≡Ty[ tyOftt ] 𝔹∙ [ idS∙ ]T∙
      tyOfff∙
        : tyOf∙ {Γ∙ = Γ∙} ff∙ ≡Ty[ tyOfff ] 𝔹∙ [ idS∙ ]T∙
      tt[]∙
        : (σ∙ : Sub∙ Γ∙ Δ∙ σ)
        → tt∙ [ σ∙ ]t∙ ≡Tm[ tt[] σ ] tt∙
      ff[]
        : (σ∙ : Sub∙ Γ∙ Δ∙ σ)
        → ff∙ [ σ∙ ]t∙ ≡Tm[ ff[] σ ] ff∙

    𝔹[]₂∙
      : tyOf∙ (π₂∙ {Γ∙ = Γ∙ ,∙ 𝔹∙} idS∙) ≡Ty[ 𝔹[]₂ ] 𝔹∙ [ τ∙ ]T∙
    𝔹[]₂∙ {Γ∙ = Γ∙} {τ∙ = τ∙} = beginTy
     tyOf∙ (π₂∙ {Γ∙ = Γ∙ ,∙ 𝔹∙} idS∙)
       ≡Ty[ tyOfπ₂ idS ]⟨ tyOfπ₂∙ idS∙ ⟩
     𝔹∙ [ π₁∙ idS∙ ]T∙
       ≡Ty[ 𝔹[] _ ]⟨ 𝔹[]∙ _ ⟩
     𝔹∙
       ≡Ty[ sym (𝔹[] _) ]⟨ symP (𝔹[]∙ _) ⟩
     𝔹∙ [ τ∙ ]T∙
       ∎

    _↑𝔹∙
      : (σ∙ : Sub∙ Γ∙ Δ∙ σ)
      → Sub∙ (Γ∙ ,∙ 𝔹∙) (Δ∙ ,∙ 𝔹∙) (σ ↑𝔹)
    σ∙ ↑𝔹∙ = (σ∙ ∘∙ π₁∙ idS∙) , π₂∙ idS∙ ∶[ _ , 𝔹[]₂∙ {τ∙ = σ∙ ∘∙ π₁∙ idS∙} ]∙

    field
      elim𝔹∙
        : {P : Ty (Γ ,C 𝔹)} (P∙ : Ty∙ (Γ∙ ,∙ 𝔹∙) P)
        → {t : Tm Γ} (t∙ : Tm∙ Γ∙ t) {pt : tyOf t ≡ (P [ idS , tt ∶[ tyOftt ] ]T)}
          (pt∙ : tyOf∙ t∙ ≡Ty[ pt ] (P∙ [ idS∙ , tt∙ ∶[ tyOftt , tyOftt∙ ]∙ ]T∙))
        → {u : Tm Γ} (u∙ : Tm∙ Γ∙ u) {pu : tyOf u ≡ (P [ idS , ff ∶[ tyOfff ] ]T)}
          (pu∙ : tyOf∙ u∙ ≡Ty[ pu ] (P∙ [ idS∙ , ff∙ ∶[ tyOfff , tyOfff∙ ]∙ ]T∙))
        → {b : Tm Γ} (b∙ : Tm∙ Γ∙ b) {pb : tyOf b ≡ 𝔹 [ idS ]T} (pb∙ : tyOf∙ b∙ ≡Ty[ pb ] 𝔹∙ [ idS∙ ]T∙)
        → Tm∙ Γ∙ (elim𝔹 P t pt u pu b pb)
      tyOfelim𝔹∙
        : {P : Ty (Γ ,C 𝔹)} (P∙ : Ty∙ (Γ∙ ,∙ 𝔹∙) P)
        → {t : Tm Γ} (t∙ : Tm∙ Γ∙ t) {pt : tyOf t ≡ (P [ idS , tt ∶[ tyOftt ] ]T)}
          (pt∙ : tyOf∙ t∙ ≡Ty[ pt ] (P∙ [ idS∙ , tt∙ ∶[ tyOftt , tyOftt∙ ]∙ ]T∙))
        → {u : Tm Γ} (u∙ : Tm∙ Γ∙ u) {pu : tyOf u ≡ (P [ idS , ff ∶[ tyOfff ] ]T)}
          (pu∙ : tyOf∙ u∙ ≡Ty[ pu ] (P∙ [ idS∙ , ff∙ ∶[ tyOfff , tyOfff∙ ]∙ ]T∙))
        → {b : Tm Γ} (b∙ : Tm∙ Γ∙ b) {pb : tyOf b ≡ 𝔹 [ idS ]T} (pb∙ : tyOf∙ b∙ ≡Ty[ pb ] 𝔹∙ [ idS∙ ]T∙)
        → tyOf∙ (elim𝔹∙ P∙ t∙ pt∙ u∙ pu∙ b∙ pb∙)
        ≡Ty[ tyOfelim𝔹 P t pt u pu b pb ]
          P∙ [ idS∙ , b∙ ∶[ pb , pb∙ ]∙ ]T∙
      elim𝔹[]∙
        : {P : Ty (Γ ,C 𝔹)} (P∙ : Ty∙ (Γ∙ ,∙ 𝔹∙) P)
        → {t : Tm Γ} (t∙ : Tm∙ Γ∙ t) {pt : tyOf t ≡ (P [ idS , tt ∶[ tyOftt ] ]T)}
          (pt∙ : tyOf∙ t∙ ≡Ty[ pt ] (P∙ [ idS∙ , tt∙ ∶[ tyOftt , tyOftt∙ ]∙ ]T∙))
        → {u : Tm Γ} (u∙ : Tm∙ Γ∙ u) {pu : tyOf u ≡ (P [ idS , ff ∶[ tyOfff ] ]T)}
          (pu∙ : tyOf∙ u∙ ≡Ty[ pu ] (P∙ [ idS∙ , ff∙ ∶[ tyOfff , tyOfff∙ ]∙ ]T∙))
        → {b : Tm Γ} (b∙ : Tm∙ Γ∙ b) {pb : tyOf b ≡ 𝔹 [ idS ]T} (pb∙ : tyOf∙ b∙ ≡Ty[ pb ] 𝔹∙ [ idS∙ ]T∙)
        → {pt₂ : tyOf (t [ σ ]t) ≡ P [ σ ↑𝔹 ]T [ idS , tt ∶[ tyOftt ] ]T}
          (pt₂∙ : tyOf∙ (t∙ [ σ∙ ]t∙) ≡Ty[ pt₂ ] P∙ [ σ∙ ↑𝔹∙ ]T∙ [ idS∙ , tt∙ ∶[ tyOftt , tyOftt∙ ]∙ ]T∙)
        → {pu₂ : tyOf (u [ σ ]t) ≡ P [ σ ↑𝔹 ]T [ idS , ff ∶[ tyOfff ] ]T}
          (pu₂∙ : tyOf∙ (u∙ [ σ∙ ]t∙) ≡Ty[ pu₂ ] P∙ [ σ∙ ↑𝔹∙ ]T∙ [ idS∙ , ff∙ ∶[ tyOfff , tyOfff∙ ]∙ ]T∙)
        → {pb₂ : tyOf (b [ σ ]t) ≡ 𝔹 [ idS ]T}
          (pb₂∙ : tyOf∙ (b∙ [ σ∙ ]t∙) ≡Ty[ pb₂ ] 𝔹∙ [ idS∙ ]T∙)
        → {p : (P [ idS , b ∶[ pb ] ]T [ σ ]T) ≡ (P [ (σ ∘ π₁ idS) , π₂ idS ∶[ 𝔹[]₂ ] ]T [ idS , b [ σ ]t ∶[ pb₂ ] ]T)}
        → (P∙ [ idS∙ , b∙ ∶[ pb , pb∙ ]∙ ]T∙ [ σ∙ ]T∙)
        ≡Ty[ p ] (P∙ [ (σ∙ ∘∙ π₁∙ idS∙) , π₂∙ idS∙ ∶[ 𝔹[]₂ , 𝔹[]₂∙ ]∙ ]T∙ [ idS∙ , b∙ [ σ∙ ]t∙ ∶[ pb₂ , pb₂∙ ]∙ ]T∙)
        → (elim𝔹∙ P∙ t∙ pt∙ u∙ pu∙ b∙ pb∙ [ σ∙ ]t∙) -- (elim𝔹∙ P∙ t∙ pt∙ u∙ pu∙ b∙ pb∙) [ σ∙ ]t∙
        ≡Tm[ elim𝔹[] P t pt u pu b pb pt₂ pu₂ pb₂ p ]
          elim𝔹∙ (P∙ [ σ∙ ↑𝔹∙ ]T∙) (t∙ [ σ∙ ]t∙) pt₂∙ (u∙ [ σ∙ ]t∙) pu₂∙ (b∙ [ σ∙ ]t∙) pb₂∙

record SC+Pi+B∙ (ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level)
  : Set (ℓ-suc (ℓ₁' ⊔ ℓ₂' ⊔ ℓ₃' ⊔ ℓ₄' ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)) where

  field
    𝒞∙  : SC∙ 𝒞 ℓ₁ ℓ₂ ℓ₃ ℓ₄
    𝒫i∙ : Pi∙ 𝒞∙
    ℬ∙  : Bool∙ 𝒞∙

  open SC∙ 𝒞∙    public
  open Pi∙ 𝒫i∙   public
  open Bool∙ ℬ∙  public

  open Var
