module Theory.SC.QIIRT-tyOf.StrictSyntax where

open import Prelude
open import Theory.SC.QIIRT-tyOf.Model

postulate
  UIP : ∀ {ℓ} → {A : Set ℓ} → {x y : A} → isProp (x ≡ y)

module _ where
  open import Theory.SC.QIIRT-tyOf.Syntax
  open import Theory.SC.QIIRT-tyOf.Models.Term
  import Theory.SC.QIIRT-tyOf.Models.Yoneda as Yoneda
  import Theory.SC.QIIRT-tyOf.Models.LocalNoQuotient as Local

  Ctx-is-set : isSet Ctx
  Ctx-is-set _ _ = UIP

  open Yoneda Termᵃ Termᵐ
  open Local よᵃ よᵐ Ctx-is-set

  Termₛᵃ : Motive _ _ _ _
  Termₛᵃ = SC!ᵃ

  Termₛᵐ : SCᴹ Termₛᵃ
  Termₛᵐ = SC!ᵐ

  ⟨_,⟩!₂≡ʸ
    : (A : Ty Δ){σʸ σ'ʸ : Subʸ Γ Δ}
    → σʸ ≡ʸ σ'ʸ → ⟨ A , σʸ ⟩! ≡ ⟨ A , σ'ʸ ⟩!
  ⟨ A ,⟩!₂≡ʸ {σʸ} {σ'ʸ} pʸ i = ⟨ A , (σʸ ≡ʸ⟨ pʸ ⟩ σ'ʸ ∎) i ⟩!

open Motive Termₛᵃ public
  hiding
  ( Γᴹ ; Δᴹ ; Θᴹ ; Ξᴹ
  ; Aᴹ ; Bᴹ ; Cᴹ ; Dᴹ
  ; σᴹ ; τᴹ ; γᴹ
  ; tᴹ ; uᴹ ; vᴹ
  )
  renaming
  ( Ctxᴬ  to Ctxₛ
  ; Tyᴬ   to Tyₛ
  ; Subᴬ  to Subₛ
  ; Tmᴬ   to Tmₛ
  ; tyOfᴬ to tyOfₛ
  ; Tyᴬ-is-set  to Tyₛ-is-set
  ; Subᴬ-is-set to Subₛ-is-set
  )

open SCᴹ Termₛᵐ public
  renaming
  ( ∅ᴹ to ∅ₛ
  ; _,ᴹ_ to _,ₛ_
  ; _[_]Tᴹ to _[_]ₛ
  ; _[_]tᴹ to _[_]tₛ
  ; tyOf[]ᴹ to tyOf[]ₛ
  ; ∅Sᴹ to ∅Sₛ
  ; _,ᴹ_∶[_] to _,ₛ_∶[_]
  ; idSᴹ to idSₛ
  ; _∘ᴹ_ to _∘ₛ_
  ; π₁ᴹ to π₁ₛ
  ; π₂ᴹ to π₂ₛ
  ; tyOfπ₂ᴹ to tyOfπ₂ₛ
  ; idS∘ᴹ_ to idS∘ₛ_
  ; _∘idSᴹ to _∘idSₛ
  ; assocSᴹ to assocSₛ
  ; [idS]Tᴹ to [idS]Tₛ
  ; [∘]Tᴹ to [∘]Tₛ
  ; ,∘ᴹ to ,∘ₛ
  ; ηπᴹ to ηπₛ
  ; η∅ᴹ to η∅ₛ
  ; βπ₁ᴹ to βπ₁ₛ
  ; βπ₂ᴹ to βπ₂ₛ
  ; [idS]tᴹ to [idS]tₛ
  ; [∘]tᴹ to [∘]tₛ
  ; Uᴹ to Uₛ
  ; U[]ᴹ to U[]ₛ
  ; π₁∘ᴹ to π₁∘ₛ
  ; π₂∘ᴹ to π₂∘ₛ
  ; π₁σ=π₁idS∘σᴹ to π₁idSₛ
  ; π₂σ=π₂id[σ]ᴹ to π₂idSₛ
  ; cong,∶[]ᴹ to cong,∶[]ₛ
  )

variable
  Γ Δ Θ Ξ : Ctxₛ
  A B C D : Tyₛ Γ
  σ τ γ : Subₛ Γ Δ
  t u v : Tmₛ Γ

import Theory.SC.QIIRT-tyOf.Rec as Rec
open Rec Termₛᵃ Termₛᵐ

▸ᶜ = recCtx
▸ᵀ = recTy
▸ᵗ = recTm
▸ˢ = recSub
▸tyOf = recTyOf