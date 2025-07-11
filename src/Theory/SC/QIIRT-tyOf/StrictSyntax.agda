module Theory.SC.QIIRT-tyOf.StrictSyntax where

open import Prelude
open import Theory.SC.QIIRT-tyOf.Model

postulate
  UIP : ∀ {ℓ} → {A : Set ℓ} → {x y : A} → isProp (x ≡ y)

module _ where
  open import Theory.SC.QIIRT-tyOf.Syntax
  open import Theory.SC.QIIRT-tyOf.Models.Term
  open import Theory.SC.QIIRT-tyOf.Models.Yoneda
  open import Theory.SC.QIIRT-tyOf.Models.LocalNoQuotient

  Ctx-is-set : isSet Ctx
  Ctx-is-set _ _ = UIP

  Termₛᵃ : Motive _ _ _ _
  Termₛᵃ = SC!ᵃ (よᵃ Termᵃ Termᵐ) (よᵐ Termᵃ Termᵐ) Ctx-is-set

  Termₛᵐ : SCᴹ Termₛᵃ
  Termₛᵐ = SC!ᵐ (よᵃ Termᵃ Termᵐ) (よᵐ Termᵃ Termᵐ) Ctx-is-set

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
  )

variable
  Γ Δ Θ Ξ : Ctxₛ
  A B C D : Tyₛ Γ
  σ τ γ : Subₛ Γ Δ
  t u v : Tmₛ Γ