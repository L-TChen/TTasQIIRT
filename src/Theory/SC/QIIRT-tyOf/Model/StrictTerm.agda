open import Prelude

module Theory.SC.QIIRT-tyOf.Model.StrictTerm where

open import Theory.SC.QIIRT-tyOf.Model

open import Theory.SC.QIIRT-tyOf.Model.Term
  using (Term; Ctx-is-Set)
import Theory.SC.QIIRT-tyOf.Model.Yoneda          as Y
import Theory.SC.QIIRT-tyOf.Model.LocalNoQuotient as L

Termₛ = (Y.よ Term) L.![ Ctx-is-Set ]

open Y Term using (Subʸ; _≡ʸ_; step-≡ʸ)
open L (Y.よ Term) Ctx-is-Set

open import Theory.SC.QIIRT-tyOf.Syntax as S
open S.Var

⟨_,⟩!₂≡ʸ
  : (A : Ty Δ){σʸ σ'ʸ : Subʸ Γ Δ}
  → σʸ ≡ʸ σ'ʸ → ⟨ A , σʸ ⟩! ≡ ⟨ A , σ'ʸ ⟩!
⟨ A ,⟩!₂≡ʸ {σʸ} {σ'ʸ} pʸ i = ⟨ A , (σʸ ≡ʸ⟨ pʸ ⟩ σ'ʸ ∎) i ⟩!

open import Theory.SC.QIIRT-tyOf.Rec Termₛ

▸ᶜ = recCtx
▸ᵀ = recTy
▸ᵗ = recTm
▸ˢ = recSub
▸tyOf = recTyOf
