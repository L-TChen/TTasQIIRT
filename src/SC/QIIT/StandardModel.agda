-- Standard Model
module SC.QIIT.StandardModel (⟦U⟧ : Set) where

open import Prelude
open import SC.QIIT.Base
open import SC.QIIT.Model
open import SC.QIIT.Elimination

StdDecl : Pdc
StdDecl = record
  {
    PCtx = λ _ → Set
  ; PTy  = λ ⟦Γ⟧ _ → ⟦Γ⟧ → Set
  ; PSub = λ ⟦Δ⟧ ⟦Γ⟧ _ → ⟦Δ⟧ → ⟦Γ⟧
  ; PTm  = λ ⟦Γ⟧ ⟦A⟧ _ → (γ : ⟦Γ⟧) → ⟦A⟧ γ
  }

StdM : IH StdDecl
StdM .IH._[_]P ⟦A⟧ ⟦σ⟧ δ = ⟦A⟧ (⟦σ⟧ δ)
StdM .IH.∅Ctx = ⊤
StdM .IH._‣Ctx_ ⟦Γ⟧ ⟦A⟧ = Σ ⟦Γ⟧ ⟦A⟧
StdM .IH.∅Sub = λ _ → tt
StdM .IH._‣Sub_ ⟦σ⟧ ⟦t⟧ δ = ⟦σ⟧ δ , ⟦t⟧ δ
StdM .IH.PidS = λ δ → δ
StdM .IH._∘P_ ⟦σ⟧ ⟦τ⟧ θ = ⟦σ⟧ (⟦τ⟧ θ)
StdM .IH.π₁P ⟦σ⟧ δ = proj₁ (⟦σ⟧ δ)
StdM .IH.PU _ = ⟦U⟧
StdM .IH.π₂P ⟦σ⟧ δ = proj₂ (⟦σ⟧ δ)
StdM .IH._[_]tmP ⟦t⟧ ⟦σ⟧ δ = ⟦t⟧ (⟦σ⟧ δ)
StdM .IH.PU[] {σ = σ} ⟦σ⟧ =
    tr _ (U[] σ) (λ _ → ⟦U⟧)
  ≡⟨ tr-conv (U[] σ) ⟩
    conv (cong _ (U[] σ)) (λ _ → ⟦U⟧)
  ≡⟨ conv-unique (cong _ (U[] σ)) refl _ ⟩
    (λ _ → ⟦U⟧)
  ∎
StdM .IH.P[idS] {A = A} ⟦A⟧ = 
    tr _ ([idS] A) ⟦A⟧
  ≡⟨ tr-conv ([idS] A) ⟩
    conv (cong _ ([idS] A)) ⟦A⟧
  ≡⟨ conv-unique (cong _ ([idS] A)) refl ⟦A⟧ ⟩
    ⟦A⟧
  ∎
StdM .IH.P[∘] {A = A} {σ} {τ} ⟦A⟧ ⟦σ⟧ ⟦τ⟧ =
    tr _ ([∘] A σ τ) (λ δ → ⟦A⟧ (⟦σ⟧ (⟦τ⟧ δ)))
  ≡⟨ tr-conv ([∘] A σ τ) ⟩
    conv (cong _ ([∘] A σ τ)) (λ δ → ⟦A⟧ (⟦σ⟧ (⟦τ⟧ δ)))
  ≡⟨ conv-unique (cong _ ([∘] A σ τ)) refl _ ⟩
    (λ δ → ⟦A⟧ (⟦σ⟧ (⟦τ⟧ δ)))
  ∎

open elim StdDecl StdM

⟦_⟧C : Ctx → Set
⟦_⟧T : Ty Γ → ⟦ Γ ⟧C → Set
⟦_⟧C = ElimCtx
⟦_⟧T = ElimTy 

⟦_⟧S : Sub Δ Γ → ⟦ Δ ⟧C → ⟦ Γ ⟧C
⟦_⟧t : Tm Γ A → (γ : ⟦ Γ ⟧C) → ⟦ A ⟧T γ
⟦_⟧S = ElimSub
⟦_⟧t = ElimTm