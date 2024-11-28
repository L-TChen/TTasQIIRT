-- Standard Model
module SC.QIIRT.StandardModel (⟦U⟧ : Set) where

open import Prelude
open import SC.QIIRT.Base
open import SC.QIIRT.Model
open import SC.QIIRT.Elimination

open ≡-Reasoning
open Pdc
open IH
open IHEq

postulate
  fun-ext : ∀{l l'}{A : Set l}{B : A → Set l'}{f g : (a : A) → B a}
          → ((a : A) → f a ≡ g a)
          → f ≡ g

StdDecl : Pdc
StdDecl = record
  {
    PCtx = λ _ → Set
  ; PTy  = λ ⟦Γ⟧ _ → ⟦Γ⟧ → Set
  ; PSub = λ ⟦Δ⟧ ⟦Γ⟧ _ → ⟦Δ⟧ → ⟦Γ⟧
  ; PTm  = λ ⟦Γ⟧ ⟦A⟧ _ → (γ : ⟦Γ⟧) → ⟦A⟧ γ
  }

StdM : IH StdDecl
StdM ._[_]P ⟦A⟧ ⟦σ⟧ δ = ⟦A⟧ (⟦σ⟧ δ)
StdM .∅Ctx = ⊤
StdM ._‣Ctx_ ⟦Γ⟧ ⟦A⟧ = Σ ⟦Γ⟧ ⟦A⟧
StdM .∅Sub = λ _ → tt
StdM ._‣Sub_ ⟦σ⟧ ⟦t⟧ δ = ⟦σ⟧ δ , ⟦t⟧ δ
StdM .PidS = λ δ → δ
StdM ._∘P_ ⟦σ⟧ ⟦τ⟧ θ = ⟦σ⟧ (⟦τ⟧ θ)
StdM .π₁P ⟦σ⟧ δ = proj₁ (⟦σ⟧ δ)
StdM .PU _ = ⟦U⟧
StdM .π₂P ⟦σ⟧ δ = proj₂ (⟦σ⟧ δ)
StdM ._[_]tmP ⟦t⟧ ⟦σ⟧ δ = ⟦t⟧ (⟦σ⟧ δ)

StdMEq : IHEq StdDecl StdM
StdMEq .PU[] = refl
StdMEq .[PidS] {A = A} PA = 
  begin
    conv _ PA
  ≡⟨ conv-unique (congPTy StdDecl refl refl ([idS] A)) refl PA ⟩
    PA
  ∎
StdMEq .[∘P] {A = A} {σ} {τ} PA Pσ Pτ = 
  begin
    conv (congPTy StdDecl refl refl ([∘] A σ τ)) (λ δ → PA (Pσ (Pτ δ)))
  ≡⟨ conv-unique (congPTy StdDecl refl refl ([∘] A σ τ)) refl (λ δ → PA (Pσ (Pτ δ))) ⟩
    (λ δ → PA (Pσ (Pτ δ)))
  ∎
StdMEq .PidS∘P_ {σ = σ} Pσ =
  begin
    conv (congPSub StdDecl refl refl refl refl (idS∘ σ)) Pσ
  ≡⟨ conv-unique (congPSub StdDecl refl refl refl refl (idS∘ σ)) refl Pσ ⟩
    Pσ
  ∎
StdMEq ._∘PPidS {σ = σ} Pσ =
  begin
    conv (congPSub StdDecl refl refl refl refl (σ ∘idS)) Pσ
  ≡⟨ conv-unique (congPSub StdDecl refl refl refl refl (σ ∘idS)) refl Pσ ⟩
    Pσ
  ∎
StdMEq .PassocS {Pσ = Pσ} {Pτ} {Pυ} =
  begin
    conv (congPSub StdDecl refl refl refl refl assocS) (λ θ → Pσ (Pτ (Pυ θ)))
  ≡⟨ conv-unique (congPSub StdDecl refl refl refl refl assocS) refl (λ θ → Pσ (Pτ (Pυ θ))) ⟩
    (λ θ → Pσ (Pτ (Pυ θ)))
  ∎
StdMEq .‣∘P {A = A} {σ} {t} {τ} {PΓ} {PΘ = PΘ} {PA = PA} {Pσ} {Pt} {Pτ} =
  begin
    conv (congPSub StdDecl refl refl refl refl ‣∘) (λ θ → Pσ (Pτ θ) , Pt (Pτ θ))
  ≡⟨ conv-unique (congPSub StdDecl refl refl refl refl ‣∘) refl (λ θ → Pσ (Pτ θ) , Pt (Pτ θ)) ⟩
    (λ θ → Pσ (Pτ θ) , Pt (Pτ θ))
  ≡⟨ {!   !} ⟩
    {!   !}

StdMEq .Pβπ₁ {Pσ = Pσ} =
  begin
    conv (congPSub StdDecl refl refl refl refl βπ₁) Pσ
  ≡⟨ conv-unique (congPSub StdDecl refl refl refl refl βπ₁) refl Pσ ⟩
    Pσ
  ∎
StdMEq .Pηπ {Pσ = Pσ} =
  begin
    conv (congPSub StdDecl refl refl refl refl ηπ) Pσ
  ≡⟨ conv-unique (congPSub StdDecl refl refl refl refl ηπ) refl Pσ ⟩
    Pσ
  ≡⟨⟩
    (λ δ → proj₁ (Pσ δ) , proj₂ (Pσ δ))
  ∎
StdMEq .Pη∅ {Pσ = Pσ} = refl

open elim StdDecl StdM StdMEq

⟦_⟧C : Ctx → Set
⟦_⟧T : Ty Γ → ⟦ Γ ⟧C → Set
⟦_⟧C = ElimCtx
⟦_⟧T = ElimTy 

⟦_⟧S : Sub Δ Γ → ⟦ Δ ⟧C → ⟦ Γ ⟧C
⟦_⟧t : Tm Γ A → (γ : ⟦ Γ ⟧C) → ⟦ A ⟧T γ
⟦_⟧S = ElimSub
⟦_⟧t = ElimTm
