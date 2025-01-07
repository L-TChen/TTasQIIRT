-- Elimination of Substitution Calculus
module SC+U+Pi.QIIRT.Elimination where

open import Prelude
  hiding (_,_)
open import SC+U+Pi.QIIRT.Base
open import SC+U+Pi.QIIRT.Model
open import SC+U+Pi.QIIRT.Properties

module elim {ℓ ℓ′}(M : Model {ℓ} {ℓ′}) where
  open Model M
  open ≡-Reasoning

  {-# TERMINATING #-}
  ElimCtx : (Γ : Ctx) → PCtx Γ
  ElimTy : (A : Ty Γ i) → PTy (ElimCtx Γ) i A
  ElimSub : (σ : Sub Δ Γ) → PSub (ElimCtx Δ) (ElimCtx Γ) σ
  ElimTm : (t : Tm Γ A) → PTm (ElimCtx Γ) (ElimTy A) t

  ElimTy[] : (σ : Sub Δ Γ)(A : Ty Γ i) → [ ElimSub σ ]P ElimTy A ≡ ElimTy ([ σ ] A)
  ElimTm[] : {A : Ty Γ i}(σ : Sub Δ Γ)(t : Tm Γ A) → tr PTmFamₜ (ElimTy[] σ A) ([ ElimSub σ ]tP ElimTm t) ≡ ElimTm ([ σ ]t t)
  
  ElimCtx ∅ = ∅Ctx
  ElimCtx (Γ , A) = ElimCtx Γ ,Ctx ElimTy A
  ElimTy (U i) = PU i
  ElimTy (Π A B) = PΠ (ElimTy A) (ElimTy B)
  ElimTy (El u) = PEl (ElimTm u)
  ElimSub ∅ = ∅Sub
  ElimSub {Δ} (_,_ σ {A} t) = ElimSub σ ,Sub tr PTmFamₜ (sym $ ElimTy[] σ A) (ElimTm t)
  ElimSub idS = PidS
  ElimSub (τ ⨟ σ) = ElimSub τ ⨟P ElimSub σ
  ElimSub (π₁ σ) = π₁P (ElimSub σ)
  ElimTm {Γ} (π₂ {A = A} σ) = tr PTmFamₜ (ElimTy[] (π₁ σ) A) (π₂P (ElimSub σ))
  ElimTm {Γ} ([_]tm_ σ {A} t) = tr PTmFamₜ (ElimTy[] σ A) ([ ElimSub σ ]tmP ElimTm t)
  ElimTm (c A) = cP (ElimTy A)
  ElimTm (ƛ t) = ƛP (ElimTm t)
  ElimTm (app t) = appP (ElimTm t)

  ElimSub↑ : (σ : Sub Δ Γ)(A : Ty Γ i) → tr (λ PB → PSub (ElimCtx Δ ,Ctx PB) (ElimCtx Γ ,Ctx ElimTy A) (σ ↑ A))
                                            (ElimTy[] σ A)
                                            (ElimSub σ ↑P ElimTy A)
                                         ≡ ElimSub (σ ↑ A) -- ElimSub (σ ↑ A)

  ElimTy[] σ (U i) = PU[]
  ElimTy[] σ (El u) = begin
    [ ElimSub σ ]P ElimTy (El u)
      ≡⟨ PEl[] (ElimSub σ) (ElimTm u) ⟩
    PEl (tr PTmFamₜ PU[] ([ ElimSub σ ]tP ElimTm u))
      ≡⟨ cong PEl (ElimTm[] σ u) ⟩
    PEl (ElimTm ([ σ ]t u))
      ∎
  ElimTy[] {Δ} {Γ} {i} σ (Π A B) = begin
    [ ElimSub σ ]P PΠ (ElimTy A) (ElimTy B)
      ≡⟨ PΠ[] (ElimSub σ) ⟩
    PΠ ([ ElimSub σ ]P ElimTy A) ([ ElimSub σ ↑P ElimTy A ]P ElimTy B)
      ≡⟨ apd₂ PΠ (ElimTy[] σ A) eq ⟩
    PΠ (ElimTy ([ σ ] A)) (ElimTy ([ σ ↑ A ] B))
      ∎
    where
      eq : tr (λ PB → PTy (ElimCtx Δ ,Ctx PB) i ([ σ ↑ A ] B))
               (ElimTy[] σ A)
               ([ ElimSub σ ↑P ElimTy A ]P ElimTy B)
          ≡ ElimTy ([ σ ↑ A ] B)
      eq = begin
        tr (λ PB → PTy (ElimCtx Δ ,Ctx PB) i ([ σ ↑ A ] B))
           (ElimTy[] σ A)
           ([ ElimSub σ ↑P ElimTy A ]P ElimTy B)
          ≡⟨ tr-nat (λ PB → PSub (ElimCtx Δ ,Ctx PB) (ElimCtx Γ ,Ctx ElimTy A) (σ ↑ A))
                    (λ _ Pσ → [ Pσ ]P ElimTy B)
                    (ElimTy[] σ A) ⟩
        [ tr (λ PB → PSub (ElimCtx Δ ,Ctx PB) (ElimCtx Γ ,Ctx ElimTy A) (σ ↑ A))
             (ElimTy[] σ A)
             (ElimSub σ ↑P ElimTy A) ]P ElimTy B
          ≡⟨ cong ([_]P ElimTy B) (ElimSub↑ σ A) ⟩
        [ ElimSub (σ ↑ A) ]P ElimTy B
          ≡⟨ ElimTy[] (σ ↑ A) B ⟩
        ElimTy ([ σ ↑ A ] B)
          ∎
  
  ElimSub↑ {Δ} {Γ} {i} σ A = begin
    tr (λ PB → PSub (ElimCtx Δ ,Ctx PB) (ElimCtx Γ ,Ctx ElimTy A) (σ ↑ A))
       (ElimTy[] σ A)
       (ElimSub σ ↑P ElimTy A)
      ≡⟨ cong (tr _ _) {! flip-tr  !} ⟩
    {!   !}

  ElimTm[] σ t = {!   !}

