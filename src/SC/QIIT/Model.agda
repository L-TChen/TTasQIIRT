-- Model of Substitution Calculus
module SC.QIIT.Model where

open import Prelude
  hiding (_∘_)
open import SC.QIIT.Base

record Pdc {i j} : Set (lsuc (i ⊔ j)) where
  field
    PCtx
      : Ctx → Set i
    PTy
      : PCtx Γ → Ty Γ → Set i
    PSub
      : PCtx Δ → PCtx Γ → Sub Δ Γ → Set j
    PTm
      : (PΓ : PCtx Γ) → PTy PΓ A → Tm Γ A → Set j

record IH {i j}(P : Pdc {i} {j}) : Set (i ⊔ j) where
  open Pdc P
  field
    -- induction on type substitution
    _[_]P
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}
        (PA : PTy PΓ A)(Pσ : PSub PΔ PΓ σ)
      ------------------------------------
      → PTy PΔ (A [ σ ])
    
    -- induction on contexts
    ∅Ctx
      : PCtx ∅
    _,Ctx_
      : (PΓ : PCtx Γ)(PA : PTy PΓ A)
      ------------------------------
      → PCtx (Γ , A)
    
    -- induction on substitutions
    ∅Sub
      : {PΔ : PCtx Δ}
      ---------------
      → PSub PΔ ∅Ctx ∅
    _,Sub_
      : {PΔ : PCtx Δ}{PΓ : PCtx Γ}{PA : PTy PΓ A}
        (Pσ : PSub PΔ PΓ σ)(Pt : PTm PΔ (PA [ Pσ ]P) t)
      --------------------------------------------------
      → PSub PΔ (PΓ ,Ctx PA) (σ , t)
    PidS
      : {PΔ : PCtx Γ}
      ---------------
      → PSub PΔ PΔ idS
    _∘P_
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PΘ : PCtx Θ}
        (Pσ : PSub PΔ PΓ σ)(Pτ : PSub PΘ PΔ τ)
      -----------------------------------------
      → PSub PΘ PΓ (σ ∘ τ)
    π₁P
      : {PΔ : PCtx Δ}{PΓ : PCtx Γ}{PA : PTy PΓ A}
        (Pσ : PSub PΔ (PΓ ,Ctx PA) σ)
      -------------------------------
      → PSub PΔ PΓ (π₁ σ)
    
    -- induction on types
    PU
      : {PΓ : PCtx Γ}
      ---------------
      → PTy PΓ U
    
    -- induction on terms
    π₂P
      : {PΔ : PCtx Δ}{PΓ : PCtx Γ}{PA : PTy PΓ A}
        (Pσ : PSub PΔ (PΓ ,Ctx PA) σ)
      ---------------------------------
      → PTm PΔ (PA [ π₁P Pσ ]P) (π₂ σ)
    _[_]tP
      : {PΓ : PCtx Γ}{PA : PTy PΓ A}{PΔ : PCtx Δ}
        (Pt : PTm PΓ PA t)(Pσ : PSub PΔ PΓ σ)
      ---------------------------------------
      → PTm PΔ (PA [ Pσ ]P) (t [ σ ])

record IHEq {i j}(P : Pdc {i} {j})(indP : IH P) : Set (i ⊔ j) where
  open Pdc P
  open IH indP
  field   
    -- induction on equalities
    PU[] 
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}(Pσ : PSub PΔ PΓ σ)
      -----------------------------------------------
      → tr (PTy PΔ) (U[] σ) (PU [ Pσ ]P) ≡ PU
    P[idS]
      : {PΓ : PCtx Γ}(PA : PTy PΓ A)
      ------------------------------
      → tr (PTy PΓ) ([idS] A) (PA [ PidS ]P) ≡ PA
    P[∘]
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PΘ : PCtx Θ}
      → (PA : PTy PΓ A)(Pσ : PSub PΔ PΓ σ)(Pτ : PSub PΘ PΔ τ)
      -----------------------------------------------------------------
      → tr (PTy PΘ) ([∘] A σ τ) (PA [ Pσ ∘P Pτ ]P) ≡ PA [ Pσ ]P [ Pτ ]P
