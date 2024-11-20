-- Model of Substitution Calculus
module SC.QIIRT.Model where

open import Prelude
open import SC.QIIRT.Base

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
    _‣Ctx_
      : (PΓ : PCtx Γ)(PA : PTy PΓ A)
      ------------------------------
      → PCtx (Γ ‣ A)
    
    -- induction on substitutions
    ∅Sub
      : {PΔ : PCtx Δ}
      ---------------
      → PSub PΔ ∅Ctx ∅
    _‣Sub_
      : {PΔ : PCtx Δ}{PΓ : PCtx Γ}{PA : PTy PΓ A}
        (Pσ : PSub PΔ PΓ σ)(Pt : PTm PΔ (PA [ Pσ ]P) t)
      --------------------------------------------------
      → PSub PΔ (PΓ ‣Ctx PA) (σ ‣ t)
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
        (Pσ : PSub PΔ (PΓ ‣Ctx PA) σ)
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
        (Pσ : PSub PΔ (PΓ ‣Ctx PA) σ)
      ---------------------------------
      → PTm PΔ (PA [ π₁P Pσ ]P) (π₂ σ)
    _[_]tmP
      : {PΓ : PCtx Γ}{PA : PTy PΓ A}{PΔ : PCtx Δ}
        (Pt : PTm PΓ PA t)(Pσ : PSub PΔ PΓ σ)
      ---------------------------------------
      → PTm PΔ (PA [ Pσ ]P) (t [ σ ]tm)
    
    -- induction on equalities
    PU[] 
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{Pσ : PSub PΔ PΓ σ}
      -------------------
      → PU [ Pσ ]P ≡ PU
    [PidS]
      : {PΓ : PCtx Γ}
      → (PA : PTy PΓ A)
      -----------------
      → tr (PTy PΓ) ([idS] A) (PA [ PidS ]P) ≡ PA
    [∘P]
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PΘ : PCtx Θ}
      → (PA : PTy PΓ A)(Pσ : PSub PΔ PΓ σ)(Pτ : PSub PΘ PΔ τ)
      -----------------------------------------------------------------
      → tr (PTy PΘ) ([∘] A σ τ) (PA [ Pσ ∘P Pτ ]P) ≡ PA [ Pσ ]P [ Pτ ]P
    PidS∘P_
      : {PΓ : PCtx Γ}{PΔ : PCtx Γ}
      → (Pσ : PSub PΔ PΓ σ)
      ---------------------
      → tr (PSub PΔ PΓ) (idS∘ σ) (PidS ∘P Pσ) ≡ Pσ
    _∘PPidS
      : {PΓ : PCtx Γ}{PΔ : PCtx Γ}
      → (Pσ : PSub PΔ PΓ σ)
      ---------------------
      → tr (PSub PΔ PΓ) (σ ∘idS) (Pσ ∘P PidS) ≡ Pσ
    PassocS
      : {υ : Sub Φ Θ}{PΓ : PCtx Γ}{PΔ : PCtx Γ}{PΘ : PCtx Θ}{PΦ : PCtx Φ}
      → {Pσ : PSub PΔ PΓ σ}{Pτ : PSub PΘ PΔ τ}{Pυ : PSub PΦ PΘ υ}
      --------------------------------------------------------------
      → tr (PSub PΦ PΓ) assocS ((Pσ ∘P Pτ) ∘P Pυ) ≡ Pσ ∘P (Pτ ∘P Pυ)
    ‣∘P
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PΘ : PCtx Θ}
      → {PA : PTy PΓ A}{Pσ : PSub PΔ PΓ σ}{Pt : PTm PΔ (PA [ Pσ ]P) t}{Pτ : PSub PΘ PΔ τ}
      ------------------------------------------------------------------------------------------
      → tr (PSub PΘ (PΓ ‣Ctx PA)) ‣∘ ((Pσ ‣Sub Pt) ∘P Pτ) ≡ (Pσ ∘P Pτ) ‣Sub {!  Pt [ Pτ ]tmP !}
    Pβπ₁
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PA : PTy PΓ A}
      → {Pσ : PSub PΔ PΓ σ}{Pt : PTm PΔ (PA [ Pσ ]P) t}
      ----------------------------------------------
      → tr (PSub PΔ PΓ) βπ₁ (π₁P (Pσ ‣Sub Pt)) ≡ Pσ
    Pηπ
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PA : PTy PΓ A}
      → {Pσ : PSub PΔ (PΓ ‣Ctx PA) σ}
      -------------------------------
      → σ ≡ π₁ σ ‣ π₂ σ
    Pη∅
      : {PΔ : PCtx Δ}
      → {Pσ : PSub PΔ ∅Ctx σ}
      ---------------------
      → tr (PSub PΔ ∅Ctx) η∅ Pσ ≡ ∅Sub
        
