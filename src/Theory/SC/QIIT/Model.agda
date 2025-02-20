-- Model of Substitution Calculus
module SC.QIIT2.Model where

open import Prelude
  hiding (_∘_)
open import SC.QIIT2.Base

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
  
  trPTm
    : {PΓ : PCtx Γ}{PA : PTy PΓ A}{PA' : PTy PΓ A'}
    → (A≡A' : A ≡ A') → tr (PTy PΓ) A≡A' PA ≡ PA'
    → tr (Tm Γ) A≡A' t ≡ t'
    → PTm PΓ PA t → PTm PΓ PA' t'
  trPTm {PΓ = PΓ} {PA} refl refl = tr (PTm PΓ PA)

record IH {i j}(P : Pdc {i} {j}) : Set (i ⊔ j) where
  open Pdc P
  field    
    -- induction on contexts
    ∅Ctx
      : PCtx ∅
    _,Ctx_
      : (PΓ : PCtx Γ)(PA : PTy PΓ A)
      ------------------------------
      → PCtx (Γ , A)
    
    -- induction on types
    PU
      : {PΓ : PCtx Γ}
      ---------------
      → PTy PΓ U
    _[_]P
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}
        (PA : PTy PΓ A)(Pσ : PSub PΔ PΓ σ)
      ------------------------------------
      → PTy PΔ (A [ σ ])

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
  
  tr[]P
    : {PΓ : PCtx Γ}{PΔ : PCtx Δ}
      {Pσ : PSub PΓ PΔ σ}{Pσ' : PSub PΓ PΔ σ'}{PA : PTy PΔ A}
      (σ≡σ' : σ ≡ σ') → tr (PSub PΓ PΔ) σ≡σ' Pσ ≡ Pσ'
    → tr (PTy PΓ) (cong (A [_]) σ≡σ') (PA [ Pσ ]P) ≡ PA [ Pσ' ]P
  tr[]P refl refl = refl

record IHEq {i j}(P : Pdc {i} {j})(indP : IH P) : Set (i ⊔ j) where
  open Pdc P
  open IH indP
  field   
    -- induction on equalities on types
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
    
    -- induction on equalities on substitutions
    PidS∘
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}(Pσ : PSub PΔ PΓ σ)
      -----------------------------------------------
      → tr (PSub PΔ PΓ) (idS∘ σ) (PidS ∘P Pσ) ≡ Pσ
    ∘PidS
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}(Pσ : PSub PΔ PΓ σ)
      -----------------------------------------------
      → tr (PSub PΔ PΓ) (σ ∘idS) (Pσ ∘P PidS) ≡ Pσ
    PassocS
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PΘ : PCtx Θ}{PΦ : PCtx Φ}
        {Pσ : PSub PΓ PΔ σ}{Pτ : PSub PΔ PΘ τ}{Pδ : PSub PΘ PΦ δ}
      --------------------------------------------------------------
      → tr (PSub PΓ PΦ) assocS ((Pδ ∘P Pτ) ∘P Pσ) ≡ Pδ ∘P (Pτ ∘P Pσ)
    P,∘
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PΘ : PCtx Θ}{PA : PTy PΘ A}
        {Pσ : PSub PΔ PΘ σ}{Pt : PTm PΔ (PA [ Pσ ]P) t}{Pτ : PSub PΓ PΔ τ}
      → tr (PSub PΓ (PΘ ,Ctx PA)) ,∘ ((Pσ ,Sub Pt) ∘P Pτ)
      ≡ (Pσ ∘P Pτ) ,Sub trPTm (sym $ [∘] A σ τ) (flip-tr (P[∘] PA Pσ Pτ)) refl (Pt [ Pτ ]tP)
    Pβπ₁
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PA : PTy PΔ A}
        {Pσ : PSub PΓ PΔ σ}{Pt : PTm PΓ (PA [ Pσ ]P) t}
      -------------------------------------------------
      → tr (PSub PΓ PΔ) βπ₁ (π₁P (Pσ ,Sub Pt)) ≡ Pσ
    Pηπ
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PA : PTy PΔ A}
        {Pσ : PSub PΓ (PΔ ,Ctx PA) σ}
      --------------------------------------------------------
      → tr (PSub PΓ (PΔ ,Ctx PA)) ηπ Pσ ≡ (π₁P Pσ ,Sub π₂P Pσ)
    Pη∅
      : {PΓ : PCtx Γ}{Pσ : PSub PΓ ∅Ctx σ}
      ------------------------------------
      → tr (PSub PΓ ∅Ctx) η∅ Pσ ≡ ∅Sub
    
    -- induction on equalities on terms
    P[idS]tm
      : {PΓ : PCtx Γ}{PA : PTy PΓ A}(Pt : PTm PΓ PA t)
      → trPTm ([idS] A) (P[idS] PA) ([idS]tm t) (Pt [ PidS ]tP) ≡ Pt
    P[∘]tm
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PΘ : PCtx Θ}{PA : PTy PΘ A}
        (Pt : PTm PΘ PA t)(Pσ : PSub PΔ PΘ σ)(Pτ : PSub PΓ PΔ τ)
      → trPTm ([∘] _ _ _) (P[∘] PA Pσ Pτ) ([∘]tm t σ τ) (Pt [ Pσ ∘P Pτ ]tP) ≡ Pt [ Pσ ]tP [ Pτ ]tP
    Pβπ₂
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PA : PTy PΔ A}
        {Pσ : PSub PΓ PΔ σ}{Pt : PTm PΓ (PA [ Pσ ]P) t}
      → trPTm (cong (A [_]) βπ₁) (tr[]P βπ₁ Pβπ₁) (trans (sym (tr-cong βπ₁)) βπ₂) (π₂P (Pσ ,Sub Pt)) ≡ Pt
    
  