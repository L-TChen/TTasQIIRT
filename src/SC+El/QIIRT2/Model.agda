-- Model of Substitution Calculus
module SC+El.QIIRT2.Model where

open import Prelude
open import SC+El.QIIRT2.Base

variable
  Γ' Φ : Ctx

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
    -- induction on recursions
    _[_]P
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}
        (PA : PTy PΓ A)(Pσ : PSub PΔ PΓ σ)
      ------------------------------------
      → PTy PΔ (A [ σ ])
    _[_]tP
      : {PΓ : PCtx Γ}{PA : PTy PΓ A}{PΔ : PCtx Δ}
        (Pt : PTm PΓ PA t)(Pσ : PSub PΔ PΓ σ)
      ---------------------------------------
      → PTm PΔ (PA [ Pσ ]P) (t [ σ ]t)
    
    
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
    
    -- induction on terms
    π₂P
      : {PΔ : PCtx Δ}{PΓ : PCtx Γ}{PA : PTy PΓ A}
        (Pσ : PSub PΔ (PΓ ,Ctx PA) σ)
      ---------------------------------
      → PTm PΔ (PA [ π₁P Pσ ]P) (π₂ σ)
    _[_]tmP
      : {PΓ : PCtx Γ}{PA : PTy PΓ A}{PΔ : PCtx Δ}
        (Pt : PTm PΓ PA t)(Pσ : PSub PΔ PΓ σ)
      ---------------------------------------
      → PTm PΔ (PA [ Pσ ]P) (t [ σ ]tm)
    
    -- induction on types
    PU
      : {PΓ : PCtx Γ}
      ---------------
      → PTy PΓ U
    PEl
      : {PΓ : PCtx Γ}{u : Tm Γ U}
        (Pu : PTm PΓ PU u)
      --------------------
      → PTy PΓ (El u)
    PU[] 
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{Pσ : PSub PΔ PΓ σ}
      -------------------
      → PU [ Pσ ]P ≡ PU
    PEl[]
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{u : Tm Γ U}{Pu : PTm PΓ PU u}
        (Pσ : PSub PΔ PΓ σ)
      -----------------------------
      → (PEl Pu) [ Pσ ]P ≡ PEl (conv (cong (λ PA → PTm PΔ PA (u [ σ ]t)) PU[]) (Pu [ Pσ ]tP))
  
  congPTm
    : {PΓ : PCtx Γ}{PA : PTy PΓ A}{PA' : PTy PΓ A'}{t : Tm Γ A}{t' : Tm Γ A'}
    → (A≡A' : A ≡ A') → conv (cong (PTy PΓ) A≡A') PA ≡ PA' → conv (cong (Tm Γ) A≡A') t ≡ t'
    ---------------------------------------------------------------------------------------
    → PTm PΓ PA t ≡ PTm PΓ PA' t'
  congPTm refl refl refl = refl

record IHEq {i j}(P : Pdc {i} {j})(indP : IH P) : Set (i ⊔ j) where
  open Pdc P
  open IH indP
  field   
    -- induction on equalities
    [PidS]
      : {PΓ : PCtx Γ}
      → (PA : PTy PΓ A)
      -----------------
      → PA [ PidS ]P ≡ PA
    [∘P]
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PΘ : PCtx Θ}
      → (PA : PTy PΓ A)(Pσ : PSub PΔ PΓ σ)(Pτ : PSub PΘ PΔ τ)
      -----------------------------------------------------------------
      → PA [ Pσ ∘P Pτ ]P ≡ PA [ Pσ ]P [ Pτ ]P
    PidS∘P_
      : {PΓ : PCtx Γ}{PΔ : PCtx Γ}
      → (Pσ : PSub PΔ PΓ σ)
      ---------------------
      → conv (cong (PSub PΔ PΓ) (idS∘ σ)) (PidS ∘P Pσ) ≡ Pσ
    _∘PPidS
      : {PΓ : PCtx Γ}{PΔ : PCtx Γ}
      → (Pσ : PSub PΔ PΓ σ)
      ---------------------
      → conv (cong (PSub PΔ PΓ) (σ ∘idS)) (Pσ ∘P PidS) ≡ Pσ
    PassocS
      : {υ : Sub Φ Θ}{PΓ : PCtx Γ}{PΔ : PCtx Γ}{PΘ : PCtx Θ}{PΦ : PCtx Φ}
      → {Pσ : PSub PΔ PΓ σ}{Pτ : PSub PΘ PΔ τ}{Pυ : PSub PΦ PΘ υ}
      --------------------------------------------------------------
      → conv (cong (PSub PΦ PΓ) assocS) ((Pσ ∘P Pτ) ∘P Pυ) ≡ Pσ ∘P (Pτ ∘P Pυ)
    Pπ₁,
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PA : PTy PΓ A}
      → {Pσ : PSub PΔ PΓ σ}{Pt : PTm PΔ (PA [ Pσ ]P) t}
      -------------------------------------------------
      → conv (cong (PSub PΔ PΓ) π₁,) (π₁P (Pσ ,Sub Pt)) ≡ Pσ
    -- Pπ₂,
    --   : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PA : PTy PΓ A}
    --   → {Pσ : PSub PΔ PΓ σ}{Pt : PTm PΔ (PA [ Pσ ]P) t}
    --   -------------------------------------------------
    --   → conv {!   !} (π₂P (Pσ ,Sub Pt)) ≡ Pt
    ,∘P -- the transport equation seems too long
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PΘ : PCtx Θ}
      → {PA : PTy PΓ A}{Pσ : PSub PΔ PΓ σ}{Pt : PTm PΔ (PA [ Pσ ]P) t}{Pτ : PSub PΘ PΔ τ}
      ------------------------------------------------------------------------------------------
      → conv (cong (PSub PΘ (PΓ ,Ctx PA)) ,∘) ((Pσ ,Sub Pt) ∘P Pτ) ≡ ((Pσ ∘P Pτ) ,Sub conv (congPTm refl (sym ([∘P] PA Pσ Pτ)) ([]tm≡[]t t τ)) (Pt [ Pτ ]tmP))
    Pη∅
      : {PΔ : PCtx Δ}
      → {Pσ : PSub PΔ ∅Ctx σ}
      ---------------------
      → conv (cong (PSub PΔ ∅Ctx) η∅) Pσ ≡ ∅Sub
    Pηπ
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PA : PTy PΓ A}
      → {Pσ : PSub PΔ (PΓ ,Ctx PA) σ}
      -------------------------------
      → conv (cong (PSub PΔ (PΓ ,Ctx PA)) η,) Pσ ≡ π₁P Pσ ,Sub π₂P Pσ
