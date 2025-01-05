-- Model of Substitution Calculus
module SC+U+Pi.QIIRT.Model where

open import Prelude
  hiding (_,_)
open import Data.Nat hiding (_⊔_)
open import SC+U+Pi.QIIRT.Base
-- open import SC.QIIRT2.Cong

private variable
  Δ' Φ : Ctx
  A' B' C' : Ty Γ i
  σ' τ' γ' : Sub Γ Δ

record Pdc {ℓ ℓ′} : Set (lsuc (ℓ ⊔ ℓ′)) where
  field
    PCtx
      : Ctx → Set ℓ
    PTy
      : PCtx Γ → (i : ℕ) → Ty Γ i → Set ℓ
    PSub
      : PCtx Γ → PCtx Δ → Sub Γ Δ → Set ℓ′
    PTm
      : (PΓ : PCtx Γ) → PTy PΓ i A → Tm Γ A → Set ℓ′
  
  PTmFamₜ : {PΓ : PCtx Γ}{t : Tm Γ A} → PTy PΓ i A → Set ℓ′
  PTmFamₜ {PΓ = PΓ} {t} PA = PTm PΓ PA t

record IH {ℓ ℓ′}(P : Pdc {ℓ} {ℓ′}) : Set (ℓ ⊔ ℓ′) where
  open Pdc P
  field
    -- induction on substitution
    [_]P_
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}
        (Pσ : PSub PΔ PΓ σ)(PA : PTy PΓ i A)
      --------------------------------------
      → PTy PΔ i ([ σ ] A)
    [_]tP_
      : {PΓ : PCtx Γ}{PA : PTy PΓ i A}{PΔ : PCtx Δ}
        (Pσ : PSub PΔ PΓ σ)(Pt : PTm PΓ PA t)
      ---------------------------------------
      → PTm PΔ ([ Pσ ]P PA) ([ σ ]t t)
    
    -- induction on contexts
    ∅Ctx
      : PCtx ∅
    _,Ctx_
      : (PΓ : PCtx Γ)(PA : PTy PΓ i A)
      ------------------------------
      → PCtx (Γ , A)
    
    -- induction on substitutions
    ∅Sub
      : {PΔ : PCtx Δ}
      ---------------
      → PSub PΔ ∅Ctx ∅
    _,Sub_
      : {PΔ : PCtx Δ}{PΓ : PCtx Γ}{PA : PTy PΓ i A}
        (Pσ : PSub PΔ PΓ σ)(Pt : PTm PΔ ([ Pσ ]P PA) t)
      --------------------------------------------------
      → PSub PΔ (PΓ ,Ctx PA) (σ , t)
    PidS
      : {PΔ : PCtx Γ}
      ---------------
      → PSub PΔ PΔ idS
    _⨟P_
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PΘ : PCtx Θ}
        (Pτ : PSub PΓ PΔ τ)(Pσ : PSub PΔ PΘ σ)
      -----------------------------------------
      → PSub PΓ PΘ (τ ⨟ σ)
    π₁P
      : {PΔ : PCtx Δ}{PΓ : PCtx Γ}{PA : PTy PΓ i A}
        (Pσ : PSub PΔ (PΓ ,Ctx PA) σ)
      -------------------------------
      → PSub PΔ PΓ (π₁ σ)
    -- induction on types
    PU
      : {PΓ : PCtx Γ}(i : ℕ)
      ----------------------
      → PTy PΓ (suc i) (U i)
    PU[] 
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{Pσ : PSub PΓ PΔ σ}
      -------------------
      → [ Pσ ]P (PU i) ≡ PU i
    PΠ
      : {PΓ : PCtx Γ}
        (PA : PTy PΓ i A)(PB : PTy (PΓ ,Ctx PA) i B)
      -----------------------------------------------
      → PTy PΓ i (Π A B)
    PEl
      : {PΓ : PCtx Γ}
        (Pt : PTm PΓ (PU i) t)
      -------------------------
      → PTy PΓ i (El t)
    PEl[]
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}
        (Pσ : PSub PΓ PΔ σ)(Pu : PTm PΔ (PU i) u)
        -----------------------------------------
      → ([ Pσ ]P (PEl Pu)) ≡ PEl (tr PTmFamₜ PU[] ([ Pσ ]tP Pu))
    
    -- induction on terms
    π₂P
      : {PΔ : PCtx Δ}{PΓ : PCtx Γ}{PA : PTy PΓ i A}
        (Pσ : PSub PΔ (PΓ ,Ctx PA) σ)
      ---------------------------------
      → PTm PΔ ([ π₁P Pσ ]P PA) (π₂ σ)
    [_]tmP_
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PA : PTy PΔ i A}
        (Pσ : PSub PΓ PΔ σ)(Pt : PTm PΔ PA t)
      ---------------------------------------
      → PTm PΓ ([ Pσ ]P PA) ([ σ ]tm t)
    cP
      : {PΓ : PCtx Γ}(PA : PTy PΓ i A)
      ------------------------------
      → PTm PΓ (PU i) (c A)
    ƛP
      : {PΓ : PCtx Γ}{PA : PTy PΓ i A}{PB : PTy (PΓ ,Ctx PA) i B}
        (Pt : PTm (PΓ ,Ctx PA) PB t)
      ----------------------------
      → PTm PΓ (PΠ PA PB) (ƛ t)
    appP
      : {PΓ : PCtx Γ}{PA : PTy PΓ i A}{PB : PTy (PΓ ,Ctx PA) i B}
        (Pt : PTm PΓ (PΠ PA PB) t)
      -----------------------------
      → PTm (PΓ ,Ctx PA) PB (app t)
  
  PTmFamₛ
    : {PΔ : PCtx Δ}(PΓ : PCtx Γ)(PA : PTy PΔ i A)(t : Tm Γ ([ σ ] A))(Pσ : PSub PΓ PΔ σ) → Set ℓ′
  PTmFamₛ PΓ PA t Pσ = PTm PΓ ([ Pσ ]P PA) t

{-
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
      → conv (congPSub refl refl refl refl (idS∘ σ)) (PidS ∘P Pσ) ≡ Pσ
    _∘PPidS
      : {PΓ : PCtx Γ}{PΔ : PCtx Γ}
      → (Pσ : PSub PΔ PΓ σ)
      ---------------------
      → conv (congPSub refl refl refl refl (σ ∘idS)) (Pσ ∘P PidS) ≡ Pσ
    PassocS
      : {υ : Sub Φ Θ}{PΓ : PCtx Γ}{PΔ : PCtx Γ}{PΘ : PCtx Θ}{PΦ : PCtx Φ}
      → {Pσ : PSub PΔ PΓ σ}{Pτ : PSub PΘ PΔ τ}{Pυ : PSub PΦ PΘ υ}
      --------------------------------------------------------------
      → conv (congPSub refl refl refl refl assocS) ((Pσ ∘P Pτ) ∘P Pυ) ≡ Pσ ∘P (Pτ ∘P Pυ)
    ,∘P -- the transport equation seems too long
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PΘ : PCtx Θ}
      → {PA : PTy PΓ A}{Pσ : PSub PΔ PΓ σ}{Pt : PTm PΔ (PA [ Pσ ]P) t}{Pτ : PSub PΘ PΔ τ}
      ------------------------------------------------------------------------------------------
      → conv (congPSub refl refl refl refl ,∘)
      ((Pσ ,Sub Pt) ∘P Pτ)
      ≡ ((Pσ ∘P Pτ) ,Sub conv (sym (congPTmPΓ refl ([∘P] PA Pσ Pτ) refl)) (Pt [ Pτ ]tmP)) 
    Pπ₁,
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PA : PTy PΓ A}
      → {Pσ : PSub PΔ PΓ σ}{Pt : PTm PΔ (PA [ Pσ ]P) t}
      ----------------------------------------------
      → conv (congPSub refl refl refl refl π₁,) (π₁P (Pσ ,Sub Pt)) ≡ Pσ
    Pη,
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PA : PTy PΓ A}
      → {Pσ : PSub PΔ (PΓ ,Ctx PA) σ}
      -------------------------------
      → conv (congPSub refl refl refl refl η,) Pσ ≡ π₁P Pσ ,Sub π₂P Pσ
    Pη∅
      : {PΔ : PCtx Δ}
      → {Pσ : PSub PΔ ∅Ctx σ}
      ---------------------
      → conv (congPSub refl refl refl refl η∅) Pσ ≡ ∅Sub
        
 
-}