-- Methods of Model of Substitution Calculus
module SC+U+Pi+Id.QIIRT.Model.Methods where

open import Prelude
  hiding (_,_)
open import Data.Nat hiding (_⊔_)
open import SC+U+Pi+Id.QIIRT.Base
open import SC+U+Pi+Id.QIIRT.Properties
open import SC+U+Pi+Id.QIIRT.Model.Motives

module _ {ℓ ℓ′}(P : Pred {ℓ} {ℓ′}) where
  open Pred P
  private variable
    PΓ PΔ PΘ : PCtx Γ
    Pσ Pτ Pγ : PSub PΔ PΓ σ
    PA PB PC : PTy PΓ i A
    Pa Pt Pu : PTm PΓ PA t
    p : Tm Γ (Id a t u)
    
  record InductionCtor : Set (ℓ ⊔ ℓ′) where
    field
      -- induction on type and term substitution function
      [_]P_
        : (Pσ : PSub PΔ PΓ σ)(PA : PTy PΓ i A)
        --------------------------------------
        → PTy PΔ i ([ σ ] A)
      [_]tP_
        : (Pσ : PSub PΔ PΓ σ)(Pt : PTm PΓ PA t)
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
        ---------------
        : PSub PΔ ∅Ctx ∅
      _,Sub_
        : (Pσ : PSub PΔ PΓ σ)(Pt : PTm PΔ ([ Pσ ]P PA) t)
        --------------------------------------------------
        → PSub PΔ (PΓ ,Ctx PA) (σ , t)
      PidS
        ---------------
        : PSub PΔ PΔ idS
      _⨟P_
        : (Pτ : PSub PΓ PΔ τ)(Pσ : PSub PΔ PΘ σ)
        -----------------------------------------
        → PSub PΓ PΘ (τ ⨟ σ)
      π₁P
        : (Pσ : PSub PΔ (PΓ ,Ctx PA) σ)
        -------------------------------
        → PSub PΔ PΓ (π₁ σ)
      
      -- induction on types
      PU
        : (i : ℕ)
        ----------------------
        → PTy PΓ (suc i) (U i)
      PEl
        : (Pt : PTm PΓ (PU i) t)
        -------------------------
        → PTy PΓ i (El t)
      PLift
        : (PA : PTy PΓ i A)
        → -----------------------
          PTy PΓ (suc i) (Lift A)
      PΠ
        : (PA : PTy PΓ i A)(PB : PTy (PΓ ,Ctx PA) i B)
        -----------------------------------------------
        → PTy PΓ i (Π A B)
      PId
        : (Pa : PTm PΓ (PU i) a)(Pt : PTm PΓ (PEl Pa) t)(Pu : PTm PΓ (PEl Pa) u)
          ----------------------------------------------------------------------
        → PTy PΓ i (Id a t u)
      
      -- induction on terms
      π₂P
        : (Pσ : PSub PΔ (PΓ ,Ctx PA) σ)
        ---------------------------------
        → PTm PΔ ([ π₁P Pσ ]P PA) (π₂ σ)
      [_]tmP_
        : (Pσ : PSub PΓ PΔ σ)(Pt : PTm PΔ PA t)
        ---------------------------------------
        → PTm PΓ ([ Pσ ]P PA) ([ σ ]tm t)
      cP
        : (PA : PTy PΓ i A)
        ------------------------------
        → PTm PΓ (PU i) (c A)
      mkP
        : (Pt : PTm PΓ PA t)
        → ------------------------
          PTm PΓ (PLift PA) (mk t)
      unP
        : (Pt : PTm PΓ (PLift PA) t)
        → --------------------------
          PTm PΓ PA (un t)
      ƛP_
        : (Pt : PTm (PΓ ,Ctx PA) PB t)
        ----------------------------
        → PTm PΓ (PΠ PA PB) (ƛ t)
      appP
        : (Pt : PTm PΓ (PΠ PA PB) t)
        -----------------------------
        → PTm (PΓ ,Ctx PA) PB (app t)
      
      -- induction on lifting
      _↑P_
        : (Pσ : PSub PΓ PΔ σ)(PA : PTy PΔ i A)
          ------------------------------------
        → PSub (PΓ ,Ctx ([ Pσ ]P PA)) (PΔ ,Ctx PA) (σ ↑ A)

    PTmFamₛ : {PΔ : PCtx Δ}{PΓ : PCtx Γ}(PA : PTy PΔ i A){t : Tm Γ ([ σ ] A)}
            → (Pσ : PSub PΓ PΔ σ) → Set ℓ′
    PTmFamₛ {PΓ = PΓ} PA {t} Pσ = PTm PΓ ([ Pσ ]P PA) t

  module _ (indC : InductionCtor) where
    open InductionCtor indC
    record InductionRec : Set (ℓ ⊔ ℓ′) where
      field
        -- Induction on computation rules of [_]_
        ---- compute [_]P_ w.r.t. substitutions
        [PidS]
              ------------------
            : [ PidS ]P PA ≡ PA
        [⨟P]P
            ---------------------------------------
          : [ Pτ ⨟P Pσ ]P PA ≡ [ Pτ ]P ([ Pσ ]P PA)
        [π₁P,Sub]P
            ----------------------------------------
          : ([ π₁P (Pσ ,Sub Pt) ]P PA) ≡ [ Pσ ]P PA
        [π₁P⨟P]P
            -------------------------------------------------
          : [ π₁P (Pσ ⨟P Pτ) ]P PA ≡ [ Pσ ]P ([ π₁P Pτ ]P PA)
        -- compute [_]tP_ w.r.t substitutions
        [PidS]tP
            -------------------------------------------
          : tr PTmFamₜ [PidS] ([ PidS ]tP Pt) ≡ Pt
        [⨟P]tP
            -------------------------------------------------------------
          : tr PTmFamₜ [⨟P]P ([ Pσ ⨟P Pτ ]tP Pt) ≡ [ Pσ ]tP ([ Pτ ]tP Pt)
        [π₁P,Sub]tP
            -------------------------------------------
          : tr PTmFamₜ [π₁P,Sub]P ([ π₁P (Pσ ,Sub Pt) ]tP Pu) ≡ [ Pσ ]tP Pu
        [π₁P⨟P]tP
            -------------------------------------------------
          : tr PTmFamₜ [π₁P⨟P]P ([ π₁P (Pσ ⨟P Pτ) ]tP Pt) ≡ [ Pσ ]tP ([ π₁P Pτ ]tP Pt)
        -- Should we put rest of each cases here or catch all ?
        
        ---- compute [_]P_ w.r.t. types 
        []PU
            -------------------
          : [ Pσ ]P (PU i) ≡ PU i
        []PEl
          : (Pσ : PSub PΓ PΔ σ)(Pu : PTm PΔ (PU i) u)
            -----------------------------------------
          → ([ Pσ ]P (PEl Pu)) ≡ PEl (tr PTmFamₜ []PU ([ Pσ ]tP Pu))
        []PLift
          : [ Pσ ]P (PLift PA) ≡ PLift ([ Pσ ]P PA)
        []PΠ
          : (Pσ : PSub PΓ PΔ σ)
            -------------------------------------------------------
          → [ Pσ ]P (PΠ PA PB) ≡ PΠ ([ Pσ ]P PA) ([ Pσ ↑P PA ]P PB)
        []PId
            ------------------------------------------------
          : [ Pσ ]P (PId Pa Pt Pu)
          ≡ PId (tr PTmFamₜ []PU ([ Pσ ]tP Pa))
              (tr PTmFamₜ ([]PEl Pσ Pa) ([ Pσ ]tP Pt))
              (tr PTmFamₜ ([]PEl Pσ Pa) ([ Pσ ]tP Pu))
        
      _⁺ᴾ
        : {PΓ : PCtx Γ}{PΔ : PCtx Δ}
          (Pσ : PSub PΓ PΔ σ){PA : PTy PΔ i A}
        → PSub (PΓ ,Ctx ([ Pσ ]P PA)) (PΔ ,Ctx PA) (σ ⁺)
      Pσ ⁺ᴾ = (π₁P PidS ⨟P Pσ) ,Sub tr PTmFamₜ (sym $ [⨟P]P) (π₂P PidS)
    
    module _ (indR : InductionRec) where
      open InductionRec indR
      record Induction≡ : Set (ℓ ⊔ ℓ′) where
        field
          -- induction on substitution equality constructors
          _⨟PPidS
            : (Pσ : PSub PΔ PΓ σ)
            --------------------------------------
            → tr PSubFam (σ ⨟idS) (Pσ ⨟P PidS) ≡ Pσ
          PidS⨟P_
            : (Pσ : PSub PΔ PΓ σ)
            ---------------------
            → tr PSubFam (idS⨟ σ) (PidS ⨟P Pσ) ≡ Pσ
          ⨟P-assoc
            --------------------------------------------------------------
            : tr PSubFam ⨟-assoc (Pσ ⨟P (Pτ ⨟P Pγ))
            ≡ (Pσ ⨟P Pτ) ⨟P Pγ
          π₁P,Sub
            : tr (PSub PΓ PΔ) π₁, (π₁P (Pσ ,Sub Pt)) ≡ Pσ
          ⨟P,Sub -- the transport equation seems too long
            ------------------------------------------------------------------------------------------
            : tr PSubFam ⨟, (Pσ ⨟P (Pτ ,Sub Pt))
            ≡ (Pσ ⨟P Pτ) ,Sub tr PTmFamₜ (sym $ [⨟P]P) ([ Pσ ]tmP Pt)
          η∅Sub
            -----------------------
            : tr PSubFam η∅ Pσ ≡ ∅Sub
          η,Sub
            -------------------------------
            : tr PSubFam η, Pσ ≡ π₁P Pσ ,Sub π₂P Pσ
          
          -- induction on term equality constructors
          [PidS]tmP
              -------------------------------------------
            : tr₂ (PTm PΓ) [PidS] [id]tm ([ PidS ]tmP Pt)
            ≡ Pt
          [⨟P]tmP
              --------------------------------------------------------------------------
            : tr₂ (PTm PΓ) [⨟P]P [⨟]tm ([ Pσ ⨟P Pτ ]tmP Pt)
            ≡ [ Pσ ]tmP ([ Pτ ]tmP Pt)
          π₂P,Sub
              --------------------------------------------
            : tr₂ (PTm PΓ) [π₁P,Sub]P π₂, (π₂P (Pσ ,Sub Pt))
            ≡ Pt
          []tPcP
            : (Pσ : PSub PΓ PΔ σ)(PA : PTy PΔ i A)
              ------------------------------------
            → tr₂ (PTm PΓ) []PU ([]tc σ A) ([ Pσ ]tP (cP PA))
            ≡ cP ([ Pσ ]P PA)
          []mkP
              ------------------
            : tr₂ (PTm PΓ) []PLift []mk ([ Pσ ]tmP mkP Pt)
            ≡ mkP ([ Pσ ]tmP Pt)
          []unP
              --------------------------
            : tr PTmFam ([]un σ A t) ([ Pσ ]tmP unP Pt)
            ≡ unP (tr PTmFamₜ []PLift ([ Pσ ]tmP Pt))
          PUη
            : tr PTmFam Uη (cP (PEl Pu)) ≡ Pu
          PLiftβ
              ------------------
            : tr PTmFam Liftβ (unP (mkP Pt)) ≡ Pt
          PLiftη
              --------------------------
            : tr PTmFam Liftη (mkP (unP Pt)) ≡ Pt
          reflectP
            : (Pp : PTm PΓ (PId Pa Pt Pu) p)
              -------------------------------
            → tr PTmFam (reflect p) Pt ≡ Pu
          []ƛP
              ---------------------------------------------------------
            : tr₂ (PTm PΓ) ([]PΠ Pσ) []ƛ ([ Pσ ]tmP (ƛP Pt)) ≡ ƛP ([ Pσ ↑P PA ]tmP Pt)
          PΠβ
              ----------------------------
            : tr PTmFam Πβ (appP (ƛP Pt)) ≡ Pt
          PΠη
              --------------------------
            : tr PTmFam Πη (ƛP (appP Pt)) ≡ Pt
          
          -- induction on type equalities
          PUβ
            : tr PTyFam Uβ (PEl (cP PA)) ≡ PA
  
  record Induction : Set (ℓ ⊔ ℓ′) where
    field
      indC : InductionCtor
      indR : InductionRec indC
      ind≡ : Induction≡ indC indR
    
    open InductionCtor indC public
    open InductionRec indR public
    open Induction≡ ind≡ public
 
