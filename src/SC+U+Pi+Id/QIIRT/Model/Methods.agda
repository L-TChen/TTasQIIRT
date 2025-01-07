-- Methods of Model of Substitution Calculus
module SC+U+Pi.QIIRT.Model.Methods where

open import Prelude
  hiding (_,_)
open import Data.Nat hiding (_⊔_)
open import SC+U+Pi.QIIRT.Base
open import SC+U+Pi.QIIRT.Properties
open import SC+U+Pi.QIIRT.Model.Motives

private variable
  Δ' Φ : Ctx
  A' B' C' : Ty Γ i
  σ' τ' γ' : Sub Γ Δ

module _ {ℓ ℓ′}(P : Predicate {ℓ} {ℓ′}) where
  open Predicate P
  record InductionCtor : Set (ℓ ⊔ ℓ′) where
    field
      -- induction on type and term substitution function
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
      PLift
        : {PΓ : PCtx Γ}
          (PA : PTy PΓ i A)
        → -----------------------
          PTy PΓ (suc i) (Lift A)
      
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
      mkP
        : {PΓ : PCtx Γ}{PA : PTy PΓ i A}
          (Pt : PTm PΓ PA t)
        → ------------------------
          PTm PΓ (PLift PA) (mk t)
      unP
        : {PΓ : PCtx Γ}{PA : PTy PΓ i A}
          (Pt : PTm PΓ (PLift PA) t)
        → --------------------------
          PTm PΓ PA (un t)
      
      -- induction on lifting
      _↑P_
        : {PΓ : PCtx Γ}{PΔ : PCtx Δ}
          (Pσ : PSub PΓ PΔ σ)(PA : PTy PΔ i A)
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
        ---- compute [_]P_ w.r.t. types 
        PU[] 
          : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{Pσ : PSub PΓ PΔ σ}
          -------------------
          → [ Pσ ]P (PU i) ≡ PU i
        PEl[]
          : {PΓ : PCtx Γ}{PΔ : PCtx Δ}
            (Pσ : PSub PΓ PΔ σ)(Pu : PTm PΔ (PU i) u)
            -----------------------------------------
          → ([ Pσ ]P (PEl Pu)) ≡ PEl (tr PTmFamₜ PU[] ([ Pσ ]tP Pu))
        PΠ[]
          : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PA : PTy PΔ i A}{PB : PTy (PΔ ,Ctx PA) i B}
            (Pσ : PSub PΓ PΔ σ)
            -------------------------------------------------------
          → [ Pσ ]P (PΠ PA PB) ≡ PΠ ([ Pσ ]P PA) ([ Pσ ↑P PA ]P PB)
        PLift[]
          : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PA : PTy PΔ i A}
            {Pσ : PSub PΓ PΔ σ}
          → --------------------------------------------
            [ Pσ ]P (PLift PA) ≡ PLift ([ Pσ ]P PA)
        
        ---- compute [_]P_ w.r.t. substitutions
        [PidS]
            : {PΓ : PCtx Γ}
            → {PA : PTy PΓ i A}
              ------------------
            → [ PidS ]P PA ≡ PA
        [⨟P]P
          : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PΘ : PCtx Θ}
            {Pτ : PSub PΓ PΔ τ}{Pσ : PSub PΔ PΘ σ}{PA : PTy PΘ i A}
            -------------------------------------------------------
          → [ Pτ ⨟P Pσ ]P PA ≡ [ Pτ ]P ([ Pσ ]P PA)
        [π₁P,Sub]P
          : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PA' : PTy PΔ i A'}
            {Pσ : PSub PΓ PΔ σ}{Pt : PTm PΓ ([ Pσ ]P PA') t}
            {PA : PTy PΔ i A}
            ----------------------------------------
          → ([ π₁P (Pσ ,Sub Pt) ]P PA) ≡ [ Pσ ]P PA
        [π₁P⨟P]P
          : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PΘ : PCtx Θ}
            {PA : PTy PΘ i A}{PB : PTy PΘ j B}
            {Pσ : PSub PΓ PΔ σ}{Pτ : PSub PΔ (PΘ ,Ctx PB) τ}
            -------------------------------------------------
          → [ π₁P (Pσ ⨟P Pτ) ]P PA ≡ [ Pσ ]P ([ π₁P Pτ ]P PA)

        -- compute [_]tP_
        [PidS]tP
          : {PΓ : PCtx Γ}{PA : PTy PΓ i A}
            {Pt : PTm PΓ PA t}
            -------------------------------------------
          → tr PTmFamₜ [PidS] ([ PidS ]tP Pt) ≡ Pt
        [⨟P]tP
          : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PΘ : PCtx Θ}
            {PA : PTy PΘ i A}{Pσ : PSub PΓ PΔ σ}{Pτ : PSub PΔ PΘ τ}{Pt : PTm PΘ PA t}
            --------------------------------------------------------------------------
          → tr PTmFamₜ [⨟P]P ([ Pσ ⨟P Pτ ]tP Pt) ≡ [ Pσ ]tP ([ Pτ ]tP Pt)
        [π₁P,Sub]tP
          : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PA' : PTy PΔ i A'}
            {Pσ : PSub PΓ PΔ σ}{Pt : PTm PΓ ([ Pσ ]P PA') t}
            {PA : PTy PΔ i A}{Pu : PTm PΔ PA u}
            -------------------------------------------
          → tr PTmFamₜ [π₁P,Sub]P ([ π₁P (Pσ ,Sub Pt) ]tP Pu) ≡ [ Pσ ]tP Pu
        [π₁P⨟P]tP
          : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PΘ : PCtx Θ}
            {PA : PTy PΘ i A}{PB : PTy PΘ j B}
            {Pσ : PSub PΓ PΔ σ}{Pτ : PSub PΔ (PΘ ,Ctx PB) τ}
            {Pt : PTm PΘ PA t}
            -------------------------------------------------
          → tr PTmFamₜ [π₁P⨟P]P ([ π₁P (Pσ ⨟P Pτ) ]tP Pt) ≡ [ Pσ ]tP ([ π₁P Pτ ]tP Pt)
        -- Should we put rest of each cases here or catch all ?
      _⁺ᴾ
        : {PΓ : PCtx Γ}{PΔ : PCtx Δ}
          (Pσ : PSub PΓ PΔ σ){PA : PTy PΔ i A}
        → PSub (PΓ ,Ctx ([ Pσ ]P PA)) (PΔ ,Ctx PA) (σ ⁺)
      Pσ ⁺ᴾ = (π₁P PidS ⨟P Pσ) ,Sub tr PTmFamₜ (sym $ [⨟P]P) (π₂P PidS)
    
    module _ (indR : InductionRec) where
      open InductionRec indR
      record Induction≡ : Set (ℓ ⊔ ℓ′) where
        field
          -- induction on substitution equalities
          _⨟PPidS
            : {PΓ : PCtx Γ}{PΔ : PCtx Γ}
            → (Pσ : PSub PΔ PΓ σ)
            --------------------------------------
            → tr PSubFam (σ ⨟idS) (Pσ ⨟P PidS) ≡ Pσ
          PidS⨟P_
            : {PΓ : PCtx Γ}{PΔ : PCtx Γ}
            → (Pσ : PSub PΔ PΓ σ)
            ---------------------
            → tr PSubFam (idS⨟ σ) (PidS ⨟P Pσ) ≡ Pσ
          ⨟P-assoc
            : {PΓ : PCtx Γ}{PΔ : PCtx Γ}{PΘ : PCtx Θ}{PΦ : PCtx Φ}
            → {Pσ : PSub PΓ PΔ σ}{Pτ : PSub PΔ PΘ τ}{Pγ : PSub PΘ PΦ γ}
            --------------------------------------------------------------
            → tr PSubFam ⨟-assoc (Pσ ⨟P (Pτ ⨟P Pγ)) ≡ (Pσ ⨟P Pτ) ⨟P Pγ
          π₁P,Sub
            : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PA : PTy PΔ i A}
              {Pσ : PSub PΓ PΔ σ}{Pt : PTm PΓ ([ Pσ ]P PA) t}
            -------------------------------------------------
            → tr (PSub PΓ PΔ) π₁, (π₁P (Pσ ,Sub Pt)) ≡ Pσ
          ⨟P,Sub -- the transport equation seems too long
            : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PΘ : PCtx Θ}{PA : PTy PΘ i A}
            → {Pσ : PSub PΓ PΔ σ}{Pτ : PSub PΔ PΘ τ}{Pt : PTm PΔ ([ Pτ ]P PA) t}
            ------------------------------------------------------------------------------------------
            → tr PSubFam ⨟, (Pσ ⨟P (Pτ ,Sub Pt)) ≡ (Pσ ⨟P Pτ) ,Sub tr PTmFamₜ (sym $ [⨟P]P) ([ Pσ ]tmP Pt)
          η∅Sub
            : {PΔ : PCtx Δ}
            → {Pσ : PSub PΔ ∅Ctx σ}
            -----------------------
            → tr PSubFam η∅ Pσ ≡ ∅Sub
          η,Sub
            : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PA : PTy PΓ i A}
            → {Pσ : PSub PΔ (PΓ ,Ctx PA) σ}
            -------------------------------
            → tr PSubFam η, Pσ ≡ π₁P Pσ ,Sub π₂P Pσ
          
          -- induction on term equalities
          [PidS]tmP
            : {PΓ : PCtx Γ}{PA : PTy PΓ i A}
              {Pt : PTm PΓ PA t}
              -------------------------------------------
            → tr₂ (PTm PΓ) [PidS] [id]tm ([ PidS ]tmP Pt) ≡ Pt
          [⨟P]tmP
            : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PΘ : PCtx Θ}
              {PA : PTy PΘ i A}{Pσ : PSub PΓ PΔ σ}{Pτ : PSub PΔ PΘ τ}{Pt : PTm PΘ PA t}
              --------------------------------------------------------------------------
            → tr₂ (PTm PΓ) [⨟P]P [⨟]tm ([ Pσ ⨟P Pτ ]tmP Pt) ≡ [ Pσ ]tmP ([ Pτ ]tmP Pt)
          π₂P,Sub
            : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PA : PTy PΔ i A}
              {Pσ : PSub PΓ PΔ σ}{Pt : PTm PΓ ([ Pσ ]P PA) t}
              --------------------------------------------
            → tr₂ (PTm PΓ) [π₁P,Sub]P π₂, (π₂P (Pσ ,Sub Pt)) ≡ Pt
          cP[]tP
            : {PΓ : PCtx Γ}{PΔ : PCtx Δ}
              (Pσ : PSub PΓ PΔ σ)(PA : PTy PΔ i A)
              ------------------------------------
            → tr₂ (PTm PΓ) PU[] (c[]t σ A) ([ Pσ ]tP (cP PA)) ≡ cP ([ Pσ ]P PA)
          PUη
            : {PΓ : PCtx Γ}{Pu : PTm PΓ (PU i) u}
            → tr PTmFam Uη (cP (PEl Pu)) ≡ Pu
          []mkP
            : {PΓ : PCtx Γ}{PΔ : PCtx Δ}
              {Pσ : PSub PΓ PΔ σ}{PA : PTy PΔ i A}
              {Pt : PTm PΔ PA t}
              ------------------
            → tr₂ (PTm PΓ) PLift[] []mk ([ Pσ ]tmP mkP Pt) ≡ mkP ([ Pσ ]tmP Pt)
          []unP
            : {PΓ : PCtx Γ}{PΔ : PCtx Δ}
              {Pσ : PSub PΓ PΔ σ}{PA : PTy PΔ i A}
              {Pt : PTm PΔ (PLift PA) t}
              --------------------------
            → tr PTmFam ([]un σ A t) ([ Pσ ]tmP unP Pt) ≡ unP (tr PTmFamₜ PLift[] ([ Pσ ]tmP Pt))
          PLiftβ
            : {PΓ : PCtx Γ}{PA : PTy PΓ i A}
              {Pt : PTm PΓ PA t}
              ------------------
            → tr PTmFam Liftβ (unP (mkP Pt)) ≡ Pt
          PLiftη
            : {PΓ : PCtx Γ}{PA : PTy PΓ i A}
              {Pt : PTm PΓ (PLift PA) t}
              --------------------------
            → tr PTmFam Liftη (mkP (unP Pt)) ≡ Pt
          []ƛP
            : {PΓ : PCtx Γ}{PΔ : PCtx Δ}
              {PA : PTy PΔ i A}{PB : PTy (PΔ ,Ctx PA) i B}
              {Pt : PTm (PΔ ,Ctx PA) PB t}{Pσ : PSub PΓ PΔ σ}
              ---------------------------------------------------------
            → tr₂ (PTm PΓ) (PΠ[] Pσ) []ƛ ([ Pσ ]tmP (ƛP Pt)) ≡ ƛP ([ Pσ ↑P PA ]tmP Pt)
          PΠβ
            : {PΓ : PCtx Γ}{PA : PTy PΓ i A}{PB : PTy (PΓ ,Ctx PA) i B}
              {Pt : PTm (PΓ ,Ctx PA) PB t}
              ----------------------------
            → tr PTmFam Πβ (appP (ƛP Pt)) ≡ Pt
          PΠη
            : {PΓ : PCtx Γ}{PA : PTy PΓ i A}{PB : PTy (PΓ ,Ctx PA) i B}
              {Pt : PTm PΓ (PΠ PA PB) t}
              --------------------------
            → tr PTmFam Πη (ƛP (appP Pt)) ≡ Pt
          
          -- induction on type equalities
          PUβ
            : {PΓ : PCtx Γ}{PA : PTy PΓ i A}
            → tr PTyFam Uβ (PEl (cP PA)) ≡ PA
          ↑P=⁺ᴾ
            : {PΓ : PCtx Γ}{PΔ : PCtx Δ}
              (Pσ : PSub PΓ PΔ σ)(PA : PTy PΔ i A)
            → tr (PSub (PΓ ,Ctx ([ Pσ ]P PA)) (PΔ ,Ctx PA)) (↑=⁺ A σ) (Pσ ↑P PA) ≡ Pσ ⁺ᴾ
  
  record Induction : Set (ℓ ⊔ ℓ′) where
    field
      indC : InductionCtor
      indR : InductionRec indC
      ind≡ : Induction≡ indC indR
    
    open InductionCtor indC public
    open InductionRec indR public
    open Induction≡ ind≡ public
 