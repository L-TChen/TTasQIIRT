-- Model of Substitution Calculus
module SC.QIIRT2.Model where

open import Prelude
  hiding (_,_)
open import SC.QIIRT2.Base
open import SC.QIIRT2.Cong

private variable
  Φ : Ctx
  A' B' C' : Ty Γ
  σ' τ' γ' : Sub Δ Γ

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
  
  congPCtx : Γ ≡ Γ' → PCtx Γ ≡ PCtx Γ'
  congPCtx refl = refl
  
  congPTy : {PΓ : PCtx Γ}{PΓ' : PCtx Γ'}
            (Γ≡Γ' : Γ ≡ Γ')(PΓ≡PΓ' : conv (congPCtx Γ≡Γ') PΓ ≡ PΓ')
          → (A≡A' : conv (congTy Γ≡Γ') A ≡ A')
          → PTy PΓ A ≡ PTy PΓ' A'
  congPTy refl refl refl = refl

  congPTyPΓ : {PΓ : PCtx Γ}{A A' : Ty Γ}(A≡A' : A ≡ A')
            → PTy PΓ A ≡ PTy PΓ A'
  congPTyPΓ = congPTy refl refl
  
  congPSub : {PΓ : PCtx Γ}{PΓ' : PCtx Γ'}{PΔ : PCtx Δ}{PΔ' : PCtx Δ'}
           → (Γ≡Γ' : Γ ≡ Γ')(Δ≡Δ' : Δ ≡ Δ')
             (PΓ≡PΓ' : conv (congPCtx Γ≡Γ') PΓ ≡ PΓ')
             (PΔ≡PΔ' : conv (congPCtx Δ≡Δ') PΔ ≡ PΔ')
           → {σ : Sub Γ Δ}{σ' : Sub Γ' Δ'}
           → conv (congSub Γ≡Γ' Δ≡Δ') σ ≡ σ'
           → PSub PΓ PΔ σ ≡ PSub PΓ' PΔ' σ'
  congPSub refl refl refl refl refl = refl

  congPTm : {PΓ : PCtx Γ}{PΓ' : PCtx Γ'}
            (Γ≡Γ' : Γ ≡ Γ')(PΓ≡PΓ' : conv (congPCtx Γ≡Γ') PΓ ≡ PΓ')
          → {PA : PTy PΓ A}{PA' : PTy PΓ' A'}
            (A≡A' : conv (congTy Γ≡Γ') A ≡ A')(PA≡PA' : conv (congPTy Γ≡Γ' PΓ≡PΓ' A≡A') PA ≡ PA')
          → {t : Tm Γ A}{t' : Tm Γ' A'}
          → conv (congTm Γ≡Γ' A≡A') t ≡ t'
          → PTm PΓ PA t ≡ PTm PΓ' PA' t'
  congPTm refl refl refl refl refl = refl

  congPTmPΓ : {PΓ : PCtx Γ}{PA : PTy PΓ A}{PA' : PTy PΓ A'}
            → (A≡A' : A ≡ A')(PA≡PA' : conv (congPTyPΓ A≡A') PA ≡ PA')
            → {t : Tm Γ A}{t' : Tm Γ A'}
            → conv (congTmΓ A≡A') t ≡ t'
            → PTm PΓ PA t ≡ PTm PΓ PA' t'
  congPTmPΓ = congPTm refl refl

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
    PU[] 
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{Pσ : PSub PΔ PΓ σ}
      -------------------
      → PU [ Pσ ]P ≡ PU
    
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
  
  cong[]P
    : {PΔ : PCtx Δ}{PΔ' : PCtx Δ'}(Δ≡Δ' : Δ ≡ Δ')(PΔ≡PΔ' : conv (congPCtx Δ≡Δ') PΔ ≡ PΔ')
      {PΓ : PCtx Γ}{PΓ' : PCtx Γ'}(Γ≡Γ' : Γ ≡ Γ')(PΓ≡PΓ' : conv (congPCtx Γ≡Γ') PΓ ≡ PΓ')
    → {PA : PTy PΓ A}{PA' : PTy PΓ' A'}(A≡A' : conv (congTy Γ≡Γ') A ≡ A')(PA≡PA : conv (congPTy Γ≡Γ' PΓ≡PΓ' A≡A') PA ≡ PA')
      {Pσ : PSub PΔ PΓ σ}{Pσ' : PSub PΔ' PΓ' σ'}
      (σ≡σ' : conv (congSub Δ≡Δ' Γ≡Γ') σ ≡ σ')
    → conv (congPSub Δ≡Δ' Γ≡Γ' PΔ≡PΔ' PΓ≡PΓ' σ≡σ') Pσ ≡ Pσ'
    → conv (congPTy Δ≡Δ' PΔ≡PΔ' (cong[] Γ≡Γ' A≡A' Δ≡Δ' σ≡σ')) (PA [ Pσ ]P) ≡ PA' [ Pσ' ]P
  cong[]P refl refl refl refl refl refl refl refl = refl

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
        
 
