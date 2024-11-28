-- Model of Substitution Calculus
module SC+El.QIIRT2.Model where

open import Prelude
open import SC+El.QIIRT2.Base

variable
  Γ' : Ctx
  A' : Ty _
  σ' τ' : Sub _ _

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

  congPTy : {PΓ : PCtx Γ}{A A' : Ty Γ} → A ≡ A' → PTy PΓ A ≡ PTy PΓ A'
  congPTy refl = refl

  congPSub : {PΔ : PCtx Δ}{PΓ : PCtx Γ}{Pσ : PSub PΔ PΓ σ}{Pσ' : PSub PΔ PΓ σ'}
           → σ ≡ σ' → PSub PΔ PΓ σ ≡ PSub PΔ PΓ σ'
  congPSub refl = refl

  congPTmΓ : {PΓ : PCtx Γ}{PA : PTy PΓ A}{PA' : PTy PΓ A'}
           → (A≡A' : A ≡ A')(PA≡PA' : conv (congPTy A≡A') PA ≡ PA')
           → {t : Tm Γ A}{t' : Tm Γ A'}
           → conv (congTmΓ A≡A') t ≡ t'
           → PTm PΓ PA t ≡ PTm PΓ PA' t'
  congPTmΓ refl refl refl = refl


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
  
  cong[]P
    : {PΔ : PCtx Δ}{PΓ : PCtx Γ}(PA : PTy PΓ A){Pσ : PSub PΔ PΓ σ}{Pσ' : PSub PΔ PΓ σ'}
    → (σ≡σ' : σ ≡ σ') → conv (congPSub {Pσ = Pσ} {Pσ'} σ≡σ') Pσ ≡ Pσ'
    → conv (congPTy (cong[] A σ≡σ')) (PA [ Pσ ]P) ≡ PA [ Pσ' ]P
  cong[]P PA refl refl = refl

  cong[]tmP
    : {PΔ : PCtx Δ}{PΓ : PCtx Γ}{PA : PTy PΓ A}{Pσ : PSub PΔ PΓ σ}{Pσ' : PSub PΔ PΓ σ'}
    → (Pt : PTm PΓ PA t)(σ≡σ' : σ ≡ σ')(Pσ≡Pσ' : conv (congPSub {Pσ = Pσ} {Pσ'} σ≡σ') Pσ ≡ Pσ')
    ------------------------------------------------------------------------------------------------------------
    → conv (congPTmΓ (cong[] A σ≡σ') (cong[]P PA σ≡σ' Pσ≡Pσ') (cong[]tm t σ≡σ')) (Pt [ Pσ ]tmP) ≡ Pt [ Pσ' ]tmP
  cong[]tmP Pt refl refl = refl

  cong∘P
    : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PΘ : PCtx Θ}
      {Pσ : PSub PΔ PΓ σ}{Pσ' : PSub PΔ PΓ σ'}
      {Pτ : PSub PΘ PΔ τ}{Pτ' : PSub PΘ PΔ τ'}
    → (σ≡σ' : σ ≡ σ')(Pσ≡Pσ' : conv (congPSub {Pσ = Pσ} {Pσ'} σ≡σ') Pσ ≡ Pσ')
      (τ≡τ' : τ ≡ τ')(Pτ≡Pτ' : conv (congPSub {Pσ = Pτ} {Pτ'} τ≡τ') Pτ ≡ Pτ')
    ----------------------------------------------------------------------------
    → conv (congPSub {Pσ = Pσ ∘P Pτ} {Pσ' ∘P Pτ'} (cong∘ σ≡σ' τ≡τ')) (Pσ ∘P Pτ) ≡ Pσ' ∘P Pτ'
  cong∘P refl refl refl refl = refl

  congπ₁P
    : {PΔ : PCtx Δ}{PΓ : PCtx Γ}{PA : PTy PΓ A}
      {Pσ : PSub PΔ (PΓ ,Ctx PA) σ}{Pσ' : PSub PΔ (PΓ ,Ctx PA) σ'}
    → (σ≡σ' : σ ≡ σ') → conv (congPSub {Pσ = Pσ} {Pσ'} σ≡σ') Pσ ≡ Pσ'
    -------------------------------------------------
    → conv (congPSub {Pσ = π₁P Pσ} {π₁P Pσ'} (congπ₁ σ≡σ')) (π₁P Pσ) ≡ π₁P Pσ'
  congπ₁P refl refl = refl

  congπ₂P
    : {PΔ : PCtx Δ}{PΓ : PCtx Γ}{PA : PTy PΓ A}
      {Pσ : PSub PΔ (PΓ ,Ctx PA) σ}{Pσ' : PSub PΔ (PΓ ,Ctx PA) σ'}
    → (σ≡σ' : σ ≡ σ')(Pσ≡Pσ' : conv (congPSub {Pσ = Pσ} {Pσ'} σ≡σ') Pσ ≡ Pσ')
    -------------------------------------------------
    → conv (congPTmΓ (cong[] A (congπ₁ σ≡σ')) (cong[]P PA (congπ₁ σ≡σ') (congπ₁P σ≡σ' Pσ≡Pσ')) (congπ₂ σ≡σ')) (π₂P Pσ) ≡ π₂P Pσ'
  congπ₂P refl refl = refl


{-
record IHEq {i j}(P : Pdc {i} {j})(indP : IH P) : Set (i ⊔ j) where
  open Pdc P
  open IH indP
  field   
    -- induction on equalities
    PU[] 
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{Pσ : PSub PΔ PΓ σ}
      -------------------
      → PU [ Pσ ]P ≡ PU
    [PidS]
      : {PΓ : PCtx Γ}
      → (PA : PTy PΓ A)
      -----------------
      → conv (congPTy refl refl ([idS] A)) (PA [ PidS ]P) ≡ PA
    [∘P]
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PΘ : PCtx Θ}
      → (PA : PTy PΓ A)(Pσ : PSub PΔ PΓ σ)(Pτ : PSub PΘ PΔ τ)
      -----------------------------------------------------------------
      → conv (congPTy refl refl ([∘] A σ τ)) (PA [ Pσ ∘P Pτ ]P) ≡ PA [ Pσ ]P [ Pτ ]P
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
    ‣∘P -- the transport equation seems too long
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PΘ : PCtx Θ}
      → {PA : PTy PΓ A}{Pσ : PSub PΔ PΓ σ}{Pt : PTm PΔ (PA [ Pσ ]P) t}{Pτ : PSub PΘ PΔ τ}
      ------------------------------------------------------------------------------------------
      → conv (congPSub refl refl refl refl ‣∘) ((Pσ ‣Sub Pt) ∘P Pτ) ≡ (Pσ ∘P Pτ) ‣Sub conv (sym (congPTm refl refl ([∘] A σ τ) ([∘P] PA Pσ Pτ) 
                                                                                                        (trans (conv² (congTm refl (sym ([∘] A σ τ))) (congTm refl ([∘] A σ τ)))
                                                                                                               (trans (cong (λ y → conv y (t [ τ ]tm)) (trans-congTmΓ {p = sym ([∘] A σ τ)} {[∘] A σ τ}))
                                                                                                                      (cong (λ y → conv (congTmΓ y) (t [ τ ]tm)) (trans-symˡ ([∘] A σ τ)))))))
                                                                                           (Pt [ Pτ ]tmP)
    Pβπ₁
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PA : PTy PΓ A}
      → {Pσ : PSub PΔ PΓ σ}{Pt : PTm PΔ (PA [ Pσ ]P) t}
      ----------------------------------------------
      → conv (congPSub refl refl refl refl βπ₁) (π₁P (Pσ ‣Sub Pt)) ≡ Pσ
    Pηπ
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PA : PTy PΓ A}
      → {Pσ : PSub PΔ (PΓ ‣Ctx PA) σ}
      -------------------------------
      → conv (congPSub refl refl refl refl ηπ) Pσ ≡ π₁P Pσ ‣Sub π₂P Pσ
    Pη∅
      : {PΔ : PCtx Δ}
      → {Pσ : PSub PΔ ∅Ctx σ}
      ---------------------
      → conv (congPSub refl refl refl refl η∅) Pσ ≡ ∅Sub
        
-} 