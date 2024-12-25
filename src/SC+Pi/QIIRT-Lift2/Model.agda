-- Model of Substitution Calculus
module SC+Pi.QIIRT-Lift2.Model where

open import Prelude
  hiding (_,_)
open import SC+Pi.QIIRT-Lift2.Base
open import SC+Pi.QIIRT-Lift2.Cong

variable
  As : Lift _

record Pdc {i j} : Set (lsuc (i ⊔ j)) where
  field
    PCtx
      : Ctx → Set i
    PLift
      : PCtx Γ → Lift Γ → Set i
    PTy
      : PCtx Γ → Ty Γ → Set i
    PSub
      : PCtx Δ → PCtx Γ → Sub Δ Γ → Set j
    PTm
      : (PΓ : PCtx Γ) → PTy PΓ A → Tm Γ A → Set j
  PCtx` : Γ ≡ Γ' →  PCtx Γ ≡ PCtx Γ'
  PCtx` = cong PCtx

  PLiftPΓ` : {PΓ : PCtx Γ}{As As' : Lift Γ} → As ≡ As' → PLift PΓ As ≡ PLift PΓ As'
  PLiftPΓ`{PΓ = PΓ} = cong (PLift PΓ)

  PTy` : {PΓ : PCtx Γ}{PΓ' : PCtx Γ'}
       → (Γ≡Γ' : Γ ≡ Γ')(PΓ≡PΓ' : conv (PCtx` Γ≡Γ') PΓ ≡ PΓ')(A≡A' : conv (Ty` Γ≡Γ') A ≡ A')
       → PTy PΓ A ≡ PTy PΓ' A'
  PTy` refl = cong₂ PTy

  PTyPΓ` : {PΓ : PCtx Γ}{A A' : Ty Γ} → A ≡ A' → PTy PΓ A ≡ PTy PΓ A'
  PTyPΓ` {PΓ = PΓ} = PTy` {PΓ = PΓ} refl refl

  PTm` : {PΓ : PCtx Γ}{PΓ' : PCtx Γ'}{PA : PTy PΓ A}{PA' : PTy PΓ' A'}
       → (Γ≡Γ' : Γ ≡ Γ')(PΓ≡PΓ' : conv (PCtx` Γ≡Γ') PΓ ≡ PΓ')
         (A≡A' : conv (Ty` Γ≡Γ') A ≡ A'){t : Tm Γ A}{t' : Tm Γ' A'}
       → conv (PTy` Γ≡Γ' PΓ≡PΓ' A≡A') PA ≡ PA' → conv (Tm` Γ≡Γ' A≡A') t ≡ t'
       → PTm PΓ PA t ≡ PTm PΓ' PA' t'
  PTm` {PΓ = PΓ} {PA = PA} refl refl refl = cong₂ (PTm PΓ)
  
  PTmPΓ`
    : {PΓ : PCtx Γ}{PA : PTy PΓ A}{PA' : PTy PΓ A'}{t : Tm Γ A}{t' : Tm Γ A'}
    → (A≡A' : A ≡ A') → conv (PTyPΓ` A≡A') PA ≡ PA' → conv (TmΓ` A≡A') t ≡ t'
    ---------------------------------------------------------------------------------------
    → PTm PΓ PA t ≡ PTm PΓ PA' t'
  PTmPΓ` {PΓ = PΓ} refl = cong₂ (PTm PΓ)

  PSub`
    : {PΓ : PCtx Γ}{PΓ' : PCtx Γ'}{PΔ : PCtx Δ}{PΔ' : PCtx Δ'}
      (Γ≡Γ' : Γ ≡ Γ')(PΓ≡PΓ' : conv (PCtx` Γ≡Γ') PΓ ≡ PΓ')
      (Δ≡Δ' : Δ ≡ Δ')(PΔ≡PΔ' : conv (PCtx` Δ≡Δ') PΔ ≡ PΔ')
    → conv (Sub` Γ≡Γ' Δ≡Δ') σ ≡ σ' → PSub PΓ PΔ σ ≡ PSub PΓ' PΔ' σ'
  PSub` refl refl refl refl refl = refl

  PSubPΓ`
    : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PΔ' : PCtx Δ'}
    → (Δ≡Δ' : Δ ≡ Δ')(PΔ≡PΔ' : conv (PCtx` Δ≡Δ') PΔ ≡ PΔ')
    → conv (Sub` refl Δ≡Δ') σ ≡ σ' → PSub PΓ PΔ σ ≡ PSub PΓ PΔ' σ'
  PSubPΓ` {PΓ = PΓ} = PSub` {PΓ = PΓ} refl refl

record IH-Ctx-Lift {i j}(P : Pdc {i} {j}) : Set (i ⊔ j) where
  open Pdc P
  field
    -- induction on recursions
    _++P_
      : (PΓ : PCtx Γ)(PAs : PLift PΓ As)
      → PCtx (Γ ++ As)
    [_]lP_
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}
        (Pσ : PSub PΓ PΔ σ)(PAs : PLift PΔ As)
      →  PLift PΓ ([ σ ]l As)
    [_⇈_]P_
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}
        (PAs : PLift PΔ As)(Pσ : PSub PΓ PΔ σ)(PA : PTy (PΔ ++P PAs) A)
      →  PTy (PΓ ++P ([ Pσ ]lP PAs)) ([ As ⇈ σ ] A)
    
    -- induction on contexts and liftings
    ∅Ctx
      : PCtx ∅
    _,Ctx_
      : (PΓ : PCtx Γ)(PA : PTy PΓ A)
      ------------------------------
      → PCtx (Γ , A)
    ∅Lift
      : {PΓ : PCtx Γ} → PLift PΓ ∅
    _,Lift_
      : {PΓ : PCtx Γ}(PAs : PLift PΓ As)(PA : PTy (PΓ ++P PAs) A)
      → PLift PΓ (As , A)

    -- induction on equalities about liftings
    ++P∅
      : (PΓ : PCtx Γ)
      → PΓ ++P ∅Lift ≡ PΓ
    ++P,
      : (PΓ : PCtx Γ)(PAs : PLift PΓ As)(PA : PTy (PΓ ++P PAs) A)
      → PΓ ++P (PAs ,Lift PA) ≡ (PΓ ++P PAs) ,Ctx PA
    ∅[]lP
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}(Pσ : PSub PΓ PΔ σ)
      → [ Pσ ]lP ∅Lift ≡ ∅Lift
    ,[]lP
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}(Pσ : PSub PΓ PΔ σ)
        (PAs : PLift PΔ As)(PA : PTy (PΔ ++P PAs) A)
      → [ Pσ ]lP (PAs ,Lift PA) ≡ ([ Pσ ]lP PAs) ,Lift ([ PAs ⇈ Pσ ]P PA)
  
  ,Ctx`
    : {PΓ PΓ' : PCtx Γ}{PA : PTy PΓ A}{PA' : PTy PΓ' A}
    → (PΓ≡PΓ' : PΓ ≡ PΓ')(PA≡PA' : conv (PTy` refl PΓ≡PΓ' refl) PA ≡ PA')
    → PΓ ,Ctx PA ≡ PΓ' ,Ctx PA'
  ,Ctx` refl refl = refl
  
  [_]P_
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}
        (Pσ : PSub PΓ PΔ σ)(PA : PTy PΔ A)
      →  PTy PΓ ([ σ ] A)
  [_]P_ {PΓ = PΓ} {PΔ} Pσ PA = conv (PTy` refl eq refl) ([ ∅Lift ⇈ Pσ ]P conv (PTy` refl (sym (++P∅ PΔ)) refl) PA)
    where
      eq : PΓ ++P ([ Pσ ]lP ∅Lift) ≡ PΓ
      eq = trans (cong (PΓ ++P_) (∅[]lP Pσ)) (++P∅ PΓ)

record IH {i j}(P : Pdc {i} {j})(indCL : IH-Ctx-Lift P) : Set (i ⊔ j) where
  open Pdc P
  open IH-Ctx-Lift indCL
  field
    -- induction on substitutions
    ∅Sub
      : {PΔ : PCtx Δ}
      ---------------
      → PSub PΔ ∅Ctx ∅
    _,Sub_
      : {PΔ : PCtx Δ}{PΓ : PCtx Γ}{PA : PTy (PΓ ++P ∅Lift) A}
        (Pσ : PSub PΔ PΓ σ)(Pt : PTm (PΔ ++P ([ Pσ ]lP ∅Lift)) ([_⇈_]P_ ∅Lift Pσ PA) t)
      --------------------------------------------------
      → PSub PΔ (PΓ ,Ctx conv (PTy` refl (++P∅ PΓ) refl) PA) (σ , t)
    PidS
      : {PΔ : PCtx Γ}
      ---------------
      → PSub PΔ PΔ idS
    _⨟P_
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PΘ : PCtx Θ}
        (Pσ : PSub PΓ PΔ σ)(Pτ : PSub PΔ PΘ τ)
      -----------------------------------------
      → PSub PΓ PΘ (σ ⨟ τ)
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
    PΠ
      : {PΓ : PCtx Γ}
        (PA : PTy PΓ A)(PB : PTy (PΓ ,Ctx PA) B)
      ------------------------------------------
      → PTy PΓ (Π A B)
    PU[] 
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}
        (PΞ : PLift PΔ Ξ)(Pσ : PSub PΓ PΔ σ)
      --------------------------------------
      → [ PΞ ⇈ Pσ ]P PU ≡ PU
    PΠ[]
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ} -- {PB : PTy (PΔ ,Ctx PA) B}
      → (PΞ : PLift PΔ Ξ)(Pσ : PSub PΓ PΔ σ){PA : PTy (PΔ ++P PΞ) A}{PB : PTy ((PΔ ++P PΞ) ,Ctx PA) B}
      → [ PΞ ⇈ Pσ ]P PΠ PA PB ≡ PΠ ([ PΞ ⇈ Pσ ]P PA) (conv (PTy` refl (trans (cong (PΓ ++P_) (,[]lP Pσ PΞ PA)) (++P, PΓ ([ Pσ ]lP PΞ) ([ PΞ ⇈ Pσ ]P PA))) refl)
                                                           ([ (PΞ ,Lift PA) ⇈ Pσ ]P conv (PTy` refl (sym (++P, PΔ PΞ PA)) refl) PB))
    
    -- induction on terms
    π₂P
      : {PΔ : PCtx Δ}{PΓ : PCtx Γ}{PA : PTy PΓ A}
        (Pσ : PSub PΔ (PΓ ,Ctx PA) σ)
      ---------------------------------
      → PTm PΔ ([ π₁P Pσ ]P PA) (π₂ σ)
    [_⇈_]tP_
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}
      → (PΞ : PLift PΔ Ξ)(Pσ : PSub PΓ PΔ σ)
        {PA : PTy (PΔ ++P PΞ) A}(Pt : PTm (PΔ ++P PΞ) PA t)
      → PTm (PΓ ++P ([ Pσ ]lP PΞ)) ([ PΞ ⇈ Pσ ]P PA) ([ Ξ ⇈ σ ]t t)
    Pabs
      : {PΓ : PCtx Γ}{PA : PTy PΓ A}{PB : PTy (PΓ ,Ctx PA) B}
      → PTm (PΓ ,Ctx PA) PB t
      → PTm PΓ (PΠ PA PB) (abs t)
    Papp
      : {PΓ : PCtx Γ}{PA : PTy PΓ A}{PB : PTy (PΓ ,Ctx PA) B}
      → PTm PΓ (PΠ PA PB) t
      → PTm (PΓ ,Ctx PA) PB (app t)
  
  [_]tP_
      : {PΓ : PCtx Γ}{PA : PTy PΓ A}{PΔ : PCtx Δ}
        (Pσ : PSub PΔ PΓ σ)(Pt : PTm PΓ PA t)
      ---------------------------------------
      → PTm PΔ ([ Pσ ]P PA) ([ σ ]t t)
  [_]tP_ {PΓ = PΓ} {PΔ = PΔ} Pσ Pt = conv (PTm` refl eq refl refl refl) ([ ∅Lift ⇈ Pσ ]tP conv (PTm` refl (sym (++P∅ PΓ)) refl refl refl) Pt)
    where
      eq : PΔ ++P ([ Pσ ]lP ∅Lift) ≡ PΔ
      eq = trans (cong (PΔ ++P_) (∅[]lP Pσ)) (++P∅ PΔ)

{-
record IHEq {i j}(P : Pdc {i} {j})(indCL : IH-Ctx-Lift P)(indP : IH P indCL) : Set (i ⊔ j) where
  open Pdc P
  open IH-Ctx-Lift indCL
  open IH indP
  field   
    -- induction on equalities of lift substitutions
    [PidS]lP
      : {PΓ : PCtx Γ}{PΞ : PLift PΓ Ξ}
      → [ PidS ]lP PΞ ≡ PΞ
    [⨟P]lP
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PΘ : PCtx Θ}
        {Pσ : PSub PΓ PΔ σ}{Pτ : PSub PΔ PΘ τ}{PΞ : PLift PΘ Ξ}
      → [ Pσ ⨟P Pτ ]lP PΞ ≡ [ Pσ ]lP [ Pτ ]lP PΞ
    [π₁,]lP
      : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PA : PTy PΓ A}
        {Pσ : PSub PΓ PΔ σ}{Pt : PTm PΓ PA t}{PΞ : PLift (PΓ ,Ctx PA) Ξ}
      → [ π₁P (conv {!   !}
              (Pσ ,Sub conv (PTm` refl (sym (trans (cong (PΓ ++P_) (∅[]lP Pσ)) (++P∅ PΓ))) refl {!   !} refl)
                             Pt)) ]lP PΞ
      ≡ {!   !}
    -- [PidS]
    --   : {PΓ : PCtx Γ}
    --   → (PA : PTy PΓ A)
    --   -----------------
    --   → PA [ PidS ]P ≡ PA
    -- [∘P]
    --   : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PΘ : PCtx Θ}
    --   → (PA : PTy PΓ A)(Pσ : PSub PΔ PΓ σ)(Pτ : PSub PΘ PΔ τ)
    --   -----------------------------------------------------------------
    --   → PA [ Pσ ∘P Pτ ]P ≡ PA [ Pσ ]P [ Pτ ]P
    -- PidS∘P_
    --   : {PΓ : PCtx Γ}{PΔ : PCtx Γ}
    --   → (Pσ : PSub PΔ PΓ σ)
    --   ---------------------
    --   → conv (cong (PSub PΔ PΓ) (idS∘ σ)) (PidS ∘P Pσ) ≡ Pσ
    -- _∘PPidS
    --   : {PΓ : PCtx Γ}{PΔ : PCtx Γ}
    --   → (Pσ : PSub PΔ PΓ σ)
    --   ---------------------
    --   → conv (cong (PSub PΔ PΓ) (σ ∘idS)) (Pσ ∘P PidS) ≡ Pσ
    -- PassocS
    --   : {υ : Sub Φ Θ}{PΓ : PCtx Γ}{PΔ : PCtx Γ}{PΘ : PCtx Θ}{PΦ : PCtx Φ}
    --   → {Pσ : PSub PΔ PΓ σ}{Pτ : PSub PΘ PΔ τ}{Pυ : PSub PΦ PΘ υ}
    --   --------------------------------------------------------------
    --   → conv (cong (PSub PΦ PΓ) assocS) ((Pσ ∘P Pτ) ∘P Pυ) ≡ Pσ ∘P (Pτ ∘P Pυ)
    -- Pπ₁,
    --   : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PA : PTy PΓ A}
    --   → {Pσ : PSub PΔ PΓ σ}{Pt : PTm PΔ (PA [ Pσ ]P) t}
    --   -------------------------------------------------
    --   → conv (cong (PSub PΔ PΓ) π₁,) (π₁P (Pσ ,Sub Pt)) ≡ Pσ
    -- -- Pπ₂,
    -- --   : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PA : PTy PΓ A}
    -- --   → {Pσ : PSub PΔ PΓ σ}{Pt : PTm PΔ (PA [ Pσ ]P) t}
    -- --   -------------------------------------------------
    -- --   → conv {!   !} (π₂P (Pσ ,Sub Pt)) ≡ Pt
    -- ,∘P -- the transport equation seems too long
    --   : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PΘ : PCtx Θ}
    --   → {PA : PTy PΓ A}{Pσ : PSub PΔ PΓ σ}{Pt : PTm PΔ (PA [ Pσ ]P) t}{Pτ : PSub PΘ PΔ τ}
    --   ------------------------------------------------------------------------------------------
    --   → conv (cong (PSub PΘ (PΓ ,Ctx PA)) ,∘) ((Pσ ,Sub Pt) ∘P Pτ) ≡ ((Pσ ∘P Pτ) ,Sub conv (PTmPΓ` refl (sym ([∘P] PA Pσ Pτ)) ([]tm≡[]t t τ)) (Pt [ Pτ ]tmP))
    -- Pη∅
    --   : {PΔ : PCtx Δ}
    --   → {Pσ : PSub PΔ ∅Ctx σ}
    --   ------------------------------------------
    --   → conv (cong (PSub PΔ ∅Ctx) η∅) Pσ ≡ ∅Sub
    -- Pηπ
    --   : {PΓ : PCtx Γ}{PΔ : PCtx Δ}{PA : PTy PΓ A}
    --   → {Pσ : PSub PΔ (PΓ ,Ctx PA) σ}
    --   -------------------------------
    --   → conv (cong (PSub PΔ (PΓ ,Ctx PA)) η,) Pσ ≡ π₁P Pσ ,Sub π₂P Pσ
-} 