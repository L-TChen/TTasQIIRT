-- Methods of Model of Substitution Calculus
module SC+U+Pi+Id.QIIRT.Model.Methods where

open import Prelude
  hiding (_,_)
open import Data.Nat hiding (_⊔_)
open import SC+U+Pi+Id.QIIRT.Base
open import SC+U+Pi+Id.QIIRT.Properties
open import SC+U+Pi+Id.QIIRT.Model.Motives

module _ {ℓ ℓ′} (P : Pred {ℓ} {ℓ′}) where
  open Pred P

  private variable
    PΓ PΔ PΘ : PCtx Δ
    PA PB    : PTy PΔ i A
    Pσ Pτ Pγ : PSub PΔ PΘ σ
    Pt Pu Pa : PTm PΓ PA t
    
  module _
    -- constructors before Ty and Sub
    (P[_]_
      : {Γ : Ctx} {PΓ : PCtx Γ} {Δ : Ctx} {PΔ : PCtx Δ} {σ : Sub Γ Δ} {i : ℕ} {A : Ty Δ i} (Pσ : PSub PΓ PΔ σ) (PA : PTy PΔ i A)
      → PTy PΓ i ([ σ ] A))
    (PCtx∅ : PCtx ∅)
    (_,PCtx_
      : {Γ : Ctx} {i : ℕ} {A : Ty Γ i} (PΓ : PCtx Γ) (PA : PTy PΓ i A)
      → PCtx (Γ , A))
    {Γ : Ctx}
    (PΓ : Pred.PCtx P Γ) where
  -- generalised variables will be shadowed by this module parameter PΓ 

    PTyΓ : (i : ℕ) → Ty Γ i → Set ℓ
    PTyΓ  = PTy PΓ

    PSubΓ : PCtx Δ → Sub Γ Δ → Set ℓ′
    PSubΓ = PSub PΓ 

    PTmΓ : PTyΓ i A → Tm Γ A → Set _
    PTmΓ = PTm PΓ

    record MethodOver : Set (ℓ ⊔ ℓ′) where
      field
        PSub∅
          : PSubΓ PCtx∅ ∅
        _,PSub_
          : (Pσ : PSubΓ PΔ σ) (Pt : PTm PΓ (P[ Pσ ] PA) t)
          → PSubΓ (PΔ ,PCtx PA) (σ , t)
        PidS
          : PSubΓ PΓ idS
        _P⨟_
          : (Pσ : PSubΓ PΔ σ)(Pτ : PSub PΔ PΘ τ)
          → PSubΓ PΘ (σ ⨟ τ)
        Pπ₁
          : PSubΓ (PΔ ,PCtx PA) σ
          → PSubΓ PΔ (π₁ σ)
        P⟨_⟩
          : PTmΓ PA t
          → PSubΓ (PΓ ,PCtx PA) ⟨ t ⟩
        PU
          : (i : ℕ)
          → PTyΓ (suc i) (U i)
        PEl
          : PTm PΓ (PU i) u
          → PTyΓ i (El u)
        PLift
          : PTyΓ i       A
          → PTyΓ (suc i) (Lift A)
        PΠ
          : (PA : PTyΓ i A) (PB : PTy (PΓ ,PCtx PA) i B)
          → PTyΓ i (Π A B)
        PId
          : {a : Tm Γ (U i)} {t u : Tm Γ (El a)}
          → (Pa : PTmΓ (PU i) a)
            (Pt : PTmΓ (PEl Pa) t) (Pu : PTmΓ (PEl Pa) u)
          → PTyΓ i (Id a t u)

  record Method : Set (ℓ ⊔ ℓ′) where
    field
      P[_]_
        : (Pσ : PSub PΓ PΔ σ) (PA : PTy PΔ i A)
        → PTy PΓ i ([ σ ] A)
      ∅Ctx
        : PCtx ∅
      _,Ctx_
        : (PΓ : PCtx Γ) (PA : PTy PΓ i A)
        → PCtx (Γ , A)
      PSubTyOp
        : (PΓ : PCtx Γ) → MethodOver P[_]_ ∅Ctx _,Ctx_ PΓ
    
    PTmFamₛ : (PA : PTy PΔ i A) {t : Tm Γ ([ σ ] A)}
            → (Pσ : PSub PΓ PΔ σ) → Set ℓ′
    PTmFamₛ PA {t} Pσ = PTm _ (P[ Pσ ] PA) t

    -- unfold the definitions in IndCtorOver manually
    PSub∅
      : PSub PΓ ∅Ctx ∅
    PSub∅ = PSubTyOp _ .MethodOver.PSub∅

    _,PSub_
      : (Pσ : PSub PΓ PΔ σ) (Pt : PTm PΓ (P[ Pσ ] PA) t)
      → PSub PΓ (PΔ ,Ctx PA) (σ , t)
    _,PSub_ = PSubTyOp _ .MethodOver._,PSub_

    PidS
      : PSub PΓ PΓ idS
    PidS = PSubTyOp _ .MethodOver.PidS

    _P⨟_
      : (Pσ : PSub PΓ PΔ σ) (Pτ : PSub PΔ PΘ τ)
      → PSub PΓ PΘ (σ ⨟ τ)
    _P⨟_ = PSubTyOp _ .MethodOver._P⨟_

    Pπ₁
      : (Pσ : PSub PΓ (PΔ ,Ctx PA) σ)
      → PSub PΓ PΔ (π₁ σ)
    Pπ₁ = PSubTyOp _ .MethodOver.Pπ₁

    P⟨_⟩
      : PTm PΓ PA t
      → PSub PΓ (PΓ ,Ctx PA) ⟨ t ⟩
    P⟨_⟩ = PSubTyOp _ .MethodOver.P⟨_⟩

    PU
      : (i : ℕ)
      → PTy PΓ (suc i) (U i)
    PU = PSubTyOp _ .MethodOver.PU

    PEl
      : PTm PΓ (PU i) u
      → PTy PΓ i (El u)
    PEl = PSubTyOp _ .MethodOver.PEl

    PLift
      : PTy PΓ i       A
      → PTy PΓ (suc i) (Lift A)
    PLift = PSubTyOp _ .MethodOver.PLift

    PΠ
      : (PA : PTy PΓ i A) (PB : PTy (PΓ ,Ctx PA) i B)
      → PTy PΓ i (Π A B)
    PΠ = PSubTyOp _ .MethodOver.PΠ

    PId
      : {a : Tm Γ (U i)} {t u : Tm Γ (El a)}
      → (Pa : PTm PΓ (PU i) a)
        (Pt : PTm PΓ (PEl Pa) t) (Pu : PTm PΓ (PEl Pa) u)
      → PTy PΓ i (Id a t u)
    PId = PSubTyOp _.MethodOver.PId

    field
      Pπ₂
        : (Pσ : PSub PΓ (PΔ ,Ctx PA) σ)
        → PTm PΓ (P[ Pπ₁ Pσ ] PA) (π₂ σ)
      P[_]tm_
        : (Pσ : PSub PΓ PΔ σ)(Pt : PTm PΔ PA t)
        ---------------------------------------
        → PTm PΓ (P[ Pσ ] PA) ([ σ ]tm t)
      Pc
        : PTy PΓ i A
        → PTm PΓ (PU i) (c A)
      Pmk
        : (Pt : PTm PΓ PA t)
        → PTm PΓ (PLift PA) (mk t)
      Pun
        : (Pt : PTm PΓ (PLift PA) t)
        → PTm PΓ PA (un t)
      Pƛ_
        : PTm (PΓ ,Ctx PA) PB t
        → PTm PΓ (PΠ PA PB) (ƛ t)
      Papp
        : PTm PΓ (PΠ PA PB) t
        → PTm (PΓ ,Ctx PA) PB (app t)
      _P⁺
        : (Pσ : PSub PΓ PΔ σ) {PA : PTy PΔ i A}
        → PSub (PΓ ,Ctx (P[ Pσ ] PA)) (PΔ ,Ctx PA) (σ ⁺)
      _P↑_
        : (Pσ : PSub PΓ PΔ σ) (PA : PTy PΔ i A)
        → PSub (PΓ ,Ctx (P[ Pσ ] PA)) (PΔ ,Ctx PA) (σ ↑ A)
      P[_]t_
        : (Pσ : PSub PΓ PΔ σ)(Pt : PTm PΔ PA u)
        → PTm PΓ (P[ Pσ ] PA) ([ σ ]t u)

  --module _ (indC : IndCtor) where
  --  open IndCtor indC
  --  record IndRec : Set (ℓ ⊔ ℓ′) where
  
    field
      -- Induction on computation rules of [_]_
      ---- compute [_]P_ w.r.t. substitutions
      [PidS]
        : P[ PidS ] PA ≡ PA
      [P⨟]
        : P[ Pτ P⨟ Pσ ] PA ≡ P[ Pτ ] P[ Pσ ] PA
      [Pπ₁,]
        : P[ Pπ₁ (Pσ ,PSub Pt) ] PA ≡ P[ Pσ ] PA
      [Pπ₁⨟]
        : P[ Pπ₁ (Pσ P⨟ Pτ) ] PA ≡ P[ Pσ ] P[ Pπ₁ Pτ ] PA
      -- compute [_]tP_ w.r.t substitutions
      [PidS]tP
        : tr PTmFamₜ [PidS] (P[ PidS ]t Pt) ≡ Pt
      [⨟P]tP
        : tr PTmFamₜ [P⨟] (P[ Pσ P⨟ Pτ ]t Pt) ≡ P[ Pσ ]t (P[ Pτ ]t Pt)
      [π₁P,Sub]tP
        : tr PTmFamₜ [Pπ₁,] (P[ Pπ₁ (Pσ ,PSub Pt) ]t Pu) ≡ P[ Pσ ]t Pu
      [π₁P⨟P]tP
        : tr PTmFamₜ [Pπ₁⨟] (P[ Pπ₁ (Pσ P⨟ Pτ) ]t Pt)
        ≡ P[ Pσ ]t (P[ Pπ₁ Pτ ]t Pt)
-- Should we put rest of each cases here or catch all ?

      ---- compute [_]P_ w.r.t. types 
      []PU
        : P[ Pσ ] (PU i) ≡ PU i
      []PEl
        : (Pσ : PSub PΓ PΔ σ) (Pu : PTm PΔ (PU i) u)
        → (P[ Pσ ] (PEl Pu)) ≡ PEl (tr PTmFamₜ []PU (P[ Pσ ]t Pu))
      []PLift
        : P[ Pσ ] (PLift PA) ≡ PLift (P[ Pσ ] PA)
      []PΠ
        : (Pσ : PSub PΓ PΔ σ)
        → P[ Pσ ] (PΠ PA PB) ≡ PΠ (P[ Pσ ] PA) (P[ Pσ P↑ PA ] PB)
      []PId
        : P[ Pσ ] (PId Pa Pt Pu)
        ≡ PId (tr PTmFamₜ []PU (P[ Pσ ]t Pa))
          (tr PTmFamₜ ([]PEl Pσ Pa) (P[ Pσ ]t Pt))
          (tr PTmFamₜ ([]PEl Pσ Pa) (P[ Pσ ]t Pu))
      _⁺ᴾ
        : (Pσ : PSub PΓ PΔ σ) 
        → _P⁺ Pσ {PA} ≡ (Pπ₁ PidS P⨟ Pσ) ,PSub (tr PTmFamₜ (sym $ [P⨟]) $ Pπ₂ PidS)

      _⨟PidS
        : (Pσ : PSub PΔ PΓ σ)
        --------------------------------------
        → tr PSubFam (σ ⨟idS) (Pσ P⨟ PidS) ≡ Pσ
      PidS⨟P_
        : (Pσ : PSub PΔ PΓ σ)
        ---------------------
        → tr PSubFam (idS⨟ σ) (PidS P⨟ Pσ) ≡ Pσ
      ⨟P-assoc
        : tr PSubFam ⨟-assoc (Pσ P⨟ (Pτ P⨟ Pγ)) ≡ (Pσ P⨟ Pτ) P⨟ Pγ
      π₁P,Sub
        : tr (PSub PΓ PΔ) π₁, (Pπ₁ (Pσ ,PSub Pt)) ≡ Pσ
      ⨟P,Sub -- the transport equation seems too long
        : tr PSubFam ⨟, (Pσ P⨟ (Pτ ,PSub Pt)) ≡
        (Pσ P⨟ Pτ) ,PSub tr PTmFamₜ (sym $ [P⨟]) (P[ Pσ ]tm Pt)
      η∅Sub
        : tr PSubFam η∅ Pσ ≡ PSub∅
      η,Sub
        : tr PSubFam η, Pσ ≡ Pπ₁ Pσ ,PSub Pπ₂ Pσ

      -- induction on term equality constructors
      [PidS]tmP
        : tr₂ (PTm PΓ) [PidS] [id]tm (P[ PidS ]tm Pt) ≡ Pt
      [⨟P]tmP
        : tr₂ (PTm PΓ) [P⨟] [⨟]tm (P[ Pσ P⨟ Pτ ]tm Pt) ≡ P[ Pσ ]tm (P[ Pτ ]tm Pt)
      π₂P,Sub
        : tr₂ (PTm PΓ) [Pπ₁,] π₂, (Pπ₂ (Pσ ,PSub Pt)) ≡ Pt
      []tPcP
        : (Pσ : PSub PΓ PΔ σ)(PA : PTy PΔ i A)
        → tr₂ (PTm PΓ) []PU ([]tc σ A) (P[ Pσ ]t (Pc PA))
        ≡ Pc (P[ Pσ ] PA)
      []mkP
        : tr₂ (PTm PΓ) []PLift []mk (P[ Pσ ]tm Pmk Pt)
        ≡ Pmk (P[ Pσ ]tm Pt)
      []unP
        : tr PTmFam ([]un σ A t) (P[ Pσ ]tm Pun Pt)
        ≡ Pun (tr PTmFamₜ []PLift (P[ Pσ ]tm Pt))
      PUη
        : tr PTmFam Uη (Pc (PEl Pu)) ≡ Pu
      PLiftβ
        : tr PTmFam Liftβ (Pun (Pmk Pt)) ≡ Pt
      PLiftη
        : tr PTmFam Liftη (Pmk (Pun Pt)) ≡ Pt
      reflectP
        : {p : Tm Γ (Id _ t u)}
        → (Pp : PTm PΓ (PId Pa Pt Pu) p)
          -------------------------------
        → tr PTmFam (reflect p) Pt ≡ Pu
      []ƛP
        : tr₂ (PTm PΓ) ([]PΠ Pσ) []ƛ (P[ Pσ ]tm (Pƛ Pt))
        ≡ Pƛ (P[ Pσ P↑ PA ]tm Pt)
      PΠβ
        : tr PTmFam Πβ (Papp (Pƛ Pt)) ≡ Pt
      PΠη
        : tr PTmFam Πη (Pƛ (Papp Pt)) ≡ Pt

      -- induction on type equalities
      PUβ
        : {PΓ : PCtx Γ}{PA : PTy PΓ i A}
        → tr PTyFam Uβ (PEl (Pc PA)) ≡ PA
--        ↑P=⁺ᴾ
--          : (Pσ : PSub PΓ PΔ σ)(PA : PTy PΔ i A)
--          → tr (PSub (PΓ ,Ctx (P[ Pσ ] PA)) (PΔ ,Ctx PA)) (↑=⁺ A σ) (Pσ P↑ PA) ≡ {!!} -- Pσ ⁺ᴾ
