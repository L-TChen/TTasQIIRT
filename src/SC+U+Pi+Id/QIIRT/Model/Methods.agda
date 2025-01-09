-- Methods of Model of Substitution Calculus
module SC+U+Pi+Id.QIIRT.Model.Methods where

open import Prelude
  hiding (_,_)
open import Data.Nat hiding (_⊔_)
open import SC+U+Pi+Id.QIIRT.Base
open import SC+U+Pi+Id.QIIRT.Properties
open import SC+U+Pi+Id.QIIRT.Model.Motives

module _ {ℓ ℓ′}(Mot : Motive {ℓ} {ℓ′}) where
  open Motive Mot
  private variable
    Γᴹ Δᴹ Θᴹ : Ctxᴹ Γ
    σᴹ τᴹ γᴹ : Subᴹ Δᴹ Γᴹ σ
    Aᴹ Bᴹ Cᴹ : Tyᴹ Γᴹ i A
    aᴹ tᴹ uᴹ : Tmᴹ Γᴹ Aᴹ t
    p : Tm Γ (Id a t u)
    
  record Method : Set (ℓ ⊔ ℓ′) where
    field
      -- induction on type and term substitution function
      [_]ᴹ_
        : (σᴹ : Subᴹ Δᴹ Γᴹ σ)(Aᴹ : Tyᴹ Γᴹ i A)
        → Tyᴹ Δᴹ i ([ σ ] A)
      
    -- TmᴹFamₛ : {Γᴹ : Ctxᴹ Γ}{Δᴹ : Ctxᴹ Δ}(Aᴹ : Tyᴹ Δᴹ i A){t : Tm Γ ([ σ ] A)} → (σᴹ : Subᴹ Γᴹ Δᴹ σ) → Set ℓ′
    -- TmᴹFamₛ {Γᴹ = Γᴹ} Aᴹ {t} σᴹ = Tmᴹ Γᴹ ([ σᴹ ]ᴹ Aᴹ) t

    field
      ∅ᶜᴹ
        : Ctxᴹ ∅
      _,ᶜᴹ_
        : (Γᴹ : Ctxᴹ Γ)(Aᴹ : Tyᴹ Γᴹ i A)
        → Ctxᴹ (Γ , A)
      ∅ˢᴹ
        : Subᴹ Δᴹ ∅ᶜᴹ ∅
      _,ˢᴹ_
        : (σᴹ : Subᴹ Γᴹ Δᴹ σ)(tᴹ : Tmᴹ Γᴹ ([ σᴹ ]ᴹ Aᴹ) t)
        → Subᴹ Γᴹ (Δᴹ ,ᶜᴹ Aᴹ) (σ , t)
      idSᴹ
        : Subᴹ Δᴹ Δᴹ idS
      _⨟ᴹ_
        : (τᴹ : Subᴹ Γᴹ Δᴹ τ)(σᴹ : Subᴹ Δᴹ Θᴹ σ)
        → Subᴹ Γᴹ Θᴹ (τ ⨟ σ)
      π₁ᴹ
        : (σᴹ : Subᴹ Δᴹ (Γᴹ ,ᶜᴹ Aᴹ) σ)
        → Subᴹ Δᴹ Γᴹ (π₁ σ)
      [idSᴹ]
        : [ idSᴹ ]ᴹ Aᴹ ≡ Aᴹ
      [⨟ᴹ]ᴹ
        : [ τᴹ ⨟ᴹ σᴹ ]ᴹ Aᴹ ≡ [ τᴹ ]ᴹ ([ σᴹ ]ᴹ Aᴹ)
      [π₁ᴹ,ˢᴹ]ᴹ
        : ([ π₁ᴹ (σᴹ ,ˢᴹ tᴹ) ]ᴹ Aᴹ) ≡ [ σᴹ ]ᴹ Aᴹ
      [π₁ᴹ⨟ᴹ]ᴹ
        : [ π₁ᴹ (σᴹ ⨟ᴹ τᴹ) ]ᴹ Aᴹ ≡ [ σᴹ ]ᴹ ([ π₁ᴹ τᴹ ]ᴹ Aᴹ)
      Uᴹ
        : (i : ℕ)
        → Tyᴹ Γᴹ (suc i) (U i)
      Elᴹ
        : Tmᴹ Γᴹ (Uᴹ i) t
        → Tyᴹ Γᴹ i (El t)
      Liftᴹ
        : Tyᴹ Γᴹ i A
        → Tyᴹ Γᴹ (suc i) (Lift A)
      Πᴹ
        : (Aᴹ : Tyᴹ Γᴹ i A)(Bᴹ : Tyᴹ (Γᴹ ,ᶜᴹ Aᴹ) i B)
        → Tyᴹ Γᴹ i (Π A B)
      Idᴹ
        : (aᴹ : Tmᴹ Γᴹ (Uᴹ i) a)(tᴹ : Tmᴹ Γᴹ (Elᴹ aᴹ) t)(uᴹ : Tmᴹ Γᴹ (Elᴹ aᴹ) u)
        → Tyᴹ Γᴹ i (Id a t u)
      π₂ᴹ
        : (σᴹ : Subᴹ Δᴹ (Γᴹ ,ᶜᴹ Aᴹ) σ)
        ---------------------------------
        → Tmᴹ Δᴹ ([ π₁ᴹ σᴹ ]ᴹ Aᴹ) (π₂ σ)
      [_]tmᴹ_
        : (σᴹ : Subᴹ Γᴹ Δᴹ σ) {Aᴹ : Tyᴹ Δᴹ i A}
        → (tᴹ : Tmᴹ Δᴹ Aᴹ t)
        → Tmᴹ Γᴹ ([ σᴹ ]ᴹ Aᴹ) ([ σ ]tm t)
      cᴹ
        : Tyᴹ Γᴹ i A
        → Tmᴹ Γᴹ (Uᴹ i) (c A)
      mkᴹ
        : Tmᴹ Γᴹ Aᴹ t
        → Tmᴹ Γᴹ (Liftᴹ Aᴹ) (mk t)
      unᴹ
        : Tmᴹ Γᴹ (Liftᴹ Aᴹ) t
        → Tmᴹ Γᴹ Aᴹ (un t)
      ƛᴹ_
        : Tmᴹ (Γᴹ ,ᶜᴹ Aᴹ) Bᴹ t
        → Tmᴹ Γᴹ (Πᴹ Aᴹ Bᴹ) (ƛ t)
      appᴹ
        : Tmᴹ Γᴹ (Πᴹ Aᴹ Bᴹ) t
        → Tmᴹ (Γᴹ ,ᶜᴹ Aᴹ) Bᴹ (app t)
    _⁺ᴹ
      : (σᴹ : Subᴹ Γᴹ Δᴹ σ)
      → Subᴹ (Γᴹ ,ᶜᴹ ([ σᴹ ]ᴹ Aᴹ)) (Δᴹ ,ᶜᴹ Aᴹ) (σ ⁺)
    σᴹ ⁺ᴹ = (π₁ᴹ idSᴹ ⨟ᴹ σᴹ) ,ˢᴹ tr TmᴹFamₜ (sym $ [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ)

    field
      _↑ᴹ_
        : (σᴹ : Subᴹ Γᴹ Δᴹ σ)(Aᴹ : Tyᴹ Δᴹ i A)
        → Subᴹ (Γᴹ ,ᶜᴹ ([ σᴹ ]ᴹ Aᴹ)) (Δᴹ ,ᶜᴹ Aᴹ) (σ ↑ A)
      -- [TODO]: the definitional equalities for _↑_ should go here
      -- [TODO]: Add _↑ᴹ_ ≡ _⁺ᴾ_
      -- [TODO]: the deifnitional equalities for [_]t_ should go here
      -- [TODO]: Add [_]t_ ≡ [_]tm_
      [_]tᴹ_
        : (σᴹ : Subᴹ Δᴹ Γᴹ σ)(tᴹ : Tmᴹ Γᴹ Aᴹ t)
        → Tmᴹ Δᴹ ([ σᴹ ]ᴹ Aᴹ) ([ σ ]t t)
      [idSᴹ]tᴹ
        : tr TmᴹFamₜ [idSᴹ] ([ idSᴹ ]tᴹ tᴹ) ≡ tᴹ
      [⨟ᴹ]tᴹ
        : tr TmᴹFamₜ [⨟ᴹ]ᴹ ([ σᴹ ⨟ᴹ τᴹ ]tᴹ tᴹ)
        ≡ [ σᴹ ]tᴹ [ τᴹ ]tᴹ tᴹ
      [π₁ᴹ,ˢᴹ]tᴹ
        : tr TmᴹFamₜ [π₁ᴹ,ˢᴹ]ᴹ ([ π₁ᴹ (σᴹ ,ˢᴹ tᴹ) ]tᴹ uᴹ)
        ≡ [ σᴹ ]tᴹ uᴹ
      [π₁ᴹ⨟ᴹ]tᴹ
        : tr TmᴹFamₜ [π₁ᴹ⨟ᴹ]ᴹ ([ π₁ᴹ (σᴹ ⨟ᴹ τᴹ) ]tᴹ tᴹ)
        ≡ [ σᴹ ]tᴹ ([ π₁ᴹ τᴹ ]tᴹ tᴹ)
      -- [TODO]: Please put the remaining cases here.

      -- 
      _⨟ᴹidSᴹ
        : (σᴹ : Subᴹ Δᴹ Γᴹ σ)
        → tr SubᴹFam (σ ⨟idS) (σᴹ ⨟ᴹ idSᴹ) ≡ σᴹ
      idSᴹ⨟ᴹ_
        : (σᴹ : Subᴹ Δᴹ Γᴹ σ)
        → tr SubᴹFam (idS⨟ σ) (idSᴹ ⨟ᴹ σᴹ) ≡ σᴹ
      ⨟ᴹ-assoc
        : tr SubᴹFam ⨟-assoc (σᴹ ⨟ᴹ (τᴹ ⨟ᴹ γᴹ))
        ≡ (σᴹ ⨟ᴹ τᴹ) ⨟ᴹ γᴹ
      π₁ᴹ,ˢᴹ
        : tr (Subᴹ Γᴹ Δᴹ) π₁, (π₁ᴹ (σᴹ ,ˢᴹ tᴹ)) ≡ σᴹ
      ⨟ᴹ,ˢᴹ -- the transport equation seems too long
        : tr SubᴹFam ⨟, (σᴹ ⨟ᴹ (τᴹ ,ˢᴹ tᴹ))
        ≡ (σᴹ ⨟ᴹ τᴹ) ,ˢᴹ tr TmᴹFamₜ (sym $ [⨟ᴹ]ᴹ) ([ σᴹ ]tmᴹ tᴹ)
      η∅ˢᴹ
        : tr SubᴹFam η∅ σᴹ ≡ ∅ˢᴹ
      η,ˢᴹ
        : tr SubᴹFam η, σᴹ ≡ π₁ᴹ σᴹ ,ˢᴹ π₂ᴹ σᴹ
      [idSᴹ]tmᴹ
        : tr₂ (Tmᴹ Γᴹ) [idSᴹ] [id]tm ([ idSᴹ ]tmᴹ tᴹ)
        ≡ tᴹ
      [⨟ᴹ]tmᴹ
        : tr₂ (Tmᴹ Γᴹ) [⨟ᴹ]ᴹ [⨟]tm ([ σᴹ ⨟ᴹ τᴹ ]tmᴹ tᴹ)
        ≡ [ σᴹ ]tmᴹ ([ τᴹ ]tmᴹ tᴹ)
      π₂ᴹ,ˢᴹ
        : tr₂ (Tmᴹ Γᴹ) [π₁ᴹ,ˢᴹ]ᴹ π₂, (π₂ᴹ (σᴹ ,ˢᴹ tᴹ))
        ≡ tᴹ
      []ᴹUᴹ
        : [ σᴹ ]ᴹ (Uᴹ i) ≡ Uᴹ i
      []ᴹElᴹ
        : (σᴹ : Subᴹ Γᴹ Δᴹ σ)(uᴹ : Tmᴹ Δᴹ (Uᴹ i) u)
        → ([ σᴹ ]ᴹ (Elᴹ uᴹ)) ≡ Elᴹ (tr TmᴹFamₜ []ᴹUᴹ ([ σᴹ ]tᴹ uᴹ))
      []ᴹLiftᴹ
        : [ σᴹ ]ᴹ (Liftᴹ Aᴹ) ≡ Liftᴹ ([ σᴹ ]ᴹ Aᴹ)
      []ᴹΠᴹ
        : [ σᴹ ]ᴹ (Πᴹ Aᴹ Bᴹ) ≡ Πᴹ ([ σᴹ ]ᴹ Aᴹ) ([ σᴹ ↑ᴹ Aᴹ ]ᴹ Bᴹ)
      []ᴹIdᴹ
        : [ σᴹ ]ᴹ (Idᴹ aᴹ tᴹ uᴹ)
        ≡ Idᴹ (tr TmᴹFamₜ []ᴹUᴹ ([ σᴹ ]tᴹ aᴹ))
            (tr TmᴹFamₜ ([]ᴹElᴹ σᴹ aᴹ) ([ σᴹ ]tᴹ tᴹ))
            (tr TmᴹFamₜ ([]ᴹElᴹ σᴹ aᴹ) ([ σᴹ ]tᴹ uᴹ))
      []tᴹcᴹ
        : (σᴹ : Subᴹ Γᴹ Δᴹ σ)(Aᴹ : Tyᴹ Δᴹ i A)
        → tr₂ (Tmᴹ Γᴹ) []ᴹUᴹ ([]tc σ A) ([ σᴹ ]tmᴹ (cᴹ Aᴹ))
        ≡ cᴹ ([ σᴹ ]ᴹ Aᴹ)
      []mkᴹ
        : tr₂ (Tmᴹ Γᴹ) []ᴹLiftᴹ []mk ([ σᴹ ]tmᴹ mkᴹ tᴹ)
        ≡ mkᴹ ([ σᴹ ]tmᴹ tᴹ)
      []unᴹ
        : tr TmᴹFam ([]un σ A t) ([ σᴹ ]tmᴹ unᴹ tᴹ)
        ≡ unᴹ (tr TmᴹFamₜ []ᴹLiftᴹ ([ σᴹ ]tmᴹ tᴹ))
      Uᴹβ
        : tr TyᴹFam Uβ (Elᴹ (cᴹ Aᴹ)) ≡ Aᴹ
      Uᴹη
        : tr TmᴹFam Uη (cᴹ (Elᴹ uᴹ)) ≡ uᴹ
      Liftᴹβ
        : tr TmᴹFam Liftβ (unᴹ (mkᴹ tᴹ)) ≡ tᴹ
      Liftᴹη
        : tr TmᴹFam Liftη (mkᴹ (unᴹ tᴹ)) ≡ tᴹ
      reflectᴹ
        : (Pp : Tmᴹ Γᴹ (Idᴹ aᴹ tᴹ uᴹ) p)
        → tr TmᴹFam (reflect p) tᴹ ≡ uᴹ
      []ƛᴹ
        : tr₂ (Tmᴹ Γᴹ) []ᴹΠᴹ []ƛ ([ σᴹ ]tmᴹ (ƛᴹ tᴹ))
        ≡ ƛᴹ ([ σᴹ ↑ᴹ Aᴹ ]tmᴹ tᴹ)
      Πᴹβ
        : tr TmᴹFam Πβ (appᴹ (ƛᴹ tᴹ)) ≡ tᴹ
      Πᴹη
        : tr TmᴹFam Πη (ƛᴹ (appᴹ tᴹ)) ≡ tᴹ
      
      []tmᴹ≡[]tᴹ
        : {Γᴹ : Ctxᴹ Γ}{Δᴹ : Ctxᴹ Δ}{Aᴹ : Tyᴹ Δᴹ i A}
          (σᴹ : Subᴹ Γᴹ Δᴹ σ)(tᴹ : Tmᴹ Δᴹ Aᴹ t)
          -------------------------------------
        → tr TmᴹFam ([]tm≡[]t t σ) ([ σᴹ ]tmᴹ tᴹ) ≡ [ σᴹ ]tᴹ tᴹ
      ↑ᴹ=⁺ᴹ
        : {Γᴹ : Ctxᴹ Γ}{Δᴹ : Ctxᴹ Δ}
          (σᴹ : Subᴹ Γᴹ Δᴹ σ)(Aᴹ : Tyᴹ Δᴹ i A)
          --------------------------------------------------------------------------
        → tr (Subᴹ (Γᴹ ,ᶜᴹ ([ σᴹ ]ᴹ Aᴹ)) (Δᴹ ,ᶜᴹ Aᴹ)) (↑=⁺ A σ) (σᴹ ↑ᴹ Aᴹ) ≡ σᴹ ⁺ᴹ

 
