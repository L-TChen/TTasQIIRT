-- Methods of Model of Substitution Calculus
open import Prelude

module Theory.SC+U+Pi+Id.QIIRT.Elimination.Method where

open import Theory.SC+U+Pi+Id.QIIRT.Syntax
open import Theory.SC+U+Pi+Id.QIIRT.Properties
open import Theory.SC+U+Pi+Id.QIIRT.Elimination.Motive

module _ {ℓ ℓ′}(Mot : Motive ℓ ℓ′) where
  open Motive Mot
  private variable
    Γᴹ Δᴹ Θᴹ : Ctxᴹ Γ
    σᴹ τᴹ γᴹ : Subᴹ Δᴹ Γᴹ σ
    Aᴹ Bᴹ Cᴹ : Tyᴹ Γᴹ i A
    aᴹ tᴹ uᴹ : Tmᴹ Γᴹ Aᴹ t
    p : Tm Γ (Id a t u)

  record CwF : Set (ℓ ⊔ ℓ′) where
    field
      [_]ᴹ_
        : (σᴹ : Subᴹ Γᴹ Δᴹ σ)(Aᴹ : Tyᴹ Δᴹ i A)
        → Tyᴹ Γᴹ i ([ σ ] A)
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
        : Subᴹ Γᴹ Γᴹ idS
      _⨟ᴹ_
        : (τᴹ : Subᴹ Γᴹ Δᴹ τ)(σᴹ : Subᴹ Δᴹ Θᴹ σ)
        → Subᴹ Γᴹ Θᴹ (τ ⨟ σ)
      π₁ᴹ
        : (σᴹ : Subᴹ Γᴹ (Δᴹ ,ᶜᴹ Aᴹ) σ)
        → Subᴹ Γᴹ Δᴹ (π₁ σ)
      [idSᴹ]
        : [ idSᴹ ]ᴹ Aᴹ ≡ Aᴹ
      [⨟ᴹ]ᴹ
        : [ σᴹ ⨟ᴹ τᴹ ]ᴹ Aᴹ ≡ [ σᴹ ]ᴹ ([ τᴹ ]ᴹ Aᴹ)
      [π₁ᴹ,ˢᴹ]ᴹ
        : ([ π₁ᴹ (σᴹ ,ˢᴹ tᴹ) ]ᴹ Aᴹ) ≡ [ σᴹ ]ᴹ Aᴹ
      [π₁ᴹ⨟ᴹ]ᴹ
        : [ π₁ᴹ (σᴹ ⨟ᴹ τᴹ) ]ᴹ Aᴹ ≡ [ σᴹ ]ᴹ ([ π₁ᴹ τᴹ ]ᴹ Aᴹ)
      π₂ᴹ
        : (σᴹ : Subᴹ Δᴹ (Γᴹ ,ᶜᴹ Aᴹ) σ)
        ---------------------------------
        → Tmᴹ Δᴹ ([ π₁ᴹ σᴹ ]ᴹ Aᴹ) (π₂ σ)
      [_]tmᴹ_
        : (σᴹ : Subᴹ Γᴹ Δᴹ σ) {Aᴹ : Tyᴹ Δᴹ i A}
        → (tᴹ : Tmᴹ Δᴹ Aᴹ t)
        → Tmᴹ Γᴹ ([ σᴹ ]ᴹ Aᴹ) ([ σ ]tm t)
    
    _⁺ᴹ
      : (σᴹ : Subᴹ Γᴹ Δᴹ σ)
      → Subᴹ (Γᴹ ,ᶜᴹ ([ σᴹ ]ᴹ Aᴹ)) (Δᴹ ,ᶜᴹ Aᴹ) (σ ⁺)
    σᴹ ⁺ᴹ = (π₁ᴹ idSᴹ ⨟ᴹ σᴹ) ,ˢᴹ tr TmᴹFamₜ (sym $ [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ)

    Subᴹ,ᶜᴹFam
      : {Γᴹ : Ctxᴹ Γ} → {Ctxᴹ Δ} → {Sub (Γ , A) Δ} → Tyᴹ Γᴹ i A → Set ℓ′
    Subᴹ,ᶜᴹFam {_} {_} {_} {_} {Γᴹ} {Δᴹ} {σ} Aᴹ = Subᴹ (Γᴹ ,ᶜᴹ Aᴹ) Δᴹ σ

    field
      _↑ᴹ_
        : (σᴹ : Subᴹ Γᴹ Δᴹ σ)(Aᴹ : Tyᴹ Δᴹ i A)
        → Subᴹ (Γᴹ ,ᶜᴹ ([ σᴹ ]ᴹ Aᴹ)) (Δᴹ ,ᶜᴹ Aᴹ) (σ ↑ A)

      idSᴹ↑ᴹ
        : tr Subᴹ,ᶜᴹFam [idSᴹ] (idSᴹ ↑ᴹ Aᴹ) ≡ idSᴹ
      ⨟ᴹ↑ᴹ
        : tr Subᴹ,ᶜᴹFam [⨟ᴹ]ᴹ ((σᴹ ⨟ᴹ τᴹ) ↑ᴹ Aᴹ)
        ≡ (σᴹ ↑ᴹ ([ τᴹ ]ᴹ Aᴹ)) ⨟ᴹ (τᴹ ↑ᴹ Aᴹ)
      π₁ᴹ,ˢᴹ↑ᴹ
        : tr Subᴹ,ᶜᴹFam [π₁ᴹ,ˢᴹ]ᴹ (π₁ᴹ (σᴹ ,ˢᴹ tᴹ) ↑ᴹ Aᴹ)
        ≡ σᴹ ↑ᴹ Aᴹ
      π₁ᴹ⨟ᴹ↑ᴹ
        : tr Subᴹ,ᶜᴹFam [π₁ᴹ⨟ᴹ]ᴹ (π₁ᴹ (σᴹ ⨟ᴹ τᴹ) ↑ᴹ Aᴹ)
        ≡ (σᴹ ↑ᴹ ([ π₁ᴹ τᴹ ]ᴹ Aᴹ)) ⨟ᴹ (π₁ᴹ τᴹ ↑ᴹ Aᴹ)
      ∅ˢᴹ↑ᴹ
        : ∅ˢᴹ {Δᴹ = Δᴹ} ↑ᴹ Aᴹ ≡ ∅ˢᴹ ⁺ᴹ
      ,ˢᴹ↑ᴹ
        : (σᴹ ,ˢᴹ tᴹ) ↑ᴹ Aᴹ ≡ (σᴹ ,ˢᴹ tᴹ) ⁺ᴹ
      π₁ᴹidSᴹ↑ᴹ
        : π₁ᴹ {Aᴹ = Aᴹ} idSᴹ ↑ᴹ Aᴹ ≡ π₁ᴹ idSᴹ ⁺ᴹ
      π₁ᴹπ₁ᴹ↑ᴹ
        : π₁ᴹ (π₁ᴹ σᴹ) ↑ᴹ Aᴹ ≡ π₁ᴹ (π₁ᴹ σᴹ) ⁺ᴹ

      [_]tᴹ_
        : (σᴹ : Subᴹ Γᴹ Δᴹ σ)(tᴹ : Tmᴹ Δᴹ Aᴹ t)
        → Tmᴹ Γᴹ ([ σᴹ ]ᴹ Aᴹ) ([ σ ]t t)

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
      [∅ˢᴹ]tᴹ
        : [ ∅ˢᴹ {Δ} {Δᴹ} ]tᴹ tᴹ ≡ [ ∅ˢᴹ ]tmᴹ tᴹ
      [,ˢᴹ]tᴹ
        : [ σᴹ ,ˢᴹ tᴹ ]tᴹ uᴹ ≡ [ σᴹ ,ˢᴹ tᴹ ]tmᴹ uᴹ
      [π₁ᴹidSᴹ]tᴹ
        : [ π₁ᴹ {Γᴹ = Γᴹ ,ᶜᴹ Aᴹ} idSᴹ ]tᴹ tᴹ
        ≡ [ π₁ᴹ idSᴹ ]tmᴹ tᴹ
      [π₁ᴹπ₁ᴹ]tᴹ
        : [ π₁ᴹ (π₁ᴹ σᴹ) ]tᴹ tᴹ ≡ [ π₁ᴹ (π₁ᴹ σᴹ) ]tmᴹ tᴹ

      -- 
      _⨟ᴹidSᴹ
        : (σᴹ : Subᴹ Γᴹ Δᴹ σ)
        → tr SubᴹFam (σ ⨟idS) (σᴹ ⨟ᴹ idSᴹ) ≡ σᴹ
      idSᴹ⨟ᴹ_
        : (σᴹ : Subᴹ Γᴹ Δᴹ σ)
        → tr SubᴹFam (idS⨟ σ) (idSᴹ ⨟ᴹ σᴹ) ≡ σᴹ
      ⨟ᴹ-assoc
        : tr SubᴹFam ⨟-assoc (σᴹ ⨟ᴹ (τᴹ ⨟ᴹ γᴹ))
        ≡ (σᴹ ⨟ᴹ τᴹ) ⨟ᴹ γᴹ
      π₁ᴹ,ˢᴹ
        : tr (Subᴹ Γᴹ Δᴹ) π₁, (π₁ᴹ (σᴹ ,ˢᴹ tᴹ)) ≡ σᴹ
      ⨟ᴹ,ˢᴹ -- the transport equation seems too long
        : tr SubᴹFam ⨟, (σᴹ ⨟ᴹ (τᴹ ,ˢᴹ tᴹ))
        ≡ (σᴹ ⨟ᴹ τᴹ) ,ˢᴹ tr TmᴹFamₜ (sym $ [⨟ᴹ]ᴹ) ([ σᴹ ]tᴹ tᴹ)
      η∅ˢᴹ
        : tr SubᴹFam η∅ σᴹ ≡ ∅ˢᴹ
      η,ˢᴹ
        : tr SubᴹFam η, σᴹ ≡ π₁ᴹ σᴹ ,ˢᴹ π₂ᴹ σᴹ
      [idSᴹ]tmᴹ
        : tr₂ (Tmᴹ Γᴹ) [idSᴹ] [idS]tm ([ idSᴹ ]tmᴹ tᴹ)
        ≡ tᴹ
      [⨟ᴹ]tmᴹ
        : tr₂ (Tmᴹ Γᴹ) [⨟ᴹ]ᴹ [⨟]tm ([ σᴹ ⨟ᴹ τᴹ ]tmᴹ tᴹ)
        ≡ [ σᴹ ]tmᴹ ([ τᴹ ]tmᴹ tᴹ)
      π₂ᴹ,ˢᴹ
        : tr₂ (Tmᴹ Γᴹ) [π₁ᴹ,ˢᴹ]ᴹ π₂, (π₂ᴹ (σᴹ ,ˢᴹ tᴹ))
        ≡ tᴹ

  record Univ (C : CwF) : Set (ℓ ⊔ ℓ′) where
    open CwF C

    field
      Uᴹ
        : (i : ℕ)
        → Tyᴹ Γᴹ (suc i) (U i)
      Elᴹ
        : Tmᴹ Γᴹ (Uᴹ i) t
        → Tyᴹ Γᴹ i (El t)
      Liftᴹ
        : Tyᴹ Γᴹ i A
        → Tyᴹ Γᴹ (suc i) (Lift A)
      cᴹ
        : Tyᴹ Γᴹ i A
        → Tmᴹ Γᴹ (Uᴹ i) (c A)
      mkᴹ
        : Tmᴹ Γᴹ Aᴹ t
        → Tmᴹ Γᴹ (Liftᴹ Aᴹ) (mk t)
      unᴹ
        : Tmᴹ Γᴹ (Liftᴹ Aᴹ) t
        → Tmᴹ Γᴹ Aᴹ (un t)
      []ᴹUᴹ
        : [ σᴹ ]ᴹ (Uᴹ i) ≡ Uᴹ i
      []ᴹElᴹ
        : (σᴹ : Subᴹ Γᴹ Δᴹ σ)(uᴹ : Tmᴹ Δᴹ (Uᴹ i) u)
        → ([ σᴹ ]ᴹ (Elᴹ uᴹ)) ≡ Elᴹ (tr TmᴹFamₜ []ᴹUᴹ ([ σᴹ ]tᴹ uᴹ))
      []ᴹLiftᴹ
        : [ σᴹ ]ᴹ (Liftᴹ Aᴹ) ≡ Liftᴹ ([ σᴹ ]ᴹ Aᴹ)
      []tᴹcᴹ
        : (σᴹ : Subᴹ Γᴹ Δᴹ σ)(Aᴹ : Tyᴹ Δᴹ i A)
        → tr₂ (Tmᴹ Γᴹ) []ᴹUᴹ ([]tc σ A) ([ σᴹ ]tᴹ (cᴹ Aᴹ))
        ≡ cᴹ ([ σᴹ ]ᴹ Aᴹ)
      []mkᴹ
        : (σ : Sub Γ Δ) (σᴹ : Subᴹ Γᴹ Δᴹ σ)
        → tr₂ (Tmᴹ Γᴹ) []ᴹLiftᴹ ([]mk σ _) ([ σᴹ ]tᴹ mkᴹ tᴹ)
        ≡ mkᴹ ([ σᴹ ]tᴹ tᴹ)
      []unᴹ
        : (σ : Sub Γ Δ) (σᴹ : Subᴹ Γᴹ Δᴹ σ)
        → tr TmᴹFam ([]un σ A t) ([ σᴹ ]tᴹ unᴹ tᴹ)
        ≡ unᴹ (tr TmᴹFamₜ []ᴹLiftᴹ ([ σᴹ ]tᴹ tᴹ))
      Uᴹβ
        : tr TyᴹFam Uβ (Elᴹ (cᴹ Aᴹ)) ≡ Aᴹ
      Uᴹη
        : tr TmᴹFam Uη (cᴹ (Elᴹ uᴹ)) ≡ uᴹ
      Liftᴹβ
        : tr TmᴹFam Liftβ (unᴹ (mkᴹ tᴹ)) ≡ tᴹ
      Liftᴹη
        : tr TmᴹFam Liftη (mkᴹ (unᴹ tᴹ)) ≡ tᴹ

  record Π-type (C : CwF) : Set (ℓ ⊔ ℓ′) where
    open CwF C
    field 
      Πᴹ
        : (Aᴹ : Tyᴹ Γᴹ i A)(Bᴹ : Tyᴹ (Γᴹ ,ᶜᴹ Aᴹ) i B)
        → Tyᴹ Γᴹ i (Π A B)
      ƛᴹ_
        : Tmᴹ (Γᴹ ,ᶜᴹ Aᴹ) Bᴹ t
        → Tmᴹ Γᴹ (Πᴹ Aᴹ Bᴹ) (ƛ t)
      appᴹ
        : Tmᴹ Γᴹ (Πᴹ Aᴹ Bᴹ) t
        → Tmᴹ (Γᴹ ,ᶜᴹ Aᴹ) Bᴹ (app t)
      []ᴹΠᴹ
        : [ σᴹ ]ᴹ (Πᴹ Aᴹ Bᴹ) ≡ Πᴹ ([ σᴹ ]ᴹ Aᴹ) ([ σᴹ ↑ᴹ Aᴹ ]ᴹ Bᴹ)
      []ƛᴹ
        : (σ : Sub Γ Δ) (σᴹ : Subᴹ Γᴹ Δᴹ σ)
        → tr₂ (Tmᴹ Γᴹ) []ᴹΠᴹ ([]ƛ σ _) ([ σᴹ ]tᴹ (ƛᴹ tᴹ))
        ≡ ƛᴹ ([ σᴹ ↑ᴹ Aᴹ ]tᴹ tᴹ)

  record Id-type (C : CwF) (U : Univ C) : Set (ℓ ⊔ ℓ′) where
    open CwF C
    open Univ U
    field
      Idᴹ
        : (aᴹ : Tmᴹ Γᴹ (Uᴹ i) a)(tᴹ : Tmᴹ Γᴹ (Elᴹ aᴹ) t)(uᴹ : Tmᴹ Γᴹ (Elᴹ aᴹ) u)
        → Tyᴹ Γᴹ i (Id a t u)
      []ᴹIdᴹ
        : [ σᴹ ]ᴹ (Idᴹ aᴹ tᴹ uᴹ)
        ≡ Idᴹ (tr TmᴹFamₜ []ᴹUᴹ ([ σᴹ ]tᴹ aᴹ))
            (tr TmᴹFamₜ ([]ᴹElᴹ σᴹ aᴹ) ([ σᴹ ]tᴹ tᴹ))
            (tr TmᴹFamₜ ([]ᴹElᴹ σᴹ aᴹ) ([ σᴹ ]tᴹ uᴹ))
      reflectᴹ
        : (Pp : Tmᴹ Γᴹ (Idᴹ aᴹ tᴹ uᴹ) p)
        → tr TmᴹFam (reflect p) tᴹ ≡ uᴹ

  record Method : Set (ℓ ⊔ ℓ′) where
    field
      𝒞    : CwF
      univ : Univ 𝒞
      piTy : Π-type 𝒞
      idTy : Id-type 𝒞 univ

    open CwF 𝒞        public
    open Univ univ    public
    open Π-type piTy  public
    open Id-type idTy public
