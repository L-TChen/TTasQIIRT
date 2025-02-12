module SC+U+Pi+Id.QIIRT.Recursion.Method where

open import Prelude
  hiding (_,_)
open import Data.Nat hiding (_⊔_)
open import SC+U+Pi+Id.QIIRT.Syntax
open import SC+U+Pi+Id.QIIRT.Properties
open import SC+U+Pi+Id.QIIRT.Recursion.Motive

module _ {ℓ ℓ′}(Mot : Motive {ℓ} {ℓ′}) where
  open Motive Mot
  private variable
    Γᴹ Δᴹ Θᴹ : Ctxᴹ
    σᴹ τᴹ γᴹ : Subᴹ Δᴹ Γᴹ
    Aᴹ Bᴹ Cᴹ : Tyᴹ Γᴹ i
    aᴹ tᴹ uᴹ : Tmᴹ Γᴹ Aᴹ
    p : Tm Γ (Id a t u)

  record CwF : Set (ℓ ⊔ ℓ′) where
    field
      [_]ᴹ_
        : (σᴹ : Subᴹ Δᴹ Γᴹ)(Aᴹ : Tyᴹ Γᴹ i)
        → Tyᴹ Δᴹ i
      ∅ᶜᴹ
        : Ctxᴹ
      _,ᶜᴹ_
        : (Γᴹ : Ctxᴹ)(Aᴹ : Tyᴹ Γᴹ i)
        → Ctxᴹ
      ∅ˢᴹ
        : Subᴹ Δᴹ ∅ᶜᴹ
      _,ˢᴹ_
        : (σᴹ : Subᴹ Γᴹ Δᴹ)(tᴹ : Tmᴹ Γᴹ ([ σᴹ ]ᴹ Aᴹ))
        → Subᴹ Γᴹ (Δᴹ ,ᶜᴹ Aᴹ)
      idSᴹ
        : Subᴹ Δᴹ Δᴹ
      _⨟ᴹ_
        : (τᴹ : Subᴹ Γᴹ Δᴹ)(σᴹ : Subᴹ Δᴹ Θᴹ)
        → Subᴹ Γᴹ Θᴹ
      π₁ᴹ
        : (σᴹ : Subᴹ Δᴹ (Γᴹ ,ᶜᴹ Aᴹ))
        → Subᴹ Δᴹ Γᴹ
      [idSᴹ]
        : [ idSᴹ ]ᴹ Aᴹ ≡ Aᴹ
      [⨟ᴹ]ᴹ
        : [ τᴹ ⨟ᴹ σᴹ ]ᴹ Aᴹ ≡ [ τᴹ ]ᴹ ([ σᴹ ]ᴹ Aᴹ)
      [π₁ᴹ,ˢᴹ]ᴹ
        : ([ π₁ᴹ (σᴹ ,ˢᴹ tᴹ) ]ᴹ Aᴹ) ≡ [ σᴹ ]ᴹ Aᴹ
      [π₁ᴹ⨟ᴹ]ᴹ
        : [ π₁ᴹ (σᴹ ⨟ᴹ τᴹ) ]ᴹ Aᴹ ≡ [ σᴹ ]ᴹ ([ π₁ᴹ τᴹ ]ᴹ Aᴹ)
      π₂ᴹ
        : (σᴹ : Subᴹ Δᴹ (Γᴹ ,ᶜᴹ Aᴹ))
        ---------------------------------
        → Tmᴹ Δᴹ ([ π₁ᴹ σᴹ ]ᴹ Aᴹ)
      [_]tmᴹ_
        : (σᴹ : Subᴹ Γᴹ Δᴹ) {Aᴹ : Tyᴹ Δᴹ i}
        → (tᴹ : Tmᴹ Δᴹ Aᴹ)
        → Tmᴹ Γᴹ ([ σᴹ ]ᴹ Aᴹ)
    
    _⁺ᴹ
      : (σᴹ : Subᴹ Γᴹ Δᴹ)
      → Subᴹ (Γᴹ ,ᶜᴹ ([ σᴹ ]ᴹ Aᴹ)) (Δᴹ ,ᶜᴹ Aᴹ)
    σᴹ ⁺ᴹ = (π₁ᴹ idSᴹ ⨟ᴹ σᴹ) ,ˢᴹ tr (Tmᴹ _) (sym $ [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ)
    
    Subᴹ,ᶜᴹFam
      : {Γᴹ Δᴹ : Ctxᴹ} → Tyᴹ Γᴹ i → Set ℓ′
    Subᴹ,ᶜᴹFam {_} {Γᴹ} {Δᴹ} Aᴹ = Subᴹ (Γᴹ ,ᶜᴹ Aᴹ) Δᴹ

    field
      _↑ᴹ_
        : (σᴹ : Subᴹ Γᴹ Δᴹ)(Aᴹ : Tyᴹ Δᴹ i)
        → Subᴹ (Γᴹ ,ᶜᴹ ([ σᴹ ]ᴹ Aᴹ)) (Δᴹ ,ᶜᴹ Aᴹ)
      idSᴹ↑ᴹ
        : tr Subᴹ,ᶜᴹFam [idSᴹ] (idSᴹ ↑ᴹ Aᴹ) ≡ idSᴹ
      ⨟ᴹ↑ᴹ
        : tr Subᴹ,ᶜᴹFam [⨟ᴹ]ᴹ ((σᴹ ⨟ᴹ τᴹ) ↑ᴹ Aᴹ)
        ≡ (σᴹ ↑ᴹ ([ τᴹ ]ᴹ Aᴹ)) ⨟ᴹ (τᴹ ↑ᴹ Aᴹ)
      π₁ᴹ,ˢᴹ↑ᴹ
        : tr Subᴹ,ᶜᴹFam [π₁ᴹ,ˢᴹ]ᴹ (π₁ᴹ (σᴹ ,ˢᴹ tᴹ) ↑ᴹ Aᴹ) ≡ σᴹ ↑ᴹ Aᴹ
      π₁ᴹ⨟ᴹ↑ᴹ
        : tr Subᴹ,ᶜᴹFam [π₁ᴹ⨟ᴹ]ᴹ (π₁ᴹ (σᴹ ⨟ᴹ τᴹ) ↑ᴹ Aᴹ) ≡ (σᴹ ↑ᴹ ([ π₁ᴹ τᴹ ]ᴹ Aᴹ)) ⨟ᴹ (π₁ᴹ τᴹ ↑ᴹ Aᴹ)
      ∅ˢᴹ↑ᴹ
        : ∅ˢᴹ {Δᴹ = Δᴹ} ↑ᴹ Aᴹ ≡ ∅ˢᴹ ⁺ᴹ
      ,ˢᴹ↑ᴹ
        : (σᴹ ,ˢᴹ tᴹ) ↑ᴹ Aᴹ ≡ (σᴹ ,ˢᴹ tᴹ) ⁺ᴹ
      π₁ᴹidSᴹ↑ᴹ
        : π₁ᴹ {Aᴹ = Bᴹ} idSᴹ ↑ᴹ Aᴹ ≡ π₁ᴹ idSᴹ ⁺ᴹ
      π₁ᴹπ₁ᴹ↑ᴹ
        : π₁ᴹ (π₁ᴹ σᴹ) ↑ᴹ Aᴹ ≡ π₁ᴹ (π₁ᴹ σᴹ) ⁺ᴹ

      [_]tᴹ_
        : (σᴹ : Subᴹ Δᴹ Γᴹ)(tᴹ : Tmᴹ Γᴹ Aᴹ)
        → Tmᴹ Δᴹ ([ σᴹ ]ᴹ Aᴹ)
      [idSᴹ]tᴹ
        :  tr TmᴹFamₜ [idSᴹ] ([ idSᴹ ]tᴹ tᴹ)  ≡ tᴹ
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
        : [ ∅ˢᴹ {Δᴹ} ]tᴹ tᴹ ≡ [ ∅ˢᴹ ]tmᴹ tᴹ
      [,ˢᴹ]tᴹ
        : [ σᴹ ,ˢᴹ tᴹ ]tᴹ uᴹ ≡ [ σᴹ ,ˢᴹ tᴹ ]tmᴹ uᴹ
      [π₁ᴹidSᴹ]tᴹ
        : [ π₁ᴹ {Δᴹ = Γᴹ ,ᶜᴹ Aᴹ} idSᴹ ]tᴹ tᴹ ≡ [ π₁ᴹ idSᴹ ]tmᴹ tᴹ
      [π₁ᴹπ₁ᴹ]tᴹ
        : [ π₁ᴹ (π₁ᴹ σᴹ) ]tᴹ tᴹ ≡ [ π₁ᴹ (π₁ᴹ σᴹ) ]tmᴹ tᴹ

      -- 
      _⨟ᴹidSᴹ
        : (σᴹ : Subᴹ Δᴹ Γᴹ)
        → σᴹ ⨟ᴹ idSᴹ ≡ σᴹ
      idSᴹ⨟ᴹ_
        : (σᴹ : Subᴹ Δᴹ Γᴹ)
        → idSᴹ ⨟ᴹ σᴹ ≡ σᴹ
      ⨟ᴹ-assoc
        : σᴹ ⨟ᴹ (τᴹ ⨟ᴹ γᴹ)
        ≡ (σᴹ ⨟ᴹ τᴹ) ⨟ᴹ γᴹ
      π₁ᴹ,ˢᴹ
        : π₁ᴹ (σᴹ ,ˢᴹ tᴹ) ≡ σᴹ
      ⨟ᴹ,ˢᴹ
        : σᴹ ⨟ᴹ (τᴹ ,ˢᴹ tᴹ)
        ≡ (σᴹ ⨟ᴹ τᴹ) ,ˢᴹ tr TmᴹFamₜ (sym $ [⨟ᴹ]ᴹ) ([ σᴹ ]tmᴹ tᴹ)
      η∅ˢᴹ
        : σᴹ ≡ ∅ˢᴹ
      η,ˢᴹ
        : σᴹ ≡ π₁ᴹ σᴹ ,ˢᴹ π₂ᴹ σᴹ
      [idSᴹ]tmᴹ
        : tr (Tmᴹ Γᴹ) [idSᴹ] ([ idSᴹ ]tmᴹ tᴹ)
        ≡ tᴹ
      [⨟ᴹ]tmᴹ
        : tr (Tmᴹ Γᴹ) [⨟ᴹ]ᴹ ([ σᴹ ⨟ᴹ τᴹ ]tmᴹ tᴹ)
        ≡ [ σᴹ ]tmᴹ ([ τᴹ ]tmᴹ tᴹ)
      π₂ᴹ,ˢᴹ
        : tr (Tmᴹ Γᴹ) [π₁ᴹ,ˢᴹ]ᴹ (π₂ᴹ (σᴹ ,ˢᴹ tᴹ))
        ≡ tᴹ

  record Univ (C : CwF) : Set (ℓ ⊔ ℓ′) where
    open CwF C

    field
      Uᴹ
        : (i : ℕ)
        → Tyᴹ Γᴹ (suc i) 
      Elᴹ
        : Tmᴹ Γᴹ (Uᴹ i)
        → Tyᴹ Γᴹ i
      Liftᴹ
        : Tyᴹ Γᴹ i
        → Tyᴹ Γᴹ (suc i)
      cᴹ
        : Tyᴹ Γᴹ i
        → Tmᴹ Γᴹ (Uᴹ i)
      mkᴹ
        : Tmᴹ Γᴹ Aᴹ
        → Tmᴹ Γᴹ (Liftᴹ Aᴹ)
      unᴹ
        : Tmᴹ Γᴹ (Liftᴹ Aᴹ)
        → Tmᴹ Γᴹ Aᴹ
      []ᴹUᴹ
        : [ σᴹ ]ᴹ (Uᴹ i) ≡ Uᴹ i
      []ᴹElᴹ
        : (σᴹ : Subᴹ Γᴹ Δᴹ)(uᴹ : Tmᴹ Δᴹ (Uᴹ i))
        → ([ σᴹ ]ᴹ (Elᴹ uᴹ)) ≡  Elᴹ (tr TmᴹFamₜ []ᴹUᴹ ([ σᴹ ]tᴹ uᴹ)) 
      []ᴹLiftᴹ
        : [ σᴹ ]ᴹ (Liftᴹ Aᴹ) ≡ Liftᴹ ([ σᴹ ]ᴹ Aᴹ)
      []tᴹcᴹ
        : (σᴹ : Subᴹ Γᴹ Δᴹ)(Aᴹ : Tyᴹ Δᴹ i)
        → tr (Tmᴹ Γᴹ) []ᴹUᴹ ([ σᴹ ]tmᴹ (cᴹ Aᴹ))
        ≡ cᴹ ([ σᴹ ]ᴹ Aᴹ)
      []mkᴹ
        : (σᴹ : Subᴹ Γᴹ Δᴹ)
        → tr (Tmᴹ Γᴹ) []ᴹLiftᴹ ([ σᴹ ]tmᴹ mkᴹ tᴹ)
        ≡ mkᴹ ([ σᴹ ]tᴹ tᴹ)
      []unᴹ
        : (σᴹ : Subᴹ Γᴹ Δᴹ)
        → [ σᴹ ]tmᴹ unᴹ tᴹ
        ≡ unᴹ (tr TmᴹFamₜ []ᴹLiftᴹ ([ σᴹ ]tmᴹ tᴹ))
      Uᴹβ
        : Elᴹ (cᴹ Aᴹ) ≡ Aᴹ
      Uᴹη
        : cᴹ (Elᴹ uᴹ) ≡ uᴹ
      Liftᴹβ
        : unᴹ (mkᴹ tᴹ) ≡ tᴹ
      Liftᴹη
        : mkᴹ (unᴹ tᴹ) ≡ tᴹ

  record Π-type (C : CwF) : Set (ℓ ⊔ ℓ′) where
    open CwF C
    field 
      Πᴹ
        : (Aᴹ : Tyᴹ Γᴹ i)(Bᴹ : Tyᴹ (Γᴹ ,ᶜᴹ Aᴹ) i)
        → Tyᴹ Γᴹ i
      ƛᴹ_
        : Tmᴹ (Γᴹ ,ᶜᴹ Aᴹ) Bᴹ
        → Tmᴹ Γᴹ (Πᴹ Aᴹ Bᴹ)
      appᴹ
        : Tmᴹ Γᴹ (Πᴹ Aᴹ Bᴹ)
        → Tmᴹ (Γᴹ ,ᶜᴹ Aᴹ) Bᴹ
      []ᴹΠᴹ
        : [ σᴹ ]ᴹ (Πᴹ Aᴹ Bᴹ) ≡ Πᴹ ([ σᴹ ]ᴹ Aᴹ) ([ σᴹ ↑ᴹ Aᴹ ]ᴹ Bᴹ)
      []ƛᴹ
        : (σ : Sub Γ Δ) (σᴹ : Subᴹ Γᴹ Δᴹ)
        → tr (Tmᴹ Γᴹ) []ᴹΠᴹ ([ σᴹ ]tmᴹ (ƛᴹ tᴹ))
        ≡ ƛᴹ ([ σᴹ ↑ᴹ Aᴹ ]tmᴹ tᴹ)
      Πβᴹ
        : appᴹ (ƛᴹ tᴹ) ≡ tᴹ
      Πηᴹ
        : ƛᴹ (appᴹ tᴹ) ≡ tᴹ

  record Id-type (C : CwF) (U : Univ C) : Set (ℓ ⊔ ℓ′) where
    open CwF C
    open Univ U
    field
      Idᴹ
        : (aᴹ : Tmᴹ Γᴹ (Uᴹ i))(tᴹ : Tmᴹ Γᴹ (Elᴹ aᴹ))(uᴹ : Tmᴹ Γᴹ (Elᴹ aᴹ))
        → Tyᴹ Γᴹ i
      []ᴹIdᴹ
        : [ σᴹ ]ᴹ (Idᴹ aᴹ tᴹ uᴹ)
        ≡ Idᴹ (tr TmᴹFamₜ []ᴹUᴹ ([ σᴹ ]tᴹ aᴹ))
            (tr TmᴹFamₜ ([]ᴹElᴹ σᴹ aᴹ) ([ σᴹ ]tᴹ tᴹ))
            (tr TmᴹFamₜ ([]ᴹElᴹ σᴹ aᴹ) ([ σᴹ ]tᴹ uᴹ))
      reflᴹ
        : (tᴹ : Tmᴹ Γᴹ (Elᴹ aᴹ))
        → Tmᴹ Γᴹ (Idᴹ aᴹ tᴹ tᴹ)
      []reflᴹ
          : tr (Tmᴹ Δᴹ) []ᴹIdᴹ ([ σᴹ ]tmᴹ (reflᴹ tᴹ))
          ≡ reflᴹ (tr TmᴹFamₜ ([]ᴹElᴹ σᴹ aᴹ) ([ σᴹ ]tᴹ tᴹ))
      reflectᴹ
        : (Pp : Tmᴹ Γᴹ (Idᴹ aᴹ tᴹ uᴹ))
        → tᴹ ≡ uᴹ

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
