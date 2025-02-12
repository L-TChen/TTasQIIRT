-- Methods of SC+U+Pi+Id Recursor
module SC+U+Pi+Id.Recursion.Recursor.Method where

open import Prelude
open import SC+U+Pi+Id.Recursion.Recursor.Motive

module _ {ℓ ℓ′}(Mot : Motive ℓ ℓ′) where
  open Motive Mot
  private variable
    i j k : ℕ
    Γᴹ Δᴹ Θᴹ Φᴹ : Ctxᴹ
    σᴹ τᴹ γᴹ : Subᴹ Γᴹ Δᴹ
    Aᴹ Bᴹ Cᴹ : Tyᴹ Γᴹ i
    aᴹ tᴹ uᴹ : Tmᴹ Γᴹ Aᴹ

  record CwF₁ : Set (ℓ ⊔ ℓ′) where
    field
      [_]ᴹ_
        : (σᴹ : Subᴹ Γᴹ Δᴹ)(Aᴹ : Tyᴹ Δᴹ i)
        → Tyᴹ Γᴹ i
      ∅ᶜᴹ
        : Ctxᴹ
      _,ᶜᴹ_
        : (Γᴹ : Ctxᴹ)(Aᴹ : Tyᴹ Γᴹ i)
        → Ctxᴹ
      ∅ˢᴹ
        : Subᴹ Δᴹ ∅ᶜᴹ
      _,ˢᴹ_
        : (σᴹ : Subᴹ Γᴹ Δᴹ){Aᴹ : Tyᴹ Δᴹ i}(tᴹ : Tmᴹ Γᴹ ([ σᴹ ]ᴹ Aᴹ))
        → Subᴹ Γᴹ (Δᴹ ,ᶜᴹ Aᴹ)
      idSᴹ
        : Subᴹ Γᴹ Γᴹ
      _⨟ᴹ_
        : (τᴹ : Subᴹ Γᴹ Δᴹ)(σᴹ : Subᴹ Δᴹ Θᴹ)
        → Subᴹ Γᴹ Θᴹ
      π₁ᴹ
        : (σᴹ : Subᴹ Γᴹ (Δᴹ ,ᶜᴹ Aᴹ))
        → Subᴹ Γᴹ Δᴹ
      [idSᴹ]
        : {Aᴹ : Tyᴹ Γᴹ i}
        → [ idSᴹ ]ᴹ Aᴹ ≡ Aᴹ
      [⨟ᴹ]ᴹ
        : {σᴹ : Subᴹ Γᴹ Δᴹ}{τᴹ : Subᴹ Δᴹ Θᴹ}{Aᴹ : Tyᴹ Θᴹ i}
        → [ σᴹ ⨟ᴹ τᴹ ]ᴹ Aᴹ ≡ [ σᴹ ]ᴹ ([ τᴹ ]ᴹ Aᴹ)
      π₂ᴹ
        : (σᴹ : Subᴹ Δᴹ (Γᴹ ,ᶜᴹ Aᴹ))
        ---------------------------------
        → Tmᴹ Δᴹ ([ π₁ᴹ σᴹ ]ᴹ Aᴹ)
      [_]tmᴹ_
        : (σᴹ : Subᴹ Γᴹ Δᴹ){Aᴹ : Tyᴹ Δᴹ i}
        → (tᴹ : Tmᴹ Δᴹ Aᴹ)
        → Tmᴹ Γᴹ ([ σᴹ ]ᴹ Aᴹ)
    
    _↑ᴹ_
      : (σᴹ : Subᴹ Γᴹ Δᴹ)(Aᴹ : Tyᴹ Δᴹ i)
      → Subᴹ (Γᴹ ,ᶜᴹ ([ σᴹ ]ᴹ Aᴹ)) (Δᴹ ,ᶜᴹ Aᴹ)
    _↑ᴹ_ {Γᴹ} {Δᴹ} σᴹ Aᴹ
      = (π₁ᴹ idSᴹ ⨟ᴹ σᴹ) ,ˢᴹ tr TmᴹFam (sym [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ)
    
    Subᴹ,ᶜᴹFam
      : {i : ℕ}{Γᴹ Δᴹ : Ctxᴹ} → Tyᴹ Γᴹ i → Set ℓ′
    Subᴹ,ᶜᴹFam {_} {Γᴹ} {Δᴹ} Aᴹ = Subᴹ (Γᴹ ,ᶜᴹ Aᴹ) Δᴹ

  record CwF₂ (C₁ : CwF₁) : Set (ℓ ⊔ ℓ′) where
    open CwF₁ C₁
    field
      _⨟ᴹidSᴹ
        : (σᴹ : Subᴹ Γᴹ Δᴹ)
        → σᴹ ⨟ᴹ idSᴹ ≡ σᴹ
      idSᴹ⨟ᴹ_
        : (σᴹ : Subᴹ Γᴹ Δᴹ)
        → idSᴹ ⨟ᴹ σᴹ ≡ σᴹ
      ⨟ᴹ-assoc
        : σᴹ ⨟ᴹ (τᴹ ⨟ᴹ γᴹ) ≡ (σᴹ ⨟ᴹ τᴹ) ⨟ᴹ γᴹ
      π₁ᴹ,ˢᴹ
        : π₁ᴹ (σᴹ ,ˢᴹ tᴹ) ≡ σᴹ
      ⨟ᴹ,ˢᴹ -- the transport equation seems too long
        : {Γᴹ Δᴹ Θᴹ : Ctxᴹ}{Aᴹ : Tyᴹ Θᴹ i}
          {σᴹ : Subᴹ Γᴹ Δᴹ}{τᴹ : Subᴹ Δᴹ Θᴹ}{tᴹ : Tmᴹ Δᴹ ([ τᴹ ]ᴹ Aᴹ)}
        → σᴹ ⨟ᴹ (τᴹ ,ˢᴹ tᴹ) ≡ (σᴹ ⨟ᴹ τᴹ) ,ˢᴹ tr TmᴹFam (sym [⨟ᴹ]ᴹ) ([ σᴹ ]tmᴹ tᴹ)
      η∅ˢᴹ
        : σᴹ ≡ ∅ˢᴹ
      η,ˢᴹ
        : σᴹ ≡ π₁ᴹ σᴹ ,ˢᴹ π₂ᴹ σᴹ
      [idSᴹ]tmᴹ
        : tr TmᴹFam [idSᴹ] ([ idSᴹ ]tmᴹ tᴹ) ≡ tᴹ
      [⨟ᴹ]tmᴹ
        : tr TmᴹFam [⨟ᴹ]ᴹ ([ σᴹ ⨟ᴹ τᴹ ]tmᴹ tᴹ) ≡ [ σᴹ ]tmᴹ ([ τᴹ ]tmᴹ tᴹ)
      π₂ᴹ,ˢᴹ
        : {Aᴹ : Tyᴹ Δᴹ i}{σᴹ : Subᴹ Γᴹ Δᴹ}{tᴹ : Tmᴹ Γᴹ ([ σᴹ ]ᴹ Aᴹ)}
        → tr (λ τᴹ → TmᴹFam ([ τᴹ ]ᴹ Aᴹ)) π₁ᴹ,ˢᴹ (π₂ᴹ (σᴹ ,ˢᴹ tᴹ)) ≡ tᴹ
  
  record CwF : Set (ℓ ⊔ ℓ′) where
    field
      C₁ : CwF₁
      C₂ : CwF₂ C₁
    open CwF₁ C₁ public
    open CwF₂ C₂ public

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
        → [ σᴹ ]ᴹ (Elᴹ uᴹ)
        ≡ Elᴹ (tr TmᴹFam []ᴹUᴹ ([ σᴹ ]tmᴹ uᴹ))
      []ᴹLiftᴹ
        : [ σᴹ ]ᴹ (Liftᴹ Aᴹ) ≡ Liftᴹ ([ σᴹ ]ᴹ Aᴹ)
      []tᴹcᴹ
        : (σᴹ : Subᴹ Γᴹ Δᴹ)(Aᴹ : Tyᴹ Δᴹ i)
        → tr TmᴹFam []ᴹUᴹ ([ σᴹ ]tmᴹ (cᴹ Aᴹ)) ≡ cᴹ ([ σᴹ ]ᴹ Aᴹ)
      []mkᴹ
        : (σᴹ : Subᴹ Γᴹ Δᴹ)(tᴹ : Tmᴹ Δᴹ Aᴹ)
        → tr TmᴹFam []ᴹLiftᴹ ([ σᴹ ]tmᴹ mkᴹ tᴹ) ≡ mkᴹ ([ σᴹ ]tmᴹ tᴹ)
      []unᴹ
        : (σᴹ : Subᴹ Γᴹ Δᴹ)(Aᴹ : Tyᴹ Δᴹ i)(tᴹ : Tmᴹ Δᴹ (Liftᴹ Aᴹ))
        → [ σᴹ ]tmᴹ unᴹ tᴹ ≡ unᴹ (tr TmᴹFam []ᴹLiftᴹ ([ σᴹ ]tmᴹ tᴹ))
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
        : [ σᴹ ]ᴹ Πᴹ Aᴹ Bᴹ ≡ Πᴹ ([ σᴹ ]ᴹ Aᴹ) ([ σᴹ ↑ᴹ Aᴹ ]ᴹ Bᴹ)
      []ƛᴹ
        : (σᴹ : Subᴹ Γᴹ Δᴹ)(tᴹ : Tmᴹ (Δᴹ ,ᶜᴹ Aᴹ) Bᴹ)
        → tr TmᴹFam []ᴹΠᴹ ([ σᴹ ]tmᴹ ƛᴹ tᴹ)
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
        : {σᴹ : Subᴹ Γᴹ Δᴹ}{aᴹ : Tmᴹ Δᴹ (Uᴹ i)}{tᴹ : Tmᴹ Δᴹ (Elᴹ aᴹ)}{uᴹ : Tmᴹ Δᴹ (Elᴹ aᴹ)}
        → [ σᴹ ]ᴹ (Idᴹ aᴹ tᴹ uᴹ)
        ≡ Idᴹ (tr TmᴹFam []ᴹUᴹ ([ σᴹ ]tmᴹ aᴹ))
              (tr TmᴹFam ([]ᴹElᴹ σᴹ aᴹ) ([ σᴹ ]tmᴹ tᴹ))
              (tr TmᴹFam ([]ᴹElᴹ σᴹ aᴹ) ([ σᴹ ]tmᴹ uᴹ))
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
