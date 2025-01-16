-- Methods of SC+U+Pi+Id/QIIT
open import Prelude

module SC+U+Pi+Id.QIIT.Elimination.Method where

open import SC+U+Pi+Id.QIIT.Syntax
open import SC+U+Pi+Id.QIIT.Properties
open import SC+U+Pi+Id.QIIT.Elimination.Motive

module _ {ℓ ℓ′}(Mot : Motive ℓ ℓ′) where
  open Motive Mot
  private variable
    Γᴹ Δᴹ Θᴹ Φᴹ : Ctxᴹ Γ
    σᴹ τᴹ γᴹ : Subᴹ Γᴹ Δᴹ σ
    Aᴹ Bᴹ Cᴹ : Tyᴹ Γᴹ i A
    aᴹ tᴹ uᴹ : Tmᴹ Γᴹ Aᴹ t
    p : Tm Γ (Id a t u)

  record CwF₁ : Set (ℓ ⊔ ℓ′) where
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
        : {Aᴹ : Tyᴹ Γᴹ i A}
        → tr TyᴹFam [idS] ([ idSᴹ ]ᴹ Aᴹ) ≡ Aᴹ
      [⨟ᴹ]ᴹ
        : {σᴹ : Subᴹ Γᴹ Δᴹ σ}{τᴹ : Subᴹ Δᴹ Θᴹ τ}{Aᴹ : Tyᴹ Θᴹ i A}
        → tr TyᴹFam [⨟] ([ σᴹ ⨟ᴹ τᴹ ]ᴹ Aᴹ) ≡ [ σᴹ ]ᴹ ([ τᴹ ]ᴹ Aᴹ)
      π₂ᴹ
        : (σᴹ : Subᴹ Δᴹ (Γᴹ ,ᶜᴹ Aᴹ) σ)
        ---------------------------------
        → Tmᴹ Δᴹ ([ π₁ᴹ σᴹ ]ᴹ Aᴹ) (π₂ σ)
      [_]tmᴹ_
        : (σᴹ : Subᴹ Γᴹ Δᴹ σ) {Aᴹ : Tyᴹ Δᴹ i A}
        → (tᴹ : Tmᴹ Δᴹ Aᴹ t)
        → Tmᴹ Γᴹ ([ σᴹ ]ᴹ Aᴹ) ([ σ ]tm t)
    
    _↑ᴹ_
      : (σᴹ : Subᴹ Γᴹ Δᴹ σ)(Aᴹ : Tyᴹ Δᴹ i A)
      → Subᴹ (Γᴹ ,ᶜᴹ ([ σᴹ ]ᴹ Aᴹ)) (Δᴹ ,ᶜᴹ Aᴹ) (σ ↑ A)
    _↑ᴹ_ {_} {Γᴹ} {_} {Δᴹ} σᴹ Aᴹ
      = (π₁ᴹ idSᴹ ⨟ᴹ σᴹ) ,ˢᴹ trTmᴹₜ (sym [⨟]) (flip-tr [⨟ᴹ]ᴹ) (π₂ᴹ {Δᴹ = Γᴹ ,ᶜᴹ ([ σᴹ ]ᴹ Aᴹ)} idSᴹ)

    Subᴹ,ᶜᴹFam
      : {Γᴹ : Ctxᴹ Γ} → {Ctxᴹ Δ} → {Sub (Γ , A) Δ} → Tyᴹ Γᴹ i A → Set ℓ′
    Subᴹ,ᶜᴹFam {_} {_} {_} {_} {Γᴹ} {Δᴹ} {σ} Aᴹ = Subᴹ (Γᴹ ,ᶜᴹ Aᴹ) Δᴹ σ

    trTmᴹₛ : {A : Ty Δ i}{Γᴹ : Ctxᴹ Γ}{Δᴹ : Ctxᴹ Δ}
            {σ σ' : Sub Γ Δ}(σ≡σ' : σ ≡ σ')
            {σᴹ : Subᴹ Γᴹ Δᴹ σ}{σ'ᴹ : Subᴹ Γᴹ Δᴹ σ'}
            (σᴹ≡σ'ᴹ : tr (Subᴹ Γᴹ Δᴹ) σ≡σ' σᴹ ≡ σ'ᴹ)
            {Aᴹ : Tyᴹ Δᴹ i A}{t : Tm Γ ([ σ ] A)}
          → Tmᴹ Γᴹ ([ σᴹ ]ᴹ Aᴹ) t → Tmᴹ Γᴹ ([ σ'ᴹ ]ᴹ Aᴹ) (tr TmFamₛ σ≡σ' t)
    trTmᴹₛ refl eq {Aᴹ} = tr TmᴹFamₜ (cong ([_]ᴹ Aᴹ) eq)

  record CwF₂ (C₁ : CwF₁) : Set (ℓ ⊔ ℓ′) where
    open CwF₁ C₁
    field
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
        : {Γᴹ : Ctxᴹ Γ}{Δᴹ : Ctxᴹ Δ}{Θᴹ : Ctxᴹ Θ}
          {Aᴹ : Tyᴹ Θᴹ i A}{σᴹ : Subᴹ Γᴹ Δᴹ σ}
          {τᴹ : Subᴹ Δᴹ Θᴹ τ}{tᴹ : Tmᴹ Δᴹ ([ τᴹ ]ᴹ Aᴹ) t}
        → tr SubᴹFam ⨟, (σᴹ ⨟ᴹ (τᴹ ,ˢᴹ tᴹ))
        ≡ (σᴹ ⨟ᴹ τᴹ) ,ˢᴹ trTmᴹₜ (sym [⨟]) (flip-tr [⨟ᴹ]ᴹ) ([ σᴹ ]tmᴹ tᴹ)
      η∅ˢᴹ
        : tr SubᴹFam η∅ σᴹ ≡ ∅ˢᴹ
      η,ˢᴹ
        : tr SubᴹFam η, σᴹ ≡ π₁ᴹ σᴹ ,ˢᴹ π₂ᴹ σᴹ
      [idSᴹ]tmᴹ
        : tr TmᴹFam [idS]tm (trTmᴹₜ [idS] [idSᴹ] ([ idSᴹ ]tmᴹ tᴹ))
        ≡ tᴹ
      [⨟ᴹ]tmᴹ
        : tr TmᴹFam [⨟]tm (trTmᴹₜ [⨟] [⨟ᴹ]ᴹ ([ σᴹ ⨟ᴹ τᴹ ]tmᴹ tᴹ))
        ≡ [ σᴹ ]tmᴹ ([ τᴹ ]tmᴹ tᴹ)
      π₂ᴹ,ˢᴹ
        : {Aᴹ : Tyᴹ Δᴹ i A}{σᴹ : Subᴹ Γᴹ Δᴹ σ}{tᴹ : Tmᴹ Γᴹ ([ σᴹ ]ᴹ Aᴹ) t}
        → tr TmᴹFam π₂, (trTmᴹₛ π₁, π₁ᴹ,ˢᴹ (π₂ᴹ (σᴹ ,ˢᴹ tᴹ)))
        ≡ tᴹ
  
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
        : tr TyᴹFam []U ([ σᴹ ]ᴹ (Uᴹ i)) ≡ Uᴹ i
      []ᴹElᴹ
        : (σᴹ : Subᴹ Γᴹ Δᴹ σ)(uᴹ : Tmᴹ Δᴹ (Uᴹ i) u)
        → tr TyᴹFam ([]El σ u) ([ σᴹ ]ᴹ (Elᴹ uᴹ))
        ≡ Elᴹ (trTmᴹₜ []U []ᴹUᴹ ([ σᴹ ]tmᴹ uᴹ))
      []ᴹLiftᴹ
        : tr TyᴹFam []Lift ([ σᴹ ]ᴹ (Liftᴹ Aᴹ))
        ≡ Liftᴹ ([ σᴹ ]ᴹ Aᴹ)
      []tᴹcᴹ
        : (σᴹ : Subᴹ Γᴹ Δᴹ σ)(Aᴹ : Tyᴹ Δᴹ i A)
        → tr TmᴹFam ([]tc σ A) (trTmᴹₜ []U []ᴹUᴹ ([ σᴹ ]tmᴹ (cᴹ Aᴹ)))
        ≡ cᴹ ([ σᴹ ]ᴹ Aᴹ)
      []mkᴹ
        : (σ : Sub Γ Δ) (σᴹ : Subᴹ Γᴹ Δᴹ σ)
        → tr TmᴹFam ([]mk _ _) (trTmᴹₜ []Lift []ᴹLiftᴹ ([ σᴹ ]tmᴹ mkᴹ tᴹ))
        ≡ mkᴹ ([ σᴹ ]tmᴹ tᴹ)
      []unᴹ
        : (σᴹ : Subᴹ Γᴹ Δᴹ σ){Aᴹ : Tyᴹ Δᴹ i A}(tᴹ : Tmᴹ Δᴹ (Liftᴹ Aᴹ) t)
        → tr TmᴹFam ([]un σ A t) ([ σᴹ ]tmᴹ unᴹ tᴹ)
        ≡ unᴹ (trTmᴹₜ []Lift []ᴹLiftᴹ ([ σᴹ ]tmᴹ tᴹ))
      Uᴹβ
        : tr TyᴹFam Uβ (Elᴹ (cᴹ Aᴹ)) ≡ Aᴹ
      Uᴹη
        : tr TmᴹFam Uη (cᴹ (Elᴹ uᴹ)) ≡ uᴹ
      Liftᴹβ
        : tr TmᴹFam Liftβ (unᴹ (mkᴹ tᴹ)) ≡ tᴹ
      Liftᴹη
        : tr TmᴹFam Liftη (mkᴹ (unᴹ tᴹ)) ≡ tᴹ
{-
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
-} 