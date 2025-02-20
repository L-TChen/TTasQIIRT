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
    σᴹ τᴹ γᴹ : Subᴹ Γᴹ Δᴹ
    Aᴹ Bᴹ Cᴹ : Tyᴹ Γᴹ i
    aᴹ tᴹ uᴹ : Tmᴹ Γᴹ Aᴹ
    p : Tm Γ (Id a t u)

  record CwF : Set (ℓ ⊔ ℓ′) where
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
        : Subᴹ Γᴹ ∅ᶜᴹ
      _,ˢᴹ_
        : (σᴹ : Subᴹ Γᴹ Δᴹ) {Aᴹ : Tyᴹ Δᴹ i} (tᴹ : Tmᴹ Γᴹ ([ σᴹ ]ᴹ Aᴹ))
        → Subᴹ Γᴹ (Δᴹ ,ᶜᴹ Aᴹ)
      idSᴹ
        : Subᴹ Γᴹ Γᴹ
      _⨟ᴹ_
        : (τᴹ : Subᴹ Γᴹ Δᴹ)(σᴹ : Subᴹ Δᴹ Θᴹ)
        → Subᴹ Γᴹ Θᴹ
      π₁ᴹ
        : (σᴹ : Subᴹ Γᴹ (Δᴹ ,ᶜᴹ Aᴹ))
        → Subᴹ Γᴹ Δᴹ
      [idS]ᴹ
        : [ idSᴹ ]ᴹ Aᴹ ≡ Aᴹ
      [⨟]ᴹ
        : [ τᴹ ⨟ᴹ σᴹ ]ᴹ Aᴹ ≡ [ τᴹ ]ᴹ ([ σᴹ ]ᴹ Aᴹ)
      [π₁,]ᴹ
        : ([ π₁ᴹ (σᴹ ,ˢᴹ tᴹ) ]ᴹ Aᴹ) ≡ [ σᴹ ]ᴹ Aᴹ
      [π₁⨟]ᴹ
        : [ π₁ᴹ (σᴹ ⨟ᴹ τᴹ) ]ᴹ Aᴹ ≡ [ σᴹ ]ᴹ ([ π₁ᴹ τᴹ ]ᴹ Aᴹ)
      π₂ᴹ
        : (σᴹ : Subᴹ Γᴹ (Δᴹ ,ᶜᴹ Aᴹ))
        → Tmᴹ Γᴹ ([ π₁ᴹ σᴹ ]ᴹ Aᴹ)
      [_]tmᴹ_
        : (σᴹ : Subᴹ Γᴹ Δᴹ) {Aᴹ : Tyᴹ Δᴹ i}
        → (tᴹ : Tmᴹ Δᴹ Aᴹ)
        → Tmᴹ Γᴹ ([ σᴹ ]ᴹ Aᴹ)
    
    _⁺ᴹ
      : (σᴹ : Subᴹ Γᴹ Δᴹ)
      → Subᴹ (Γᴹ ,ᶜᴹ ([ σᴹ ]ᴹ Aᴹ)) (Δᴹ ,ᶜᴹ Aᴹ)
    σᴹ ⁺ᴹ = (π₁ᴹ idSᴹ ⨟ᴹ σᴹ) ,ˢᴹ tr (Tmᴹ _) (sym $ [⨟]ᴹ) (π₂ᴹ idSᴹ)
    
    Subᴹ,ᶜᴹFam
      : {Γᴹ Δᴹ : Ctxᴹ} → Tyᴹ Γᴹ i → Set ℓ′
    Subᴹ,ᶜᴹFam {_} {Γᴹ} {Δᴹ} Aᴹ = Subᴹ (Γᴹ ,ᶜᴹ Aᴹ) Δᴹ

    field
      _↑ᴹ_
        : (σᴹ : Subᴹ Γᴹ Δᴹ)(Aᴹ : Tyᴹ Δᴹ i)
        → Subᴹ (Γᴹ ,ᶜᴹ ([ σᴹ ]ᴹ Aᴹ)) (Δᴹ ,ᶜᴹ Aᴹ)
      idS↑ᴹ
        : tr Subᴹ,ᶜᴹFam [idS]ᴹ (idSᴹ ↑ᴹ Aᴹ) ≡ idSᴹ
      ⨟↑ᴹ
        : tr Subᴹ,ᶜᴹFam [⨟]ᴹ ((σᴹ ⨟ᴹ τᴹ) ↑ᴹ Aᴹ)
        ≡ (σᴹ ↑ᴹ ([ τᴹ ]ᴹ Aᴹ)) ⨟ᴹ (τᴹ ↑ᴹ Aᴹ)
      π₁,↑ᴹ
        : tr Subᴹ,ᶜᴹFam [π₁,]ᴹ (π₁ᴹ (σᴹ ,ˢᴹ tᴹ) ↑ᴹ Aᴹ) ≡ σᴹ ↑ᴹ Aᴹ
      π₁⨟↑ᴹ
        : tr Subᴹ,ᶜᴹFam [π₁⨟]ᴹ (π₁ᴹ (σᴹ ⨟ᴹ τᴹ) ↑ᴹ Aᴹ) ≡ (σᴹ ↑ᴹ ([ π₁ᴹ τᴹ ]ᴹ Aᴹ)) ⨟ᴹ (π₁ᴹ τᴹ ↑ᴹ Aᴹ)
      ∅↑ᴹ
        : ∅ˢᴹ {Γᴹ = Γᴹ} ↑ᴹ Aᴹ ≡ ∅ˢᴹ ⁺ᴹ
      ,↑ᴹ
        : (σᴹ ,ˢᴹ tᴹ) ↑ᴹ Aᴹ ≡ (σᴹ ,ˢᴹ tᴹ) ⁺ᴹ
      π₁idS↑ᴹ
        : π₁ᴹ {Aᴹ = Bᴹ} idSᴹ ↑ᴹ Aᴹ ≡ π₁ᴹ idSᴹ ⁺ᴹ
      π₁π₁↑ᴹ
        : π₁ᴹ (π₁ᴹ σᴹ) ↑ᴹ Aᴹ ≡ π₁ᴹ (π₁ᴹ σᴹ) ⁺ᴹ

      [_]tᴹ_
        : (σᴹ : Subᴹ Γᴹ Δᴹ){Aᴹ : Tyᴹ Δᴹ i}(tᴹ : Tmᴹ Δᴹ Aᴹ)
        → Tmᴹ Γᴹ ([ σᴹ ]ᴹ Aᴹ)
      [idS]tᴹ
        :  tr TmᴹFam [idS]ᴹ ([ idSᴹ ]tᴹ tᴹ)  ≡ tᴹ
      [⨟]tᴹ
        : tr TmᴹFam [⨟]ᴹ ([ σᴹ ⨟ᴹ τᴹ ]tᴹ tᴹ)
        ≡ [ σᴹ ]tᴹ [ τᴹ ]tᴹ tᴹ
      [π₁,]tᴹ
        : tr TmᴹFam [π₁,]ᴹ ([ π₁ᴹ (σᴹ ,ˢᴹ tᴹ) ]tᴹ uᴹ)
        ≡ [ σᴹ ]tᴹ uᴹ
      [π₁⨟]tᴹ
        : tr TmᴹFam [π₁⨟]ᴹ ([ π₁ᴹ (σᴹ ⨟ᴹ τᴹ) ]tᴹ tᴹ)
        ≡ [ σᴹ ]tᴹ ([ π₁ᴹ τᴹ ]tᴹ tᴹ)
      [∅]tᴹ
        : [ ∅ˢᴹ {Δᴹ} ]tᴹ tᴹ ≡ [ ∅ˢᴹ ]tmᴹ tᴹ
      [,]tᴹ
        : [ σᴹ ,ˢᴹ tᴹ ]tᴹ uᴹ ≡ [ σᴹ ,ˢᴹ tᴹ ]tmᴹ uᴹ
      [π₁idS]tᴹ
        : [ π₁ᴹ {Γᴹ = Γᴹ ,ᶜᴹ Aᴹ} idSᴹ ]tᴹ tᴹ ≡ [ π₁ᴹ idSᴹ ]tmᴹ tᴹ
      [π₁π₁]tᴹ
        : [ π₁ᴹ (π₁ᴹ σᴹ) ]tᴹ tᴹ ≡ [ π₁ᴹ (π₁ᴹ σᴹ) ]tmᴹ tᴹ

      -- 
      _⨟idSᴹ
        : (σᴹ : Subᴹ Γᴹ Δᴹ)
        → σᴹ ⨟ᴹ idSᴹ ≡ σᴹ
      idS⨟ᴹ_
        : (σᴹ : Subᴹ Γᴹ Δᴹ)
        → idSᴹ ⨟ᴹ σᴹ ≡ σᴹ
      ⨟-assocᴹ
        : σᴹ ⨟ᴹ (τᴹ ⨟ᴹ γᴹ)
        ≡ (σᴹ ⨟ᴹ τᴹ) ⨟ᴹ γᴹ
      π₁,ᴹ
        : π₁ᴹ (σᴹ ,ˢᴹ tᴹ) ≡ σᴹ
      ⨟,ᴹ
        : σᴹ ⨟ᴹ (τᴹ ,ˢᴹ tᴹ)
        ≡ (σᴹ ⨟ᴹ τᴹ) ,ˢᴹ tr TmᴹFam (sym $ [⨟]ᴹ) ([ σᴹ ]tmᴹ tᴹ)
      η∅ᴹ
        : σᴹ ≡ ∅ˢᴹ
      η,ᴹ
        : σᴹ ≡ π₁ᴹ σᴹ ,ˢᴹ π₂ᴹ σᴹ
      [idS]tmᴹ
        : tr (Tmᴹ Γᴹ) [idS]ᴹ ([ idSᴹ ]tmᴹ tᴹ)
        ≡ tᴹ
      [⨟]tmᴹ
        : tr (Tmᴹ Γᴹ) [⨟]ᴹ ([ σᴹ ⨟ᴹ τᴹ ]tmᴹ tᴹ)
        ≡ [ σᴹ ]tmᴹ ([ τᴹ ]tmᴹ tᴹ)
      π₂,ᴹ
        : tr (Tmᴹ Γᴹ) [π₁,]ᴹ (π₂ᴹ (σᴹ ,ˢᴹ tᴹ))
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
      []Uᴹ
        : [ σᴹ ]ᴹ (Uᴹ i) ≡ Uᴹ i
      []Elᴹ
        : (σᴹ : Subᴹ Γᴹ Δᴹ)(uᴹ : Tmᴹ Δᴹ (Uᴹ i))
        → ([ σᴹ ]ᴹ (Elᴹ uᴹ)) ≡  Elᴹ (tr TmᴹFam []Uᴹ ([ σᴹ ]tᴹ uᴹ)) 
      []Liftᴹ
        : [ σᴹ ]ᴹ (Liftᴹ Aᴹ) ≡ Liftᴹ ([ σᴹ ]ᴹ Aᴹ)
      []tcᴹ
        : (σᴹ : Subᴹ Γᴹ Δᴹ)(Aᴹ : Tyᴹ Δᴹ i)
        → tr (Tmᴹ Γᴹ) []Uᴹ ([ σᴹ ]tmᴹ (cᴹ Aᴹ))
        ≡ cᴹ ([ σᴹ ]ᴹ Aᴹ)
      []mkᴹ
        : (σᴹ : Subᴹ Γᴹ Δᴹ) {Aᴹ : Tyᴹ Δᴹ i} (tᴹ : Tmᴹ Δᴹ Aᴹ)
        → tr (Tmᴹ Γᴹ) []Liftᴹ ([ σᴹ ]tmᴹ mkᴹ tᴹ)
        ≡ mkᴹ ([ σᴹ ]tᴹ tᴹ)
      []unᴹ
        : (σᴹ : Subᴹ Γᴹ Δᴹ) (Aᴹ : Tyᴹ Δᴹ i) (tᴹ : Tmᴹ Δᴹ (Liftᴹ Aᴹ))
        → [ σᴹ ]tmᴹ unᴹ tᴹ
        ≡ unᴹ (tr TmᴹFam []Liftᴹ ([ σᴹ ]tmᴹ tᴹ))
      Uβᴹ 
        : Elᴹ (cᴹ Aᴹ) ≡ Aᴹ
      Uηᴹ
        : cᴹ (Elᴹ uᴹ) ≡ uᴹ
      Liftβᴹ
        : unᴹ (mkᴹ tᴹ) ≡ tᴹ
      Liftηᴹ
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
      []Πᴹ
        : [ σᴹ ]ᴹ (Πᴹ Aᴹ Bᴹ) ≡ Πᴹ ([ σᴹ ]ᴹ Aᴹ) ([ σᴹ ↑ᴹ Aᴹ ]ᴹ Bᴹ)
      []ƛᴹ
        : (σᴹ : Subᴹ Γᴹ Δᴹ) (tᴹ : Tmᴹ (Δᴹ ,ᶜᴹ Aᴹ) Bᴹ)
        → tr (Tmᴹ Γᴹ) []Πᴹ ([ σᴹ ]tmᴹ (ƛᴹ tᴹ))
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
      []Idᴹ
        : [ σᴹ ]ᴹ (Idᴹ aᴹ tᴹ uᴹ)
        ≡ Idᴹ (tr TmᴹFam []Uᴹ ([ σᴹ ]tᴹ aᴹ))
            (tr TmᴹFam ([]Elᴹ σᴹ aᴹ) ([ σᴹ ]tᴹ tᴹ))
            (tr TmᴹFam ([]Elᴹ σᴹ aᴹ) ([ σᴹ ]tᴹ uᴹ))
      reflᴹ
        : (tᴹ : Tmᴹ Γᴹ (Elᴹ aᴹ))
        → Tmᴹ Γᴹ (Idᴹ aᴹ tᴹ tᴹ)
      []reflᴹ
          : (σᴹ : Subᴹ Γᴹ Δᴹ) {aᴹ : Tmᴹ Δᴹ (Uᴹ i)} (tᴹ : Tmᴹ Δᴹ (Elᴹ aᴹ))
          → tr (Tmᴹ Γᴹ) []Idᴹ ([ σᴹ ]tmᴹ (reflᴹ tᴹ))
          ≡ reflᴹ (tr TmᴹFam ([]Elᴹ σᴹ aᴹ) ([ σᴹ ]tᴹ tᴹ))
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
