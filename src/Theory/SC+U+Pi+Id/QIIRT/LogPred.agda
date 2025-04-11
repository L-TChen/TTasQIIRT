open import Prelude

module Theory.SC+U+Pi+Id.QIIRT.LogPred where

open import Theory.SC+U+Pi+Id.QIIRT.Syntax
open import Theory.SC+U+Pi+Id.QIIRT.Properties
open import Theory.SC+U+Pi+Id.QIIRT.Elimination
open Eliminator

record Ctxᵐ (Γ : Ctx) : Set where
  field
    ctxᵐ : Ctx
    wkᵐ : Sub ctxᵐ Γ
open Ctxᵐ

Tyᵐ : Ctxᵐ Γ → (i : ℕ) → Ty Γ i → Set
Tyᵐ Γᵐ i A = Ty (ctxᵐ Γᵐ , [ wkᵐ Γᵐ ] A) i

record Subᵐ {Γ Δ : Ctx}(Γᵐ : Ctxᵐ Γ)(Δᵐ : Ctxᵐ Δ)(σ : Sub Γ Δ) : Set where
  field
    subᵐ : Sub (ctxᵐ Γᵐ) (ctxᵐ Δᵐ)
    wkᵐnat : subᵐ ⨟ wkᵐ Δᵐ ≡ wkᵐ Γᵐ ⨟ σ
open Subᵐ

Tmᵐ : {A : Ty Γ i}(Γᵐ : Ctxᵐ Γ) → Tyᵐ Γᵐ i A → Tm Γ A → Set
Tmᵐ Γᵐ Aᵐ t = Tm (ctxᵐ Γᵐ) ([ idS , [ wkᵐ Γᵐ ]t t ] Aᵐ)

[_]ᵐ_
  : {Γᵐ : Ctxᵐ Γ}{Δᵐ : Ctxᵐ Δ} 
  → (σᵐ : Subᵐ Γᵐ Δᵐ σ)(Aᵐ : Tyᵐ Δᵐ i A)
  → Tyᵐ Γᵐ i ([ σ ] A)
[_]ᵐ_ {A = A} {Γᵐ = Γᵐ} {Δᵐ} σᵐ Aᵐ =
  [ 
    tr (λ A' → Sub (ctxᵐ Γᵐ , A') (ctxᵐ Δᵐ , [ wkᵐ Δᵐ ] A))
       (cong ([_] A) (wkᵐnat σᵐ)) -- two equalities on substitution composition are reduced here
       (subᵐ σᵐ ↑ [ wkᵐ Δᵐ ] A)
  ] Aᵐ

∅ᶜᵐ : Ctxᵐ ∅
∅ᶜᵐ = record
  { ctxᵐ = ∅
  ; wkᵐ  = ∅
  }

_,ᶜᵐ_
  : (Γᵐ : Ctxᵐ Γ)(Aᵐ : Tyᵐ Γᵐ i A)
  → Ctxᵐ (Γ , A)
_,ᶜᵐ_ {A = A} Γᵐ Aᵐ = record
  { ctxᵐ = (ctxᵐ Γᵐ , [ wkᵐ Γᵐ ] A) , Aᵐ
  ; wkᵐ  = wk ⨟ wkᵐ Γᵐ ↑ A 
  }

∅ˢᵐ : {Γᵐ : Ctxᵐ Γ} → Subᵐ Γᵐ ∅ᶜᵐ ∅
∅ˢᵐ = record
  { subᵐ   = ∅
  ; wkᵐnat = η∅ ∙ sym η∅
  }

_,ˢᵐ_
  : {Γᵐ : Ctxᵐ Γ}{Δᵐ : Ctxᵐ Δ}{Aᵐ : Tyᵐ Δᵐ i A}
  → (σᵐ : Subᵐ Γᵐ Δᵐ σ)(tᵐ : Tmᵐ Γᵐ ([_]ᵐ_ {A = A} σᵐ Aᵐ) t)
  → Subᵐ Γᵐ (Δᵐ ,ᶜᵐ Aᵐ) (_,_ σ {A} t)
_,ˢᵐ_ {A = A} {σ = σ} {t = t} {Γᵐ = Γᵐ} {Δᵐ} {Aᵐ} σᵐ tᵐ = record
  { subᵐ   = (subᵐ σᵐ , tr (Tm _) (cong ([_] A) (sym $ wkᵐnat σᵐ)) ([ wkᵐ Γᵐ ]t t))
                      , tr (Tm _) {!   !} tᵐ
  ; wkᵐnat = {!   !}
  }

idSᵐ : {Γᵐ : Ctxᵐ Γ} → Subᵐ Γᵐ Γᵐ idS
idSᵐ {Γᵐ = Γᵐ} = record
  { subᵐ   = idS
  ; wkᵐnat = (idS⨟ wkᵐ Γᵐ) ∙ (sym $ wkᵐ Γᵐ ⨟idS)
  }

_⨟ᵐ_
  :{Γᵐ : Ctxᵐ Γ}{Δᵐ : Ctxᵐ Δ}{Θᵐ : Ctxᵐ Θ}
  → (σᵐ : Subᵐ Γᵐ Δᵐ σ)(τᵐ : Subᵐ Δᵐ Θᵐ τ)
  → Subᵐ Γᵐ Θᵐ (σ ⨟ τ)
_⨟ᵐ_ {τ = τ} σᵐ τᵐ = record
  { subᵐ   = subᵐ σᵐ ⨟ subᵐ τᵐ
  ; wkᵐnat = sym ⨟-assoc
           ∙ cong (subᵐ σᵐ ⨟_) (wkᵐnat τᵐ)
           ∙ ⨟-assoc
           ∙ cong (_⨟ τ) (wkᵐnat σᵐ)
           ∙ sym ⨟-assoc
  }

π₁ᵐ
  : {Γᵐ : Ctxᵐ Γ}{Δᵐ : Ctxᵐ Δ}{Aᵐ : Tyᵐ Δᵐ i A}
  → (σᵐ : Subᵐ Γᵐ (_,ᶜᵐ_ {A = A} Δᵐ Aᵐ) σ)
  → Subᵐ Γᵐ Δᵐ (π₁ σ)
π₁ᵐ {Δᵐ = Δᵐ} σᵐ = record
  { subᵐ   = π₁ (π₁ (subᵐ σᵐ))
  ; wkᵐnat = {!   !}
  }

π₂ᵐ
  : {Γᵐ : Ctxᵐ Γ}{Δᵐ : Ctxᵐ Δ}{Aᵐ : Tyᵐ Δᵐ i A}
  → (σᵐ : Subᵐ Γᵐ (_,ᶜᵐ_ {A = A} Δᵐ Aᵐ) σ)
  → Tmᵐ Γᵐ ([_]ᵐ_ {A = A} {Δᵐ = Δᵐ} (π₁ᵐ σᵐ) Aᵐ) (π₂ σ)
π₂ᵐ σᵐ = tr (Tm _) {!   !} (π₂ (subᵐ σᵐ))

[_]tmᵐ_
  : {Γᵐ : Ctxᵐ Γ}{Δᵐ : Ctxᵐ Δ}
  → (σᵐ : Subᵐ Γᵐ Δᵐ σ){Aᵐ : Tyᵐ Δᵐ i A}(tᵐ : Tmᵐ {A = A} Δᵐ Aᵐ t)
  → Tmᵐ Γᵐ ([_]ᵐ_ {A = A} σᵐ Aᵐ) ([ σ ]tm t)
[_]tmᵐ_ σᵐ tᵐ = tr (Tm _) {!   !} ([ subᵐ σᵐ ]tm tᵐ)

_↑ᵐ_
  : {Γᵐ : Ctxᵐ Γ}{Δᵐ : Ctxᵐ Δ}
  → (σᵐ : Subᵐ Γᵐ Δᵐ σ)(Aᵐ : Tyᵐ Δᵐ i A)
  → Subᵐ (Γᵐ ,ᶜᵐ ([_]ᵐ_ {A = A} σᵐ Aᵐ)) (Δᵐ ,ᶜᵐ Aᵐ) (σ ↑ A)
_↑ᵐ_ {A = A} {Γᵐ = Γᵐ} {Δᵐ} σᵐ Aᵐ = record
  { subᵐ = tr (λ A' → Sub (ctxᵐ Γᵐ , A') (ctxᵐ Δᵐ , [ wkᵐ Δᵐ ] A))
              (cong ([_] A) (wkᵐnat σᵐ)) -- two equalities on substitution composition are reduced here
              (subᵐ σᵐ ↑ [ wkᵐ Δᵐ ] A)
           ↑ Aᵐ
  ; wkᵐnat = {!   !}
  }

[_]tᵐ_
  : {Γᵐ : Ctxᵐ Γ}{Δᵐ : Ctxᵐ Δ}{Aᵐ : Tyᵐ Δᵐ i A}
  → (σᵐ : Subᵐ Γᵐ Δᵐ σ)(tᵐ : Tmᵐ {A = A} Δᵐ Aᵐ t)
  → Tmᵐ Γᵐ ([_]ᵐ_ {A = A} σᵐ Aᵐ) ([ σ ]t t)
[_]tᵐ_ σᵐ tᵐ = tr (Tm _) {!   !} ([ subᵐ σᵐ ]t tᵐ)

Uᵐ
  : {Γᵐ : Ctxᵐ Γ}(i : ℕ)
  → Tyᵐ Γᵐ (suc i) (U i)
Uᵐ i = U i -- transports are reduced here

Elᵐ
  : {Γᵐ : Ctxᵐ Γ}
  → Tmᵐ Γᵐ (Uᵐ {Γᵐ = Γᵐ} i) u
  → Tyᵐ Γᵐ i (El u)
Elᵐ {Γᵐ = Γᵐ} uᵐ = El ([ wk ]t uᵐ) -- transports are reduced here

logpred : Eliminator
logpred .mot = record
  { Ctxᴹ = Ctxᵐ
  ; Tyᴹ  = Tyᵐ
  ; Subᴹ = Subᵐ
  ; Tmᴹ  = Tmᵐ
  }
logpred .met = record
  { 𝒞 = record
    { [_]ᴹ_   = [_]ᵐ_
    ; ∅ᶜᴹ     = ∅ᶜᵐ
    ; _,ᶜᴹ_   = _,ᶜᵐ_
    ; ∅ˢᴹ     = ∅ˢᵐ
    ; _,ˢᴹ_   = _,ˢᵐ_
    ; idSᴹ    = idSᵐ
    ; _⨟ᴹ_    = _⨟ᵐ_
    ; π₁ᴹ     = π₁ᵐ
    ; π₂ᴹ     = π₂ᵐ
    ; [_]tmᴹ_ = [_]tmᵐ_
    ; _↑ᴹ_    = _↑ᵐ_
    ; [_]tᴹ_  = [_]tᵐ_
    }
  ; univ = record
    { Uᴹ = Uᵐ
    ; Elᴹ = Elᵐ
    }
  }                    