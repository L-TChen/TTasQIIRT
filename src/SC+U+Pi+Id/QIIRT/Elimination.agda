-- Elimination of Substitution Calculus
module SC+U+Pi+Id.QIIRT.Elimination where

open import Prelude
  renaming (_,_ to _,'_)
open import SC+U+Pi+Id.QIIRT.Syntax
open import SC+U+Pi+Id.QIIRT.Elimination.Motive
open import SC+U+Pi+Id.QIIRT.Elimination.Method
open import SC+U+Pi+Id.QIIRT.Properties

record Eliminator {ℓ ℓ′} : Set (lsuc (ℓ ⊔ ℓ′)) where
  field
    mot : Motive {ℓ} {ℓ′}
    met : Method mot
  
  open Motive mot public
  open Method met public

module elim {ℓ ℓ′}(M : Eliminator {ℓ} {ℓ′}) where
  open Eliminator M

  {-# TERMINATING #-}
  elimCtx
    : (Γ : Ctx) → Ctxᴹ Γ
  elimTy
    : (A : Ty Γ i) → Tyᴹ (elimCtx Γ) i A
  elimSub
    : (σ : Sub Δ Γ) → Subᴹ (elimCtx Δ) (elimCtx Γ) σ
  elimTm
    : (t : Tm Γ A) → Tmᴹ (elimCtx Γ) (elimTy A) t
  elimTy[]
    : (σ : Sub Δ Γ)(A : Ty Γ i)
    → [ elimSub σ ]ᴹ elimTy A ≡ elimTy ([ σ ] A)
  elimTm[]
    : (σ : Sub Δ Γ){A : Ty Γ i}(t : Tm Γ A)
    → tr TmᴹFamₜ (elimTy[] σ A) ([ elimSub σ ]tᴹ elimTm t) ≡ elimTm ([ σ ]t t)
  
  elimCtx ∅          = ∅ᶜᴹ
  elimCtx (Γ , A)    = elimCtx Γ ,ᶜᴹ elimTy A
  elimTy (U i)       = Uᴹ i
  elimTy (El u)      = Elᴹ (elimTm u)
  elimTy (Lift A)    = Liftᴹ (elimTy A)
  elimTy (Π A B)     = Πᴹ (elimTy A) (elimTy B)
  elimTy (Id a t u)  = Idᴹ (elimTm a) (elimTm t) (elimTm u)
  elimSub ∅          = ∅ˢᴹ
  elimSub (σ , t)    = elimSub σ ,ˢᴹ tr TmᴹFamₜ (sym $ elimTy[] σ _) (elimTm t)
  elimSub idS        = idSᴹ
  elimSub (τ ⨟ σ)    = elimSub τ ⨟ᴹ elimSub σ
  elimSub (π₁ σ)     = π₁ᴹ (elimSub σ)
  elimTm (π₂ σ)      = tr TmᴹFamₜ (elimTy[] (π₁ σ) _) (π₂ᴹ (elimSub σ))
  elimTm ([ σ ]tm t) = tr TmᴹFamₜ (elimTy[] σ _) ([ elimSub σ ]tmᴹ elimTm t)
  elimTm (c A)       = cᴹ (elimTy A)
  elimTm (mk t)      = mkᴹ (elimTm t)
  elimTm (un t)      = unᴹ (elimTm t)
  elimTm (ƛ t)       = (ƛᴹ elimTm t)
  elimTm (app t)     = appᴹ (elimTm t)
  elimTm (refl t)    = reflᴹ (elimTm t)

  elimSub↑-tot
    : (σ : Sub Δ Γ)(A : Ty Γ i)
    → _≡_ {A = ∃ λ PB → Subᴹ (elimCtx Δ ,ᶜᴹ PB) (elimCtx Γ ,ᶜᴹ elimTy A) (σ ↑ A)}
      ([ elimSub σ ]ᴹ elimTy A ,' elimSub σ ↑ᴹ elimTy A)
      (elimTy ([ σ ] A) ,' elimSub (σ ↑ A))

  elimTy[] σ (U i) = []ᴹUᴹ
  elimTy[] σ (El u) = begin
    [ elimSub σ ]ᴹ elimTy (El u)
      ≡⟨ []ᴹElᴹ (elimSub σ) (elimTm u) ⟩
    Elᴹ (tr TmᴹFamₜ []ᴹUᴹ ([ elimSub σ ]tᴹ elimTm u))
      ≡⟨ cong Elᴹ (elimTm[] σ u) ⟩
    Elᴹ (elimTm ([ σ ]t u))
      ∎
    where open ≡-Reasoning
  elimTy[] σ (Lift A) = begin
    [ elimSub σ ]ᴹ Liftᴹ (elimTy A)
      ≡⟨ []ᴹLiftᴹ ⟩
    Liftᴹ ([ elimSub σ ]ᴹ elimTy A)
      ≡⟨ cong Liftᴹ (elimTy[] σ A) ⟩
    Liftᴹ (elimTy ([ σ ] A))
      ∎
    where open ≡-Reasoning
  elimTy[] {Δ} {Γ} {i} σ (Π A B) =
      begin
    [ elimSub σ ]ᴹ Πᴹ (elimTy A) (elimTy B)
      ≡⟨ []ᴹΠᴹ ⟩
    Πᴹ ([ elimSub σ ]ᴹ elimTy A) ([ elimSub σ ↑ᴹ elimTy A ]ᴹ elimTy B)
      ≡⟨ cong (uncurry Πᴹ) eq ⟩
    Πᴹ (elimTy ([ σ ] A)) (elimTy ([ σ ↑ A ] B))
      ∎
    where
      open ≡-Reasoning
      eq : _≡_ {A = ∃ λ PB → Tyᴹ (elimCtx Δ ,ᶜᴹ PB) i ([ σ ↑ A ] B)}
                ([ elimSub σ ]ᴹ elimTy A ,' [ elimSub σ ↑ᴹ elimTy A ]ᴹ elimTy B)
                (elimTy ([ σ ] A) ,' elimTy ([ σ ↑ A ] B))
      eq = begin
        [ elimSub σ ]ᴹ elimTy A ,' [ elimSub σ ↑ᴹ elimTy A ]ᴹ elimTy B
          ≡⟨ ap₂Σ ([_]ᴹ elimTy B) (elimSub↑-tot σ A) ⟩
        elimTy ([ σ ] A) ,' ([ elimSub (σ ↑ A) ]ᴹ elimTy B)
          ≡⟨ cong (elimTy ([ σ ] A) ,'_) (elimTy[] (σ ↑ A) B) ⟩
        elimTy ([ σ ] A) ,' elimTy ([ σ ↑ A ] B)
          ∎
      {-
      eq : tr (λ PB → Tyᴹ (elimCtx Δ ,ᶜᴹ PB) i ([ σ ↑ A ] B))
              (elimTy[] σ A)
              ([ elimSub σ ↑ᴹ elimTy A ]ᴹ elimTy B)
          ≡ elimTy ([ σ ↑ A ] B)
      eq = begin
        tr (λ PB → Tyᴹ (elimCtx Δ ,ᶜᴹ PB) i ([ σ ↑ A ] B))
           (elimTy[] σ A)
           ([ elimSub σ ↑ᴹ elimTy A ]ᴹ elimTy B)
          ≡⟨ tr-nat (λ PB → Subᴹ (elimCtx Δ ,ᶜᴹ PB) (elimCtx Γ ,ᶜᴹ elimTy A) (σ ↑ A))
                    (λ _ Pσ → [ Pσ ]ᴹ elimTy B)
                    (elimTy[] σ A) ⟩
        [ tr (λ PB → Subᴹ (elimCtx Δ ,ᶜᴹ PB) (elimCtx Γ ,ᶜᴹ elimTy A) (σ ↑ A))
             (elimTy[] σ A)
             (elimSub σ ↑ᴹ elimTy A) ]ᴹ elimTy B
          ≡⟨ cong ([_]ᴹ elimTy B) (elimSub↑ σ A) ⟩
        [ elimSub (σ ↑ A) ]ᴹ elimTy B
          ≡⟨ elimTy[] (σ ↑ A) B ⟩
        elimTy ([ σ ↑ A ] B)
          ∎
      -}
  elimTy[] {Δ} {Γ} {i} σ (Id a t u) = begin
    [ elimSub σ ]ᴹ Idᴹ (elimTm a) (elimTm t) (elimTm u)
      ≡⟨ []ᴹIdᴹ ⟩
    Idᴹ tr[Eσ]Ea tr[Eσ]Et tr[Eσ]Eu
      ≡⟨ cong₃ Idᴹ eqa eqt equ ⟩
    Idᴹ (elimTm ([ σ ]t a)) (elimTm ([ σ ]t t)) (elimTm ([ σ ]t u))
      ∎
      where
        open ≡-Reasoning
        tr[Eσ]Ea = tr TmᴹFamₜ []ᴹUᴹ ([ elimSub σ ]tᴹ elimTm a)
        tr[Eσ]Et = tr TmᴹFamₜ ([]ᴹElᴹ (elimSub σ) (elimTm a)) ([ elimSub σ ]tᴹ elimTm t)
        tr[Eσ]Eu = tr TmᴹFamₜ ([]ᴹElᴹ (elimSub σ) (elimTm a)) ([ elimSub σ ]tᴹ elimTm u)

        eqa : tr[Eσ]Ea ≡ elimTm ([ σ ]t a)
        eqa = elimTm[] σ a

        eqt : tr (λ Pa → TmᴹFamₜ (Elᴹ Pa)) eqa tr[Eσ]Et ≡ elimTm ([ σ ]t t)
        eqt = begin
          tr (λ Pa → TmᴹFamₜ (Elᴹ Pa)) eqa tr[Eσ]Et
            ≡⟨ tr-cong eqa ⟩
          tr TmᴹFamₜ (cong Elᴹ eqa) tr[Eσ]Et
            ≡⟨ tr² ([]ᴹElᴹ (elimSub σ) (elimTm a)) {cong Elᴹ eqa} ⟩
          tr TmᴹFamₜ (trans ([]ᴹElᴹ (elimSub σ) (elimTm a)) (cong Elᴹ eqa)) ([ elimSub σ ]tᴹ elimTm t)
            ≡⟨ cong (λ p → tr TmᴹFamₜ p ([ elimSub σ ]tᴹ elimTm t)) 
                    (uip (trans ([]ᴹElᴹ (elimSub σ) (elimTm a)) (cong Elᴹ eqa))
                         (elimTy[] σ (El a))) ⟩
          tr TmᴹFamₜ (elimTy[] σ (El a)) ([ elimSub σ ]tᴹ elimTm t)
            ≡⟨ elimTm[] σ t ⟩
          elimTm ([ σ ]t t)
            ∎

        equ : tr (λ Pa → TmᴹFamₜ (Elᴹ Pa)) eqa tr[Eσ]Eu ≡ elimTm ([ σ ]t u)
        equ = begin
          tr (λ Pa → TmᴹFamₜ (Elᴹ Pa)) eqa tr[Eσ]Eu
            ≡⟨ tr-cong eqa ⟩
          tr TmᴹFamₜ (cong Elᴹ eqa) tr[Eσ]Eu
            ≡⟨ tr² ([]ᴹElᴹ (elimSub σ) (elimTm a)) {cong Elᴹ eqa} ⟩
          tr TmᴹFamₜ (trans ([]ᴹElᴹ (elimSub σ) (elimTm a)) (cong Elᴹ eqa)) ([ elimSub σ ]tᴹ elimTm u)
            ≡⟨ cong (λ p → tr TmᴹFamₜ p ([ elimSub σ ]tᴹ elimTm u)) 
                    (uip (trans ([]ᴹElᴹ (elimSub σ) (elimTm a)) (cong Elᴹ eqa))
                         (elimTy[] σ (El a))) ⟩
          tr TmᴹFamₜ (elimTy[] σ (El a)) ([ elimSub σ ]tᴹ elimTm u)
            ≡⟨ elimTm[] σ u ⟩
          elimTm ([ σ ]t u)
            ∎

  elimTm[] idS {A} t = begin
    tr TmᴹFamₜ (elimTy[] idS A) ([ elimSub idS ]tᴹ elimTm t)
      ≡⟨ cong (λ p → tr TmᴹFamₜ p ([ elimSub idS ]tᴹ elimTm t)) (uip _ [idSᴹ]) ⟩
    tr TmᴹFamₜ [idSᴹ] ([ elimSub idS ]tᴹ elimTm t)
      ≡⟨ [idSᴹ]tᴹ ⟩
    elimTm t
      ∎
    where open ≡-Reasoning
  elimTm[] (τ ⨟ σ) {A} t = begin
    tr TmᴹFamₜ (elimTy[] (τ ⨟ σ) A) ([ elimSub τ ⨟ᴹ elimSub σ ]tᴹ elimTm t)
      ≡⟨ cong (λ p → tr TmᴹFamₜ p ([ elimSub τ ⨟ᴹ elimSub σ ]tᴹ elimTm t)) (uip _ (trans [⨟ᴹ]ᴹ eq)) ⟩
    tr TmᴹFamₜ (trans [⨟ᴹ]ᴹ eq) ([ elimSub τ ⨟ᴹ elimSub σ ]tᴹ elimTm t)
      ≡⟨ tr² [⨟ᴹ]ᴹ ⟨
    tr TmᴹFamₜ eq (tr TmᴹFamₜ [⨟ᴹ]ᴹ ([ elimSub τ ⨟ᴹ elimSub σ ]tᴹ elimTm t))
      ≡⟨ cong (tr TmᴹFamₜ eq) [⨟ᴹ]tᴹ ⟩
    tr TmᴹFamₜ eq ([ elimSub τ ]tᴹ ([ elimSub σ ]tᴹ elimTm t))
      ≡⟨ tr² (cong ([ elimSub τ ]ᴹ_) (elimTy[] σ A)) ⟨
    tr TmᴹFamₜ (elimTy[] τ _)
      (tr TmᴹFamₜ (cong ([ elimSub τ ]ᴹ_) (elimTy[] σ A))
         ([ elimSub τ ]tᴹ ([ elimSub σ ]tᴹ elimTm t)))
      ≡⟨ cong (tr TmᴹFamₜ (elimTy[] τ ([ σ ] A)))
              (tr-cong {P = TmᴹFamₜ} (elimTy[] σ A)) ⟨
    tr TmᴹFamₜ (elimTy[] τ _) (tr (λ Aᴹ → TmᴹFamₜ ([ elimSub τ ]ᴹ Aᴹ)) (elimTy[] σ A)
                                  ([ elimSub τ ]tᴹ ([ elimSub σ ]tᴹ elimTm t)))
      ≡⟨ cong (tr TmᴹFamₜ (elimTy[] τ ([ σ ] A)))
              (tr-nat TmᴹFamₜ (λ _ tᴹ → [ elimSub τ ]tᴹ tᴹ) (elimTy[] σ A)) ⟩
    tr TmᴹFamₜ (elimTy[] τ _) ([ elimSub τ ]tᴹ tr TmᴹFamₜ (elimTy[] σ A) ([ elimSub σ ]tᴹ elimTm t))
      ≡⟨ cong (λ tᴹ → tr TmᴹFamₜ (elimTy[] τ _) ([ elimSub τ ]tᴹ tᴹ))
              (elimTm[] σ t) ⟩
    tr TmᴹFamₜ (elimTy[] τ _) ([ elimSub τ ]tᴹ elimTm ([ σ ]t t))
      ≡⟨ elimTm[] τ ([ σ ]t t) ⟩
    elimTm ([ τ ]t [ σ ]t t)
      ∎
    where
      open ≡-Reasoning
      eq : [ elimSub τ ]ᴹ ([ elimSub σ ]ᴹ elimTy A) ≡ elimTy ([ τ ] [ σ ] A)
      eq = trans (cong ([ elimSub τ ]ᴹ_) (elimTy[] σ A)) (elimTy[] τ _)

  elimTm[] (π₁ (σ , u))  {A} t = begin
    tr TmᴹFamₜ (elimTy[] (π₁ (σ , u)) A) ([ π₁ᴹ (elimSub σ ,ˢᴹ _) ]tᴹ elimTm t)
      ≡⟨ cong (λ p → tr TmᴹFamₜ p ([ π₁ᴹ (elimSub σ ,ˢᴹ _) ]tᴹ elimTm t))
              (uip _ (trans [π₁ᴹ,ˢᴹ]ᴹ (elimTy[] σ A))) ⟩
    tr TmᴹFamₜ (trans [π₁ᴹ,ˢᴹ]ᴹ (elimTy[] σ A)) ([ π₁ᴹ (elimSub σ ,ˢᴹ _) ]tᴹ elimTm t)
      ≡⟨ tr² {P = TmᴹFamₜ} [π₁ᴹ,ˢᴹ]ᴹ ⟨
    tr TmᴹFamₜ (elimTy[] σ A)
       (tr TmᴹFamₜ [π₁ᴹ,ˢᴹ]ᴹ ([ π₁ᴹ (elimSub σ ,ˢᴹ _) ]tᴹ elimTm t))
      ≡⟨ cong (tr TmᴹFamₜ (elimTy[] σ A)) [π₁ᴹ,ˢᴹ]tᴹ ⟩
    tr TmᴹFamₜ (elimTy[] σ A) ([ elimSub σ ]tᴹ elimTm t)
      ≡⟨ elimTm[] σ t ⟩
    elimTm ([ σ ]t t)
      ∎
    where open ≡-Reasoning
  elimTm[] (π₁ (σ ⨟ τ))  {A} t = begin
    tr TmᴹFamₜ (elimTy[] (π₁ (σ ⨟ τ)) A)
          ([ π₁ᴹ (elimSub σ ⨟ᴹ elimSub τ) ]tᴹ elimTm t)
      ≡⟨ cong (λ p → tr TmᴹFamₜ p ([ π₁ᴹ (elimSub σ ⨟ᴹ elimSub τ) ]tᴹ elimTm t))
              (uip _ (trans [π₁ᴹ⨟ᴹ]ᴹ eq)) ⟩
    tr TmᴹFamₜ (trans [π₁ᴹ⨟ᴹ]ᴹ eq) ([ π₁ᴹ (elimSub σ ⨟ᴹ elimSub τ) ]tᴹ elimTm t)
      ≡⟨ tr² {P = TmᴹFamₜ} [π₁ᴹ⨟ᴹ]ᴹ ⟨
    tr TmᴹFamₜ eq (tr TmᴹFamₜ [π₁ᴹ⨟ᴹ]ᴹ ([ π₁ᴹ (elimSub σ ⨟ᴹ elimSub τ) ]tᴹ elimTm t))
      ≡⟨ cong (tr TmᴹFamₜ eq) [π₁ᴹ⨟ᴹ]tᴹ ⟩
    tr TmᴹFamₜ eq ([ elimSub σ ]tᴹ ([ π₁ᴹ (elimSub τ) ]tᴹ elimTm t))
      ≡⟨ tr² {P = TmᴹFamₜ} (cong ([ elimSub σ ]ᴹ_) (elimTy[] (π₁ τ) A)) ⟨
    tr TmᴹFamₜ (elimTy[] σ ([ π₁ τ ] A))
       (tr TmᴹFamₜ (cong ([ elimSub σ ]ᴹ_) (elimTy[] (π₁ τ) A)) _)
      ≡⟨ cong (tr TmᴹFamₜ (elimTy[] σ ([ π₁ τ ] A)))
              (tr-cong {P = TmᴹFamₜ} (elimTy[] (π₁ τ) A)) ⟨
    tr TmᴹFamₜ (elimTy[] σ ([ π₁ τ ] A))
       (tr (λ Aᴹ → TmᴹFamₜ ([ elimSub σ ]ᴹ Aᴹ)) (elimTy[] (π₁ τ) A) _)
      ≡⟨ cong (tr TmᴹFamₜ (elimTy[] σ ([ π₁ τ ] A)))
              (tr-nat TmᴹFamₜ (λ _ tᴹ → [ elimSub σ ]tᴹ tᴹ) (elimTy[] (π₁ τ) A)) ⟩
    tr TmᴹFamₜ (elimTy[] σ ([ π₁ τ ] A))
       ([ elimSub σ ]tᴹ tr TmᴹFamₜ (elimTy[] (π₁ τ) A) ([ elimSub (π₁ τ) ]tᴹ elimTm t))
      ≡⟨ cong (λ tᴹ → tr TmᴹFamₜ (elimTy[] σ ([ π₁ τ ] A)) ([ elimSub σ ]tᴹ tᴹ))
              (elimTm[] (π₁ τ)t) ⟩
    tr TmᴹFamₜ (elimTy[] σ ([ π₁ τ ] A)) ([ elimSub σ ]tᴹ elimTm ([ π₁ τ ]t t))
      ≡⟨ elimTm[] σ ([ π₁ τ ]t t) ⟩
    elimTm ([ σ ]t [ π₁ τ ]t t)
      ∎
    where
      open ≡-Reasoning
      eq : [ elimSub σ ]ᴹ ([ π₁ᴹ (elimSub τ) ]ᴹ elimTy A) ≡ elimTy ([ σ ] [ π₁ τ ] A)
      eq = trans (cong ([ elimSub σ ]ᴹ_) (elimTy[] (π₁ τ) A)) (elimTy[] σ ([ π₁ τ ] A))
  
  elimTm[]  ∅            {A} t = cong (tr TmᴹFamₜ (elimTy[] ∅ A)) [∅ˢᴹ]tᴹ
  elimTm[] (σ , u)       {A} t = cong (tr TmᴹFamₜ (elimTy[] (σ , u) A)) [,ˢᴹ]tᴹ
  elimTm[] (π₁ idS)      {A} t = cong (tr TmᴹFamₜ (elimTy[] (π₁ idS) A)) [π₁ᴹidSᴹ]tᴹ
  elimTm[] (π₁ (π₁ σ))   {A} t = cong (tr TmᴹFamₜ (elimTy[] (π₁ (π₁ σ)) A)) [π₁ᴹπ₁ᴹ]tᴹ

  elimSub↑-tot idS A = begin
    ([ idSᴹ ]ᴹ elimTy A) ,' (idSᴹ ↑ᴹ elimTy A)
      ≡⟨ _ ,Σ≡ idSᴹ↑ᴹ ⟩
    elimTy ([ idS ] A) ,' elimSub (idS ↑ A)
      ∎
    where open ≡-Reasoning
  elimSub↑-tot {Δ} {Γ} {i} (_⨟_ {Δ = Θ} σ τ) A = begin
    [ elimSub σ ⨟ᴹ elimSub τ ]ᴹ elimTy A ,' (elimSub σ ⨟ᴹ elimSub τ) ↑ᴹ elimTy A
      ≡⟨ _ ,Σ≡ ⨟ᴹ↑ᴹ ⟩
    [ elimSub σ ]ᴹ ([ elimSub τ ]ᴹ elimTy A) ,'
    (elimSub σ ↑ᴹ ([ elimSub τ ]ᴹ elimTy A)) ⨟ᴹ (elimSub τ ↑ᴹ elimTy A)
      ≡⟨ apΣ Subᴹ,ᶜᴹFam ([ elimSub σ ]ᴹ_) (ap₂Σ (λ {Aᴹ} τᴹ → (elimSub σ ↑ᴹ Aᴹ) ⨟ᴹ τᴹ) (elimSub↑-tot τ A)) ⟩
    [ elimSub σ ]ᴹ elimTy ([ τ ] A) ,'
    (elimSub σ ↑ᴹ elimTy ([ τ ] A)) ⨟ᴹ elimSub (τ ↑ A)
      ≡⟨ ap₂Σ (_⨟ᴹ elimSub (τ ↑ A)) (elimSub↑-tot σ ([ τ ] A)) ⟩
    elimTy ([ σ ] [ τ ] A) ,' elimSub (σ ↑ ([ τ ] A)) ⨟ᴹ elimSub (τ ↑ A)
      ∎
    where open ≡-Reasoning
  
  elimSub↑-tot {Δ} {Γ} {i} (π₁ (σ , t)) A = begin
    [ π₁ᴹ (elimSub σ ,ˢᴹ _) ]ᴹ elimTy A ,' (π₁ᴹ (elimSub σ ,ˢᴹ _) ↑ᴹ elimTy A)
      ≡⟨ _ ,Σ≡ π₁ᴹ,ˢᴹ↑ᴹ ⟩
    [ elimSub σ ]ᴹ elimTy A ,' elimSub σ ↑ᴹ elimTy A
      ≡⟨ elimSub↑-tot σ A ⟩
    elimTy ([ σ ] A) ,' elimSub (σ ↑ A)
      ∎
    where open ≡-Reasoning
  elimSub↑-tot (π₁ (σ ⨟ τ)) A = begin
    [ π₁ᴹ (elimSub σ ⨟ᴹ elimSub τ) ]ᴹ elimTy A ,' π₁ᴹ (elimSub σ ⨟ᴹ elimSub τ) ↑ᴹ elimTy A
      ≡⟨ _ ,Σ≡ π₁ᴹ⨟ᴹ↑ᴹ ⟩
    [ elimSub σ ]ᴹ ([ π₁ᴹ (elimSub τ) ]ᴹ elimTy A) ,'
    (elimSub σ ↑ᴹ ([ π₁ᴹ (elimSub τ) ]ᴹ elimTy A)) ⨟ᴹ (π₁ᴹ (elimSub τ) ↑ᴹ elimTy A)
      ≡⟨ apΣ Subᴹ,ᶜᴹFam ([ elimSub σ ]ᴹ_) (ap₂Σ (λ {Aᴹ} τᴹ → (elimSub σ ↑ᴹ Aᴹ) ⨟ᴹ τᴹ) (elimSub↑-tot (π₁ τ) A)) ⟩
    [ elimSub σ ]ᴹ elimTy ([ π₁ τ ] A) ,'
    (elimSub σ ↑ᴹ elimTy ([ π₁ τ ] A)) ⨟ᴹ elimSub (π₁ τ ↑ A)
      ≡⟨ ap₂Σ (_⨟ᴹ elimSub (π₁ τ ↑ A)) (elimSub↑-tot σ ([ π₁ τ ] A)) ⟩
    elimTy ([ σ ] [ π₁ τ ] A) ,' elimSub (σ ↑ ([ π₁ τ ] A)) ⨟ᴹ elimSub (π₁ τ ↑ A)
      ∎
    where open ≡-Reasoning
  elimSub↑-tot ∅ A = ≅-to-≡ $ begin
    [ ∅ˢᴹ ]ᴹ elimTy A ,' ∅ˢᴹ ↑ᴹ elimTy A
      ≡⟨ _ ,Σ≡ ∅ˢᴹ↑ᴹ ⟩
    [ ∅ˢᴹ ]ᴹ elimTy A ,' (π₁ᴹ idSᴹ ⨟ᴹ ∅ˢᴹ) ,ˢᴹ tr TmᴹFamₜ (sym $ [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ)
      ≡⟨ ap₂Σ ((π₁ᴹ idSᴹ ⨟ᴹ ∅ˢᴹ) ,ˢᴹ_) (elimTy[] ∅ A ,Σ≡ ≅-to-≡ heq) ⟩
    elimTy ([ ∅ ] A) ,' _
      ∎
      where
        open ≅-Reasoning
        heq : tr (λ Aᴹ → Tmᴹ (elimCtx Δ ,ᶜᴹ Aᴹ) ([ π₁ᴹ idSᴹ ⨟ᴹ ∅ˢᴹ ]ᴹ elimTy A) vz)
                (elimTy[] ∅ A)
                (tr TmᴹFamₜ (sym [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ))
           ≅ tr TmᴹFamₜ (sym $ elimTy[] (wk ⨟ ∅) A)
                (tr TmᴹFamₜ (elimTy[] wk ([ ∅ ] A)) (π₂ᴹ idSᴹ))
        heq {Δ} = begin
          tr (λ Aᴹ → Tmᴹ (elimCtx Δ ,ᶜᴹ Aᴹ) ([ π₁ᴹ idSᴹ ⨟ᴹ ∅ˢᴹ ]ᴹ elimTy A) vz)
             (elimTy[] ∅ A)
             (tr TmᴹFamₜ (sym [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ))
            ≅⟨ tr≅ (λ Aᴹ → Tmᴹ (elimCtx Δ ,ᶜᴹ Aᴹ) ([ π₁ᴹ idSᴹ ⨟ᴹ ∅ˢᴹ ]ᴹ elimTy A) vz)
                   (elimTy[] ∅ A) _ ⟩
          tr TmᴹFamₜ (sym [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ)
            ≅⟨ tr≅ TmᴹFamₜ (sym [⨟ᴹ]ᴹ) _ ⟩
          π₂ᴹ {Aᴹ = [ elimSub ∅ ]ᴹ elimTy A} idSᴹ
            ≅⟨ vzᴹ≅ ⟩
          π₂ᴹ {Aᴹ = elimTy ([ ∅ ] A)} idSᴹ
            ≅⟨ tr≅ TmᴹFamₜ (trans (elimTy[] wk ([ ∅ ] A)) (sym $ elimTy[] (wk ⨟ ∅) A)) _ ⟨
          tr TmᴹFamₜ (trans (elimTy[] wk ([ ∅ ] A)) (sym $ elimTy[] (wk ⨟ ∅) A)) (π₂ᴹ idSᴹ)
            ≡⟨ tr² {P = TmᴹFamₜ} (elimTy[] wk ([ ∅ ] A)) ⟨
          tr TmᴹFamₜ (sym $ elimTy[] (wk ⨟ ∅) A)
            (tr TmᴹFamₜ (elimTy[] wk ([ ∅ ] A)) (π₂ᴹ idSᴹ))
            ∎
            where
              vzᴹ≅ : π₂ᴹ {Δᴹ = elimCtx Δ ,ᶜᴹ ([ elimSub ∅ ]ᴹ elimTy A)} {Aᴹ = [ elimSub ∅ ]ᴹ elimTy A} idSᴹ
                    ≅ π₂ᴹ {Δᴹ = elimCtx Δ ,ᶜᴹ elimTy ([ ∅ ] A)} {Aᴹ = elimTy ([ ∅ ] A)} idSᴹ
              vzᴹ≅ = hcong (λ Aᴹ → π₂ᴹ {Δᴹ = elimCtx Δ ,ᶜᴹ Aᴹ} {Aᴹ = Aᴹ} idSᴹ) (≡-to-≅ $ elimTy[] ∅ A)
  
  elimSub↑-tot {Δ} (_,_ σ {A'} t) A = ≅-to-≡ $ begin
    [ elimSub σ ,ˢᴹ tᴹ ]ᴹ elimTy A
      ,' (elimSub σ ,ˢᴹ tᴹ) ↑ᴹ elimTy A
      ≡⟨ _ ,Σ≡ ,ˢᴹ↑ᴹ {σᴹ = elimSub σ} {tᴹ = tᴹ} ⟩
    [ elimSub σ ,ˢᴹ tᴹ ]ᴹ elimTy A
      ,' (π₁ᴹ idSᴹ ⨟ᴹ (elimSub σ ,ˢᴹ tᴹ)) ,ˢᴹ tr TmᴹFamₜ (sym $ [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ)
      ≡⟨ ap₂Σ ((π₁ᴹ idSᴹ ⨟ᴹ (elimSub σ ,ˢᴹ tᴹ)) ,ˢᴹ_) (elimTy[] (σ , t) A ,Σ≡ ≅-to-≡ heq) ⟩
    elimTy ([ σ , t ] A) ,' _
      ∎
    where
      open ≅-Reasoning
      tᴹ = tr TmᴹFamₜ (sym $ elimTy[] σ A') (elimTm t)
      heq : tr (λ Aᴹ → Tmᴹ (elimCtx Δ ,ᶜᴹ Aᴹ) ([ π₁ᴹ idSᴹ ⨟ᴹ (elimSub σ ,ˢᴹ tᴹ) ]ᴹ elimTy A) vz)
               (elimTy[] (σ , t) A)
               (tr TmᴹFamₜ (sym $ [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ))
          ≅ tr TmᴹFamₜ (sym $ elimTy[] (wk ⨟ (σ , t)) A)
              (tr TmᴹFamₜ (elimTy[] wk ([ σ , t ] A)) (π₂ᴹ idSᴹ))
      heq = begin
        tr (λ Aᴹ → Tmᴹ (elimCtx Δ ,ᶜᴹ Aᴹ) ([ π₁ᴹ idSᴹ ⨟ᴹ (elimSub σ ,ˢᴹ tᴹ) ]ᴹ elimTy A) vz)
           (elimTy[] (σ , t) A)
           (tr TmᴹFamₜ (sym $ [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ))
          ≅⟨ tr≅ (λ Aᴹ → Tmᴹ (elimCtx Δ ,ᶜᴹ Aᴹ) ([ π₁ᴹ idSᴹ ⨟ᴹ (elimSub σ ,ˢᴹ tᴹ) ]ᴹ elimTy A) vz)
                 (elimTy[] (σ , t) A) _ ⟩
        tr TmᴹFamₜ (sym $ [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ)
          ≅⟨ tr≅ TmᴹFamₜ (sym $ [⨟ᴹ]ᴹ) _ ⟩
        π₂ᴹ {Aᴹ = [ elimSub (σ , t) ]ᴹ elimTy A} idSᴹ
          ≅⟨ vzᴹ≅ ⟩
        π₂ᴹ {Aᴹ = elimTy ([ σ , t ] A)} idSᴹ
          ≅⟨ tr≅ TmᴹFamₜ (trans (elimTy[] wk ([ σ , t ] A)) (sym $ elimTy[] (wk ⨟ (σ , t)) A)) _ ⟨
        tr TmᴹFamₜ (trans (elimTy[] wk ([ σ , t ] A)) (sym $ elimTy[] (wk ⨟ (σ , t)) A))
          (π₂ᴹ idSᴹ)
          ≡⟨ tr² {P = TmᴹFamₜ} (elimTy[] wk ([ σ , t ] A)) ⟨
        tr TmᴹFamₜ (sym $ elimTy[] (wk ⨟ (σ , t)) A)
          (tr TmᴹFamₜ (elimTy[] wk ([ σ , t ] A)) (π₂ᴹ idSᴹ))
          ∎
          where
            vzᴹ≅ : π₂ᴹ {Δᴹ = elimCtx Δ ,ᶜᴹ ([ elimSub (σ , t) ]ᴹ elimTy A)} {Aᴹ = [ elimSub (σ , t) ]ᴹ elimTy A} idSᴹ
                  ≅ π₂ᴹ {Δᴹ = elimCtx Δ ,ᶜᴹ elimTy ([ σ , t ] A)} {Aᴹ = elimTy ([ σ , t ] A)} idSᴹ
            vzᴹ≅ = hcong (λ Aᴹ → π₂ᴹ {Δᴹ = elimCtx Δ ,ᶜᴹ Aᴹ} {Aᴹ = Aᴹ} idSᴹ) (≡-to-≅ $ elimTy[] (σ , t) A)
      
  elimSub↑-tot {Δ} {Γ} {i} (π₁ {A = A'} idS) A = ≅-to-≡ $ begin
    [ π₁ᴹ idSᴹ ]ᴹ elimTy A ,' (π₁ᴹ idSᴹ ↑ᴹ elimTy A)
      ≡⟨ _ ,Σ≡ π₁ᴹidSᴹ↑ᴹ ⟩
    [ π₁ᴹ idSᴹ ]ᴹ elimTy A ,' (π₁ᴹ idSᴹ ⨟ᴹ π₁ᴹ idSᴹ) ,ˢᴹ tr TmᴹFamₜ (sym $ [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ)
      ≡⟨ ap₂Σ ((π₁ᴹ idSᴹ ⨟ᴹ π₁ᴹ idSᴹ) ,ˢᴹ_) (elimTy[] (π₁ idS) A ,Σ≡ ≅-to-≡ heq) ⟩
    elimTy ([ wk ] A) ,' _
      ∎
    where
      open ≅-Reasoning
      heq : tr (λ Aᴹ → Tmᴹ ((elimCtx Γ ,ᶜᴹ elimTy A') ,ᶜᴹ Aᴹ) ([ π₁ᴹ idSᴹ ⨟ᴹ π₁ᴹ idSᴹ ]ᴹ elimTy A) vz)
              (elimTy[] wk A)
              (tr TmᴹFamₜ (sym $ [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ))
         ≅ tr TmᴹFamₜ (sym $ elimTy[] (wk ⨟ π₁ {Γ , A'} idS) A)
              (tr TmᴹFamₜ (elimTy[] wk ([ wk ] A)) (π₂ᴹ idSᴹ))
      heq = begin
        tr (λ Aᴹ → Tmᴹ ((elimCtx Γ ,ᶜᴹ elimTy A') ,ᶜᴹ Aᴹ) ([ π₁ᴹ idSᴹ ⨟ᴹ π₁ᴹ idSᴹ ]ᴹ elimTy A) vz)
           (elimTy[] wk A)
           (tr TmᴹFamₜ (sym $ [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ))
          ≅⟨ tr≅ (λ Aᴹ → Tmᴹ ((elimCtx Γ ,ᶜᴹ elimTy A') ,ᶜᴹ Aᴹ) ([ π₁ᴹ idSᴹ ⨟ᴹ π₁ᴹ idSᴹ ]ᴹ elimTy A) vz)
                 (elimTy[] wk A) _ ⟩
        tr TmᴹFamₜ (sym $ [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ)
          ≅⟨ tr≅ TmᴹFamₜ (sym $ [⨟ᴹ]ᴹ) _ ⟩
        π₂ᴹ {Aᴹ = [ elimSub wk ]ᴹ elimTy A} idSᴹ
          ≅⟨ vzᴹ≅ ⟩
        π₂ᴹ {Aᴹ = elimTy ([ wk ] A)} idSᴹ
          ≅⟨ tr≅ TmᴹFamₜ (trans (elimTy[] wk ([ wk ] A)) (sym $ elimTy[] (wk ⨟ π₁ {Γ , A'} idS) A)) _ ⟨
        tr TmᴹFamₜ (trans (elimTy[] wk ([ wk ] A)) (sym $ elimTy[] (wk ⨟ π₁ idS) A))
           (π₂ᴹ idSᴹ)
          ≡⟨ tr² (elimTy[] wk ([ wk ] A)) ⟨
        tr TmᴹFamₜ (sym $ elimTy[] (wk ⨟ π₁ idS) A)
           (tr TmᴹFamₜ (elimTy[] wk ([ wk ] A)) (π₂ᴹ idSᴹ))
          ∎
        where
          vzᴹ≅ : π₂ᴹ {Δᴹ = (_ ,ᶜᴹ elimTy A') ,ᶜᴹ _} {Aᴹ = [ elimSub wk ]ᴹ elimTy A} idSᴹ
               ≅ π₂ᴹ {Δᴹ = (_ ,ᶜᴹ elimTy A') ,ᶜᴹ _} {Aᴹ = elimTy ([ wk ] A)} idSᴹ
          vzᴹ≅ = hcong (λ Aᴹ → π₂ᴹ {Aᴹ = Aᴹ} idSᴹ) (≡-to-≅ $ elimTy[] wk A)
          
  elimSub↑-tot {Δ} (π₁ (π₁ σ)) A = ≅-to-≡ $ begin
    [ π₁ᴹ (π₁ᴹ (elimSub σ)) ]ᴹ elimTy A ,' (π₁ᴹ (π₁ᴹ (elimSub σ)) ↑ᴹ elimTy A)
      ≡⟨ _ ,Σ≡ π₁ᴹπ₁ᴹ↑ᴹ {σᴹ = elimSub σ} ⟩
    [ π₁ᴹ (π₁ᴹ (elimSub σ)) ]ᴹ elimTy A ,'
      ((π₁ᴹ idSᴹ ⨟ᴹ π₁ᴹ (π₁ᴹ (elimSub σ))) ,ˢᴹ tr TmᴹFamₜ (sym [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ))
      ≡⟨ ap₂Σ ((π₁ᴹ idSᴹ ⨟ᴹ π₁ᴹ (π₁ᴹ (elimSub σ))) ,ˢᴹ_) (elimTy[] (π₁ (π₁ σ)) A ,Σ≡ ≅-to-≡ heq) ⟩
    elimTy ([ π₁ (π₁ σ) ] A) ,' _
      ∎
    where
      open ≅-Reasoning
      heq : tr (λ Aᴹ → Tmᴹ (elimCtx Δ ,ᶜᴹ Aᴹ) ([ π₁ᴹ idSᴹ ⨟ᴹ π₁ᴹ (π₁ᴹ (elimSub σ)) ]ᴹ elimTy A) vz)
               (elimTy[] (π₁ (π₁ σ)) A)
               (tr TmᴹFamₜ (sym [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ))
          ≅ tr TmᴹFamₜ (sym $ elimTy[] (wk ⨟ π₁ (π₁ σ)) A)
               (tr TmᴹFamₜ (elimTy[] wk ([ π₁ (π₁ σ) ] A)) (π₂ᴹ idSᴹ))
      heq = begin
        tr (λ Aᴹ → Tmᴹ (elimCtx Δ ,ᶜᴹ Aᴹ) ([ π₁ᴹ idSᴹ ⨟ᴹ π₁ᴹ (π₁ᴹ (elimSub σ)) ]ᴹ elimTy A) vz)
           (elimTy[] (π₁ (π₁ σ)) A)
           (tr TmᴹFamₜ (sym [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ))
          ≅⟨ tr≅ (λ Aᴹ → Tmᴹ (elimCtx Δ ,ᶜᴹ Aᴹ) ([ π₁ᴹ idSᴹ ⨟ᴹ π₁ᴹ (π₁ᴹ (elimSub σ)) ]ᴹ elimTy A) vz)
                 (elimTy[] (π₁ (π₁ σ)) A) _ ⟩
        tr TmᴹFamₜ (sym [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ)
          ≅⟨ tr≅ TmᴹFamₜ (sym [⨟ᴹ]ᴹ) _ ⟩
        π₂ᴹ {Aᴹ = [ elimSub (π₁ (π₁ σ)) ]ᴹ elimTy A} idSᴹ
          ≅⟨ vzᴹ≅ ⟩
        π₂ᴹ {Aᴹ = elimTy ([ π₁ (π₁ σ) ] A)} idSᴹ
          ≅⟨ tr≅ TmᴹFamₜ (trans (elimTy[] wk ([ π₁ (π₁ σ) ] A)) (sym $ elimTy[] (wk ⨟ π₁ (π₁ σ)) A)) _ ⟨
        tr TmᴹFamₜ _ (π₂ᴹ idSᴹ)
          ≡⟨ tr² (elimTy[] wk ([ π₁ (π₁ σ) ] A)) ⟨
        tr TmᴹFamₜ (sym $ elimTy[] (wk ⨟ π₁ (π₁ σ)) A) _
          ∎
        where
          vzᴹ≅ : π₂ᴹ {Aᴹ = [ elimSub (π₁ (π₁ σ)) ]ᴹ elimTy A} idSᴹ
               ≅ π₂ᴹ {Aᴹ = elimTy ([ π₁ (π₁ σ) ] A)} idSᴹ
          vzᴹ≅ = hcong (λ Aᴹ → π₂ᴹ {Aᴹ = Aᴹ} idSᴹ) (≡-to-≅ $ elimTy[] (π₁ (π₁ σ)) A)
