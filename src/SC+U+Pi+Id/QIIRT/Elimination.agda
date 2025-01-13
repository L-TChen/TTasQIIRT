-- Elimination of Substitution Calculus
module SC+U+Pi+Id.QIIRT.Elimination where

open import Prelude
  renaming (_,_ to _,'_)
open import SC+U+Pi+Id.QIIRT.Base
open import SC+U+Pi+Id.QIIRT.Model
open import SC+U+Pi+Id.QIIRT.Properties

module elim {ℓ ℓ′}(M : Model {ℓ} {ℓ′}) where
  open Model M
  open ≡-Reasoning

  {-# TERMINATING #-}
  ElimCtx
    : (Γ : Ctx) → Ctxᴹ Γ
  ElimTy
    : (A : Ty Γ i) → Tyᴹ (ElimCtx Γ) i A
  ElimSub
    : (σ : Sub Δ Γ) → Subᴹ (ElimCtx Δ) (ElimCtx Γ) σ
  ElimTm
    : (t : Tm Γ A) → Tmᴹ (ElimCtx Γ) (ElimTy A) t
  ElimTy[]
    : (σ : Sub Δ Γ)(A : Ty Γ i)
    → [ ElimSub σ ]ᴹ ElimTy A ≡ ElimTy ([ σ ] A)
  ElimTm[]
    : (σ : Sub Δ Γ){A : Ty Γ i}(t : Tm Γ A)
    → tr TmᴹFamₜ (ElimTy[] σ A) ([ ElimSub σ ]tᴹ ElimTm t) ≡ ElimTm ([ σ ]t t)
  
  ElimCtx ∅          = ∅ᶜᴹ
  ElimCtx (Γ , A)    = ElimCtx Γ ,ᶜᴹ ElimTy A
  ElimTy (U i)       = Uᴹ i
  ElimTy (El u) = Elᴹ (ElimTm u)
  ElimTy (Lift A) = Liftᴹ (ElimTy A)
  ElimTy (Π A B)     = Πᴹ (ElimTy A) (ElimTy B)
  ElimTy (Id a t u)      = Idᴹ (ElimTm a) (ElimTm t) (ElimTm u)
  ElimSub ∅          = ∅ˢᴹ
  ElimSub (σ , t)    = ElimSub σ ,ˢᴹ tr TmᴹFamₜ (sym $ ElimTy[] σ _) (ElimTm t)
  ElimSub idS        = idSᴹ
  ElimSub (τ ⨟ σ)    = ElimSub τ ⨟ᴹ ElimSub σ
  ElimSub (π₁ σ)     = π₁ᴹ (ElimSub σ)
  ElimTm (π₂ σ)      = tr TmᴹFamₜ (ElimTy[] (π₁ σ) _) (π₂ᴹ (ElimSub σ))
  ElimTm ([ σ ]tm t) = tr TmᴹFamₜ (ElimTy[] σ _) ([ ElimSub σ ]tmᴹ ElimTm t)
  ElimTm (c A)       = cᴹ (ElimTy A)
  ElimTm (mk t)      = mkᴹ (ElimTm t)
  ElimTm (un t)      = unᴹ (ElimTm t)
  ElimTm (ƛ t)       = (ƛᴹ ElimTm t)
  ElimTm (app t)     = appᴹ (ElimTm t)

  ElimSub↑-tot : (σ : Sub Δ Γ)(A : Ty Γ i)
               → _≡_ {A = ∃ λ PB → Subᴹ (ElimCtx Δ ,ᶜᴹ PB) (ElimCtx Γ ,ᶜᴹ ElimTy A) (σ ↑ A)}
                     ([ ElimSub σ ]ᴹ ElimTy A ,' ElimSub σ ↑ᴹ ElimTy A)
                     (ElimTy ([ σ ] A) ,' ElimSub (σ ↑ A))

  ElimTy[] σ (U i) = []ᴹUᴹ
  ElimTy[] σ (El u) = begin
    [ ElimSub σ ]ᴹ ElimTy (El u)
      ≡⟨ []ᴹElᴹ (ElimSub σ) (ElimTm u) ⟩
    Elᴹ (tr TmᴹFamₜ []ᴹUᴹ ([ ElimSub σ ]tᴹ ElimTm u))
      ≡⟨ cong Elᴹ (ElimTm[] σ u) ⟩
    Elᴹ (ElimTm ([ σ ]t u))
      ∎
  ElimTy[] σ (Lift A) = begin
    [ ElimSub σ ]ᴹ Liftᴹ (ElimTy A)
      ≡⟨ []ᴹLiftᴹ ⟩
    Liftᴹ ([ ElimSub σ ]ᴹ ElimTy A)
      ≡⟨ cong Liftᴹ (ElimTy[] σ A) ⟩
    Liftᴹ (ElimTy ([ σ ] A))
      ∎
  ElimTy[] {Δ} {Γ} {i} σ (Π A B) =
      begin
    [ ElimSub σ ]ᴹ Πᴹ (ElimTy A) (ElimTy B)
      ≡⟨ []ᴹΠᴹ ⟩
    Πᴹ ([ ElimSub σ ]ᴹ ElimTy A) ([ ElimSub σ ↑ᴹ ElimTy A ]ᴹ ElimTy B)
      ≡⟨ cong (uncurry Πᴹ) eq ⟩
    Πᴹ (ElimTy ([ σ ] A)) (ElimTy ([ σ ↑ A ] B))
      ∎
    where
      eq : _≡_ {A = ∃ λ PB → Tyᴹ (ElimCtx Δ ,ᶜᴹ PB) i ([ σ ↑ A ] B)}
                ([ ElimSub σ ]ᴹ ElimTy A ,' [ ElimSub σ ↑ᴹ ElimTy A ]ᴹ ElimTy B)
                (ElimTy ([ σ ] A) ,' ElimTy ([ σ ↑ A ] B))
      eq = begin
        [ ElimSub σ ]ᴹ ElimTy A ,' [ ElimSub σ ↑ᴹ ElimTy A ]ᴹ ElimTy B
          ≡⟨ ap₂Σ ([_]ᴹ ElimTy B) (ElimSub↑-tot σ A) ⟩
        ElimTy ([ σ ] A) ,' ([ ElimSub (σ ↑ A) ]ᴹ ElimTy B)
          ≡⟨ cong (ElimTy ([ σ ] A) ,'_) (ElimTy[] (σ ↑ A) B) ⟩
        ElimTy ([ σ ] A) ,' ElimTy ([ σ ↑ A ] B)
          ∎
      {-
      eq : tr (λ PB → Tyᴹ (ElimCtx Δ ,ᶜᴹ PB) i ([ σ ↑ A ] B))
               (ElimTy[] σ A)
               ([ ElimSub σ ↑ᴹ ElimTy A ]ᴹ ElimTy B)
          ≡ ElimTy ([ σ ↑ A ] B)
      eq = begin
        tr (λ PB → Tyᴹ (ElimCtx Δ ,ᶜᴹ PB) i ([ σ ↑ A ] B))
           (ElimTy[] σ A)
           ([ ElimSub σ ↑ᴹ ElimTy A ]ᴹ ElimTy B)
          ≡⟨ tr-nat (λ PB → Subᴹ (ElimCtx Δ ,ᶜᴹ PB) (ElimCtx Γ ,ᶜᴹ ElimTy A) (σ ↑ A))
                    (λ _ Pσ → [ Pσ ]ᴹ ElimTy B)
                    (ElimTy[] σ A) ⟩
        [ tr (λ PB → Subᴹ (ElimCtx Δ ,ᶜᴹ PB) (ElimCtx Γ ,ᶜᴹ ElimTy A) (σ ↑ A))
             (ElimTy[] σ A)
             (ElimSub σ ↑ᴹ ElimTy A) ]ᴹ ElimTy B
          ≡⟨ cong ([_]ᴹ ElimTy B) (ElimSub↑ σ A) ⟩
        [ ElimSub (σ ↑ A) ]ᴹ ElimTy B
          ≡⟨ ElimTy[] (σ ↑ A) B ⟩
        ElimTy ([ σ ↑ A ] B)
          ∎
      -}
  ElimTy[] {Δ} {Γ} {i} σ (Id a t u) = begin
    [ ElimSub σ ]ᴹ Idᴹ (ElimTm a) (ElimTm t) (ElimTm u)
      ≡⟨ []ᴹIdᴹ ⟩
    Idᴹ tr[Eσ]Ea tr[Eσ]Et tr[Eσ]Eu
      ≡⟨ cong₃ Idᴹ eqa eqt equ ⟩
    Idᴹ (ElimTm ([ σ ]t a)) (ElimTm ([ σ ]t t)) (ElimTm ([ σ ]t u))
      ∎
      where
        tr[Eσ]Ea = tr TmᴹFamₜ []ᴹUᴹ ([ ElimSub σ ]tᴹ ElimTm a)
        tr[Eσ]Et = tr TmᴹFamₜ ([]ᴹElᴹ (ElimSub σ) (ElimTm a)) ([ ElimSub σ ]tᴹ ElimTm t)
        tr[Eσ]Eu = tr TmᴹFamₜ ([]ᴹElᴹ (ElimSub σ) (ElimTm a)) ([ ElimSub σ ]tᴹ ElimTm u)

        eqa : tr[Eσ]Ea ≡ ElimTm ([ σ ]t a)
        eqa = ElimTm[] σ a

        eqt : tr (λ Pa → TmᴹFamₜ (Elᴹ Pa)) eqa tr[Eσ]Et ≡ ElimTm ([ σ ]t t)
        eqt = begin
          tr (λ Pa → TmᴹFamₜ (Elᴹ Pa)) eqa tr[Eσ]Et
            ≡⟨ tr-cong eqa ⟩
          tr TmᴹFamₜ (cong Elᴹ eqa) tr[Eσ]Et
            ≡⟨ tr² ([]ᴹElᴹ (ElimSub σ) (ElimTm a)) {cong Elᴹ eqa} ⟩
          tr TmᴹFamₜ (trans ([]ᴹElᴹ (ElimSub σ) (ElimTm a)) (cong Elᴹ eqa)) ([ ElimSub σ ]tᴹ ElimTm t)
            ≡⟨ cong (λ p → tr TmᴹFamₜ p ([ ElimSub σ ]tᴹ ElimTm t)) 
                    (uip (trans ([]ᴹElᴹ (ElimSub σ) (ElimTm a)) (cong Elᴹ eqa))
                         (ElimTy[] σ (El a))) ⟩
          tr TmᴹFamₜ (ElimTy[] σ (El a)) ([ ElimSub σ ]tᴹ ElimTm t)
            ≡⟨ ElimTm[] σ t ⟩
          ElimTm ([ σ ]t t)
            ∎

        equ : tr (λ Pa → TmᴹFamₜ (Elᴹ Pa)) eqa tr[Eσ]Eu ≡ ElimTm ([ σ ]t u)
        equ = begin
          tr (λ Pa → TmᴹFamₜ (Elᴹ Pa)) eqa tr[Eσ]Eu
            ≡⟨ tr-cong eqa ⟩
          tr TmᴹFamₜ (cong Elᴹ eqa) tr[Eσ]Eu
            ≡⟨ tr² ([]ᴹElᴹ (ElimSub σ) (ElimTm a)) {cong Elᴹ eqa} ⟩
          tr TmᴹFamₜ (trans ([]ᴹElᴹ (ElimSub σ) (ElimTm a)) (cong Elᴹ eqa)) ([ ElimSub σ ]tᴹ ElimTm u)
            ≡⟨ cong (λ p → tr TmᴹFamₜ p ([ ElimSub σ ]tᴹ ElimTm u)) 
                    (uip (trans ([]ᴹElᴹ (ElimSub σ) (ElimTm a)) (cong Elᴹ eqa))
                         (ElimTy[] σ (El a))) ⟩
          tr TmᴹFamₜ (ElimTy[] σ (El a)) ([ ElimSub σ ]tᴹ ElimTm u)
            ≡⟨ ElimTm[] σ u ⟩
          ElimTm ([ σ ]t u)
            ∎

  ElimTm[] idS {A} t = begin
    tr TmᴹFamₜ (ElimTy[] idS A) ([ ElimSub idS ]tᴹ ElimTm t)
      ≡⟨ cong (λ p → tr TmᴹFamₜ p ([ ElimSub idS ]tᴹ ElimTm t)) (uip _ [idSᴹ]) ⟩
    tr TmᴹFamₜ [idSᴹ] ([ ElimSub idS ]tᴹ ElimTm t)
      ≡⟨ [idSᴹ]tᴹ ⟩
    ElimTm t
      ∎
  ElimTm[] (τ ⨟ σ) {A} t = begin
    tr TmᴹFamₜ (ElimTy[] (τ ⨟ σ) A) ([ ElimSub τ ⨟ᴹ ElimSub σ ]tᴹ ElimTm t)
      ≡⟨ cong (λ p → tr TmᴹFamₜ p ([ ElimSub τ ⨟ᴹ ElimSub σ ]tᴹ ElimTm t)) (uip _ (trans [⨟ᴹ]ᴹ eq)) ⟩
    tr TmᴹFamₜ (trans [⨟ᴹ]ᴹ eq) ([ ElimSub τ ⨟ᴹ ElimSub σ ]tᴹ ElimTm t)
      ≡⟨ tr² [⨟ᴹ]ᴹ ⟨
    tr TmᴹFamₜ eq (tr TmᴹFamₜ [⨟ᴹ]ᴹ ([ ElimSub τ ⨟ᴹ ElimSub σ ]tᴹ ElimTm t))
      ≡⟨ cong (tr TmᴹFamₜ eq) [⨟ᴹ]tᴹ ⟩
    tr TmᴹFamₜ eq ([ ElimSub τ ]tᴹ ([ ElimSub σ ]tᴹ ElimTm t))
      ≡⟨ tr² (cong ([ ElimSub τ ]ᴹ_) (ElimTy[] σ A)) ⟨
    tr TmᴹFamₜ (ElimTy[] τ _)
      (tr TmᴹFamₜ (cong ([ ElimSub τ ]ᴹ_) (ElimTy[] σ A))
         ([ ElimSub τ ]tᴹ ([ ElimSub σ ]tᴹ ElimTm t)))
      ≡⟨ cong (tr TmᴹFamₜ (ElimTy[] τ ([ σ ] A)))
              (tr-cong {P = TmᴹFamₜ} (ElimTy[] σ A)) ⟨
    tr TmᴹFamₜ (ElimTy[] τ _) (tr (λ Aᴹ → TmᴹFamₜ ([ ElimSub τ ]ᴹ Aᴹ)) (ElimTy[] σ A)
                                  ([ ElimSub τ ]tᴹ ([ ElimSub σ ]tᴹ ElimTm t)))
      ≡⟨ cong (tr TmᴹFamₜ (ElimTy[] τ ([ σ ] A)))
              (tr-nat TmᴹFamₜ (λ _ tᴹ → [ ElimSub τ ]tᴹ tᴹ) (ElimTy[] σ A)) ⟩
    tr TmᴹFamₜ (ElimTy[] τ _) ([ ElimSub τ ]tᴹ tr TmᴹFamₜ (ElimTy[] σ A) ([ ElimSub σ ]tᴹ ElimTm t))
      ≡⟨ cong (λ tᴹ → tr TmᴹFamₜ (ElimTy[] τ _) ([ ElimSub τ ]tᴹ tᴹ))
              (ElimTm[] σ t) ⟩
    tr TmᴹFamₜ (ElimTy[] τ _) ([ ElimSub τ ]tᴹ ElimTm ([ σ ]t t))
      ≡⟨ ElimTm[] τ ([ σ ]t t) ⟩
    ElimTm ([ τ ]t [ σ ]t t)
      ∎
    where
      eq : [ ElimSub τ ]ᴹ ([ ElimSub σ ]ᴹ ElimTy A) ≡ ElimTy ([ τ ] [ σ ] A)
      eq = trans (cong ([ ElimSub τ ]ᴹ_) (ElimTy[] σ A)) (ElimTy[] τ _)

  ElimTm[] (π₁ (σ , u))  {A} t = begin
    tr TmᴹFamₜ (ElimTy[] (π₁ (σ , u)) A) ([ π₁ᴹ (ElimSub σ ,ˢᴹ _) ]tᴹ ElimTm t)
      ≡⟨ cong (λ p → tr TmᴹFamₜ p ([ π₁ᴹ (ElimSub σ ,ˢᴹ _) ]tᴹ ElimTm t))
              (uip _ (trans [π₁ᴹ,ˢᴹ]ᴹ (ElimTy[] σ A))) ⟩
    tr TmᴹFamₜ (trans [π₁ᴹ,ˢᴹ]ᴹ (ElimTy[] σ A)) ([ π₁ᴹ (ElimSub σ ,ˢᴹ _) ]tᴹ ElimTm t)
      ≡⟨ tr² {P = TmᴹFamₜ} [π₁ᴹ,ˢᴹ]ᴹ ⟨
    tr TmᴹFamₜ (ElimTy[] σ A)
       (tr TmᴹFamₜ [π₁ᴹ,ˢᴹ]ᴹ ([ π₁ᴹ (ElimSub σ ,ˢᴹ _) ]tᴹ ElimTm t))
      ≡⟨ cong (tr TmᴹFamₜ (ElimTy[] σ A)) [π₁ᴹ,ˢᴹ]tᴹ ⟩
    tr TmᴹFamₜ (ElimTy[] σ A) ([ ElimSub σ ]tᴹ ElimTm t)
      ≡⟨ ElimTm[] σ t ⟩
    ElimTm ([ σ ]t t)
      ∎
  ElimTm[] (π₁ (σ ⨟ τ))  {A} t = begin
    tr TmᴹFamₜ (ElimTy[] (π₁ (σ ⨟ τ)) A)
          ([ π₁ᴹ (ElimSub σ ⨟ᴹ ElimSub τ) ]tᴹ ElimTm t)
      ≡⟨ cong (λ p → tr TmᴹFamₜ p ([ π₁ᴹ (ElimSub σ ⨟ᴹ ElimSub τ) ]tᴹ ElimTm t))
              (uip _ (trans [π₁ᴹ⨟ᴹ]ᴹ eq)) ⟩
    tr TmᴹFamₜ (trans [π₁ᴹ⨟ᴹ]ᴹ eq) ([ π₁ᴹ (ElimSub σ ⨟ᴹ ElimSub τ) ]tᴹ ElimTm t)
      ≡⟨ tr² {P = TmᴹFamₜ} [π₁ᴹ⨟ᴹ]ᴹ ⟨
    tr TmᴹFamₜ eq (tr TmᴹFamₜ [π₁ᴹ⨟ᴹ]ᴹ ([ π₁ᴹ (ElimSub σ ⨟ᴹ ElimSub τ) ]tᴹ ElimTm t))
      ≡⟨ cong (tr TmᴹFamₜ eq) [π₁ᴹ⨟ᴹ]tᴹ ⟩
    tr TmᴹFamₜ eq ([ ElimSub σ ]tᴹ ([ π₁ᴹ (ElimSub τ) ]tᴹ ElimTm t))
      ≡⟨ tr² {P = TmᴹFamₜ} (cong ([ ElimSub σ ]ᴹ_) (ElimTy[] (π₁ τ) A)) ⟨
    tr TmᴹFamₜ (ElimTy[] σ ([ π₁ τ ] A))
       (tr TmᴹFamₜ (cong ([ ElimSub σ ]ᴹ_) (ElimTy[] (π₁ τ) A)) _)
      ≡⟨ cong (tr TmᴹFamₜ (ElimTy[] σ ([ π₁ τ ] A)))
              (tr-cong {P = TmᴹFamₜ} (ElimTy[] (π₁ τ) A)) ⟨
    tr TmᴹFamₜ (ElimTy[] σ ([ π₁ τ ] A))
       (tr (λ Aᴹ → TmᴹFamₜ ([ ElimSub σ ]ᴹ Aᴹ)) (ElimTy[] (π₁ τ) A) _)
      ≡⟨ cong (tr TmᴹFamₜ (ElimTy[] σ ([ π₁ τ ] A)))
              (tr-nat TmᴹFamₜ (λ _ tᴹ → [ ElimSub σ ]tᴹ tᴹ) (ElimTy[] (π₁ τ) A)) ⟩
    tr TmᴹFamₜ (ElimTy[] σ ([ π₁ τ ] A))
       ([ ElimSub σ ]tᴹ tr TmᴹFamₜ (ElimTy[] (π₁ τ) A) ([ ElimSub (π₁ τ) ]tᴹ ElimTm t))
      ≡⟨ cong (λ tᴹ → tr TmᴹFamₜ (ElimTy[] σ ([ π₁ τ ] A)) ([ ElimSub σ ]tᴹ tᴹ))
              (ElimTm[] (π₁ τ)t) ⟩
    tr TmᴹFamₜ (ElimTy[] σ ([ π₁ τ ] A)) ([ ElimSub σ ]tᴹ ElimTm ([ π₁ τ ]t t))
      ≡⟨ ElimTm[] σ ([ π₁ τ ]t t) ⟩
    ElimTm ([ σ ]t [ π₁ τ ]t t)
      ∎
    where
      eq : [ ElimSub σ ]ᴹ ([ π₁ᴹ (ElimSub τ) ]ᴹ ElimTy A) ≡ ElimTy ([ σ ] [ π₁ τ ] A)
      eq = trans (cong ([ ElimSub σ ]ᴹ_) (ElimTy[] (π₁ τ) A)) (ElimTy[] σ ([ π₁ τ ] A))
  
  ElimTm[]  ∅            {A} t = cong (tr TmᴹFamₜ (ElimTy[] ∅ A)) [∅ˢᴹ]tᴹ
  ElimTm[] (σ , u)       {A} t = cong (tr TmᴹFamₜ (ElimTy[] (σ , u) A)) [,ˢᴹ]tᴹ
  ElimTm[] (π₁ idS)      {A} t = cong (tr TmᴹFamₜ (ElimTy[] (π₁ idS) A)) [π₁ᴹidSᴹ]tᴹ
  ElimTm[] (π₁ (π₁ σ))   {A} t = cong (tr TmᴹFamₜ (ElimTy[] (π₁ (π₁ σ)) A)) [π₁ᴹπ₁ᴹ]tᴹ
 
  ElimSub↑-tot ∅ A = {!   !}
  ElimSub↑-tot (σ , t) A = {!   !}
  ElimSub↑-tot idS A = {!   !}
  ElimSub↑-tot (σ ⨟ σ₁) A = {!   !}
  ElimSub↑-tot (π₁ σ) A = {!   !}