-- Elimination of Substitution Calculus
module SC+U+Pi+Id.QIIRT.Recursion where

open import Prelude
  renaming (_,_ to _,'_)
open import SC+U+Pi+Id.QIIRT.Syntax
open import SC+U+Pi+Id.QIIRT.Recursion.Motive
open import SC+U+Pi+Id.QIIRT.Recursion.Method
open import SC+U+Pi+Id.QIIRT.Properties

record Recursor {ℓ ℓ′} : Set (lsuc (ℓ ⊔ ℓ′)) where
  field
    Mot : Motive {ℓ} {ℓ′}
    Met : Method Mot
  
  open Motive Mot public
  open Method Met public

module rec {ℓ ℓ′}(M : Recursor {ℓ} {ℓ′}) where
  open Recursor M

  {-# TERMINATING #-}
  recCtx
    : Ctx → Ctxᴹ
  recTy
    : Ty Γ i → Tyᴹ (recCtx Γ) i
  recSub
    : Sub Γ Δ → Subᴹ (recCtx Γ) (recCtx Δ)
  recTm
    : Tm Γ A → Tmᴹ (recCtx Γ) (recTy A)
  postulate -- already proved in Elimination
    recTy[]
      : (σ : Sub Γ Δ) (A : Ty Δ i)
      → [ recSub σ ]ᴹ recTy A ≡ recTy ([ σ ] A)
    recTm[]
      : (σ : Sub Γ Δ) {A : Ty Δ i}(t : Tm Δ A)
      → tr TmᴹFamₜ (recTy[] σ A) ([ recSub σ ]tᴹ recTm t) ≡ recTm ([ σ ]t t)
  
  recCtx ∅          = ∅ᶜᴹ
  recCtx (Γ , A)    = recCtx Γ ,ᶜᴹ recTy A
  recTy (U i)       = Uᴹ i
  recTy (El u)      = Elᴹ (recTm u)
  recTy (Lift A)    = Liftᴹ (recTy A)
  recTy (Π A B)     = Πᴹ (recTy A) (recTy B)
  recTy (Id a t u)  = Idᴹ (recTm a) (recTm t) (recTm u)
  recSub ∅          = ∅ˢᴹ
  recSub (_,_ σ {A} t) = recSub σ ,ˢᴹ tr (Tmᴹ _) (sym $ recTy[] σ A) (recTm t)
  recSub idS        = idSᴹ
  recSub (τ ⨟ σ)    = recSub τ ⨟ᴹ recSub σ
  recSub (π₁ σ)     = π₁ᴹ (recSub σ)
  recTm (π₂ {A = A} σ) = tr TmᴹFamₜ (recTy[] (π₁ σ) A) (π₂ᴹ (recSub σ))
  recTm ([_]tm_ σ {A} t) = tr TmᴹFamₜ (recTy[] σ A) ([ recSub σ ]tmᴹ recTm t)
  recTm (c A)       = cᴹ (recTy A)
  recTm (mk t)      = mkᴹ (recTm t)
  recTm (un t)      = unᴹ (recTm t)
  recTm (ƛ t)       = (ƛᴹ recTm t)
  recTm (app t)     = appᴹ (recTm t)

  postulate
    recSub↑-tot
      : (σ : Sub Γ Δ) (A : Ty Δ i)
      → _≡_ {A = ∃ λ PB → Subᴹ (recCtx Γ ,ᶜᴹ PB) (_,ᶜᴹ_ (recCtx Δ) (recTy {Δ} A))}
        ([ recSub σ ]ᴹ recTy A ,' recSub σ ↑ᴹ recTy {Δ} A)
        (recTy {Γ} ([ σ ] A) ,' recSub (σ ↑ A))

  -- recTy[] σ (U i) = []ᴹUᴹ
  -- recTy[] σ (El u) = begin
  --   [ recSub σ ]ᴹ recTy (El u)
  --     ≡⟨ []ᴹElᴹ (recSub σ) (recTm u) ⟩
  --   Elᴹ (tr TmᴹFamₜ []ᴹUᴹ ([ recSub σ ]tᴹ recTm u))
  --     ≡⟨ cong Elᴹ (recTm[] σ u) ⟩
  --   Elᴹ (recTm ([ σ ]t u))
  --     ∎
  --   where open ≡-Reasoning
  -- recTy[] σ (Lift A) = begin
  --   [ recSub σ ]ᴹ Liftᴹ (recTy A)
  --     ≡⟨ []ᴹLiftᴹ ⟩
  --   Liftᴹ ([ recSub σ ]ᴹ recTy A)
  --     ≡⟨ cong Liftᴹ (recTy[] σ A) ⟩
  --   Liftᴹ (recTy ([ σ ] A))
  --     ∎
  --   where open ≡-Reasoning
  -- recTy[] {Δ} {Γ} {i} σ (Π A B) =
  --     begin
  --   [ recSub σ ]ᴹ Πᴹ (recTy A) (recTy B)
  --     ≡⟨ []ᴹΠᴹ ⟩
  --   Πᴹ ([ recSub σ ]ᴹ recTy A) ([ recSub σ ↑ᴹ recTy A ]ᴹ recTy B)
  --     ≡⟨ cong (uncurry Πᴹ) eq ⟩
  --   Πᴹ (recTy ([ σ ] A)) (recTy ([ σ ↑ A ] B))
  --     ∎
  --   where
  --     open ≡-Reasoning
  --     eq : _≡_ {A = ∃ λ PB → Tyᴹ (recCtx Δ ,ᶜᴹ PB) i}
  --               ([ recSub σ ]ᴹ recTy A ,' [ recSub σ ↑ᴹ recTy A ]ᴹ recTy B)
  --               (recTy ([ σ ] A) ,' recTy ([ σ ↑ A ] B))
  --     eq = begin
  --       [ recSub σ ]ᴹ recTy A ,' [ recSub σ ↑ᴹ recTy A ]ᴹ recTy B
  --         ≡⟨ ap₂Σ ([_]ᴹ recTy B) (recSub↑-tot σ A) ⟩
  --       recTy ([ σ ] A) ,' ([ recSub (σ ↑ A) ]ᴹ recTy B)
  --         ≡⟨ cong (recTy ([ σ ] A) ,'_) (recTy[] (σ ↑ A) B) ⟩
  --       recTy ([ σ ] A) ,' recTy ([ σ ↑ A ] B)
  --         ∎
  -- recTy[] {Δ} {Γ} {i} σ (Id a t u) = begin
  --   [ recSub σ ]ᴹ Idᴹ (recTm a) (recTm t) (recTm u)
  --     ≡⟨ []ᴹIdᴹ ⟩
  --   Idᴹ tr[Eσ]Ea tr[Eσ]Et tr[Eσ]Eu
  --     ≡⟨ cong₃ Idᴹ eqa eqt equ ⟩
  --   Idᴹ (recTm ([ σ ]t a)) (recTm ([ σ ]t t)) (recTm ([ σ ]t u))
  --     ∎
  --     where
  --       open ≡-Reasoning
  --       tr[Eσ]Ea = tr TmᴹFamₜ []ᴹUᴹ ([ recSub σ ]tᴹ recTm a)
  --       tr[Eσ]Et = tr TmᴹFamₜ ([]ᴹElᴹ (recSub σ) (recTm a)) ([ recSub σ ]tᴹ recTm t)
  --       tr[Eσ]Eu = tr TmᴹFamₜ ([]ᴹElᴹ (recSub σ) (recTm a)) ([ recSub σ ]tᴹ recTm u)

  --       eqa : tr[Eσ]Ea ≡ recTm ([ σ ]t a)
  --       eqa = recTm[] σ a

  --       eqt : tr (λ Pa → TmᴹFamₜ (Elᴹ Pa)) eqa tr[Eσ]Et ≡ recTm ([ σ ]t t)
  --       eqt = begin
  --         tr (λ Pa → TmᴹFamₜ (Elᴹ Pa)) eqa tr[Eσ]Et
  --           ≡⟨ tr-cong eqa ⟩
  --         tr TmᴹFamₜ (cong Elᴹ eqa) tr[Eσ]Et
  --           ≡⟨ tr² ([]ᴹElᴹ (recSub σ) (recTm a)) {cong Elᴹ eqa} ⟩
  --         tr TmᴹFamₜ (trans ([]ᴹElᴹ (recSub σ) (recTm a)) (cong Elᴹ eqa)) ([ recSub σ ]tᴹ recTm t)
  --           ≡⟨ cong (λ p → tr TmᴹFamₜ p ([ recSub σ ]tᴹ recTm t)) 
  --                   (uip (trans ([]ᴹElᴹ (recSub σ) (recTm a)) (cong Elᴹ eqa))
  --                        (recTy[] σ (El a))) ⟩
  --         tr TmᴹFamₜ (recTy[] σ (El a)) ([ recSub σ ]tᴹ recTm t)
  --           ≡⟨ recTm[] σ t ⟩
  --         recTm ([ σ ]t t)
  --           ∎

  --       equ : tr (λ Pa → TmᴹFamₜ (Elᴹ Pa)) eqa tr[Eσ]Eu ≡ recTm ([ σ ]t u)
  --       equ = begin
  --         tr (λ Pa → TmᴹFamₜ (Elᴹ Pa)) eqa tr[Eσ]Eu
  --           ≡⟨ tr-cong eqa ⟩
  --         tr TmᴹFamₜ (cong Elᴹ eqa) tr[Eσ]Eu
  --           ≡⟨ tr² ([]ᴹElᴹ (recSub σ) (recTm a)) {cong Elᴹ eqa} ⟩
  --         tr TmᴹFamₜ (trans ([]ᴹElᴹ (recSub σ) (recTm a)) (cong Elᴹ eqa)) ([ recSub σ ]tᴹ recTm u)
  --           ≡⟨ cong (λ p → tr TmᴹFamₜ p ([ recSub σ ]tᴹ recTm u)) 
  --                   (uip (trans ([]ᴹElᴹ (recSub σ) (recTm a)) (cong Elᴹ eqa))
  --                        (recTy[] σ (El a))) ⟩
  --         tr TmᴹFamₜ (recTy[] σ (El a)) ([ recSub σ ]tᴹ recTm u)
  --           ≡⟨ recTm[] σ u ⟩
  --         recTm ([ σ ]t u)
  --           ∎

  -- recTm[] idS {A} t = begin
  --   tr TmᴹFamₜ (recTy[] idS A) ([ idSᴹ ]tᴹ recTm t)
  --     ≡⟨ cong (λ p → tr TmᴹFamₜ p ([ idSᴹ ]tᴹ recTm t)) (uip _ [idSᴹ]) ⟩
  --   tr TmᴹFamₜ [idSᴹ] ([ idSᴹ ]tᴹ recTm t)
  --     ≡⟨ [idSᴹ]tᴹ ⟩
  --   recTm t
  --     ∎
  --   where open ≡-Reasoning
  -- recTm[] (τ ⨟ σ) {A} t = begin
  --   tr TmᴹFamₜ (recTy[] (τ ⨟ σ) A) ([ recSub τ ⨟ᴹ recSub σ ]tᴹ recTm t)
  --     ≡⟨ cong (λ p → tr TmᴹFamₜ p ([ recSub τ ⨟ᴹ recSub σ ]tᴹ recTm t)) (uip _ (trans [⨟ᴹ]ᴹ eq)) ⟩
  --   tr TmᴹFamₜ (trans [⨟ᴹ]ᴹ eq) ([ recSub τ ⨟ᴹ recSub σ ]tᴹ recTm t)
  --     ≡⟨ tr² [⨟ᴹ]ᴹ ⟨
  --   tr TmᴹFamₜ eq (tr TmᴹFamₜ [⨟ᴹ]ᴹ ([ recSub τ ⨟ᴹ recSub σ ]tᴹ recTm t))
  --     ≡⟨ cong (tr TmᴹFamₜ eq) [⨟ᴹ]tᴹ ⟩
  --   tr TmᴹFamₜ eq ([ recSub τ ]tᴹ ([ recSub σ ]tᴹ recTm t))
  --     ≡⟨ tr² (cong ([ recSub τ ]ᴹ_) (recTy[] σ A)) ⟨
  --   tr TmᴹFamₜ (recTy[] τ ([ σ ] A))
  --     (tr TmᴹFamₜ (cong ([ recSub τ ]ᴹ_) (recTy[] σ A))
  --        ([ recSub τ ]tᴹ ([ recSub σ ]tᴹ recTm t)))
  --     ≡⟨ cong (tr TmᴹFamₜ (recTy[] τ ([ σ ] A)))
  --             (tr-cong {P = TmᴹFamₜ} (recTy[] σ A)) ⟨
  --   tr TmᴹFamₜ (recTy[] τ ([ σ ] A)) (tr (λ Aᴹ → TmᴹFamₜ ([ recSub τ ]ᴹ Aᴹ)) (recTy[] σ A)
  --                                 ([ recSub τ ]tᴹ ([ recSub σ ]tᴹ recTm t)))
  --     ≡⟨ cong (tr TmᴹFamₜ (recTy[] τ ([ σ ] A)))
  --             (tr-nat TmᴹFamₜ (λ _ tᴹ → [ recSub τ ]tᴹ tᴹ) (recTy[] σ A)) ⟩
  --   tr TmᴹFamₜ (recTy[] τ ([ σ ] A)) ([ recSub τ ]tᴹ tr TmᴹFamₜ (recTy[] σ A) ([ recSub σ ]tᴹ recTm t))
  --     ≡⟨ cong (λ tᴹ → tr TmᴹFamₜ (recTy[] τ ([ σ ] A)) ([ recSub τ ]tᴹ tᴹ))
  --             (recTm[] σ t) ⟩
  --   tr TmᴹFamₜ (recTy[] τ ([ σ ] A)) ([ recSub τ ]tᴹ recTm ([ σ ]t t))
  --     ≡⟨ recTm[] τ ([ σ ]t t) ⟩
  --   recTm ([ τ ]t [ σ ]t t)
  --     ∎
  --   where
  --     open ≡-Reasoning
  --     eq : [ recSub τ ]ᴹ ([ recSub σ ]ᴹ recTy A) ≡ recTy ([ τ ] [ σ ] A)
  --     eq = trans (cong ([ recSub τ ]ᴹ_) (recTy[] σ A)) (recTy[] τ ([ σ ] A))

  -- recTm[] (π₁ (σ , u))  {A} t = begin
  --   tr TmᴹFamₜ (recTy[] (π₁ (σ , u)) A) ([ π₁ᴹ (recSub σ ,ˢᴹ _) ]tᴹ recTm t)
  --     ≡⟨ cong (λ p → tr TmᴹFamₜ p ([ π₁ᴹ (recSub σ ,ˢᴹ _) ]tᴹ recTm t))
  --             (uip _ (trans [π₁ᴹ,ˢᴹ]ᴹ (recTy[] σ A))) ⟩
  --   tr TmᴹFamₜ (trans [π₁ᴹ,ˢᴹ]ᴹ (recTy[] σ A)) ([ π₁ᴹ (recSub σ ,ˢᴹ _) ]tᴹ recTm t)
  --     ≡⟨ tr² {P = TmᴹFamₜ} [π₁ᴹ,ˢᴹ]ᴹ ⟨
  --   tr TmᴹFamₜ (recTy[] σ A)
  --      (tr TmᴹFamₜ [π₁ᴹ,ˢᴹ]ᴹ ([ π₁ᴹ (recSub σ ,ˢᴹ _) ]tᴹ recTm t))
  --     ≡⟨ cong (tr TmᴹFamₜ (recTy[] σ A)) [π₁ᴹ,ˢᴹ]tᴹ ⟩
  --   tr TmᴹFamₜ (recTy[] σ A) ([ recSub σ ]tᴹ recTm t)
  --     ≡⟨ recTm[] σ t ⟩
  --   recTm ([ σ ]t t)
  --     ∎
  --   where open ≡-Reasoning
  -- recTm[] (π₁ (σ ⨟ τ))  {A} t = begin
  --   tr TmᴹFamₜ (recTy[] (π₁ (σ ⨟ τ)) A)
  --         ([ π₁ᴹ (recSub σ ⨟ᴹ recSub τ) ]tᴹ recTm t)
  --     ≡⟨ cong (λ p → tr TmᴹFamₜ p ([ π₁ᴹ (recSub σ ⨟ᴹ recSub τ) ]tᴹ recTm t))
  --             (uip _ (trans [π₁ᴹ⨟ᴹ]ᴹ eq)) ⟩
  --   tr TmᴹFamₜ (trans [π₁ᴹ⨟ᴹ]ᴹ eq) ([ π₁ᴹ (recSub σ ⨟ᴹ recSub τ) ]tᴹ recTm t)
  --     ≡⟨ tr² {P = TmᴹFamₜ} [π₁ᴹ⨟ᴹ]ᴹ ⟨
  --   tr TmᴹFamₜ eq (tr TmᴹFamₜ [π₁ᴹ⨟ᴹ]ᴹ ([ π₁ᴹ (recSub σ ⨟ᴹ recSub τ) ]tᴹ recTm t))
  --     ≡⟨ cong (tr TmᴹFamₜ eq) [π₁ᴹ⨟ᴹ]tᴹ ⟩
  --   tr TmᴹFamₜ eq ([ recSub σ ]tᴹ ([ π₁ᴹ (recSub τ) ]tᴹ recTm t))
  --     ≡⟨ tr² {P = TmᴹFamₜ} (cong ([ recSub σ ]ᴹ_) (recTy[] (π₁ τ) A)) ⟨
  --   tr TmᴹFamₜ (recTy[] σ ([ π₁ τ ] A))
  --      (tr TmᴹFamₜ (cong ([ recSub σ ]ᴹ_) (recTy[] (π₁ τ) A)) _)
  --     ≡⟨ cong (tr TmᴹFamₜ (recTy[] σ ([ π₁ τ ] A)))
  --             (tr-cong {P = TmᴹFamₜ} (recTy[] (π₁ τ) A)) ⟨
  --   tr TmᴹFamₜ (recTy[] σ ([ π₁ τ ] A))
  --      (tr (λ Aᴹ → TmᴹFamₜ ([ recSub σ ]ᴹ Aᴹ)) (recTy[] (π₁ τ) A) _)
  --     ≡⟨ cong (tr TmᴹFamₜ (recTy[] σ ([ π₁ τ ] A)))
  --             (tr-nat TmᴹFamₜ (λ _ tᴹ → [ recSub σ ]tᴹ tᴹ) (recTy[] (π₁ τ) A)) ⟩
  --   tr TmᴹFamₜ (recTy[] σ ([ π₁ τ ] A))
  --      ([ recSub σ ]tᴹ tr TmᴹFamₜ (recTy[] (π₁ τ) A) ([ recSub (π₁ τ) ]tᴹ recTm t))
  --     ≡⟨ cong (λ tᴹ → tr TmᴹFamₜ (recTy[] σ ([ π₁ τ ] A)) ([ recSub σ ]tᴹ tᴹ))
  --             (recTm[] (π₁ τ)t) ⟩
  --   tr TmᴹFamₜ (recTy[] σ ([ π₁ τ ] A)) ([ recSub σ ]tᴹ recTm ([ π₁ τ ]t t))
  --     ≡⟨ recTm[] σ ([ π₁ τ ]t t) ⟩
  --   recTm ([ σ ]t [ π₁ τ ]t t)
  --     ∎
  --   where
  --     open ≡-Reasoning
  --     eq : [ recSub σ ]ᴹ ([ π₁ᴹ (recSub τ) ]ᴹ recTy A) ≡ recTy ([ σ ] [ π₁ τ ] A)
  --     eq = trans (cong ([ recSub σ ]ᴹ_) (recTy[] (π₁ τ) A)) (recTy[] σ ([ π₁ τ ] A))
  
  -- recTm[]  ∅            {A} t = cong (tr TmᴹFamₜ (recTy[] ∅ A)) [∅ˢᴹ]tᴹ
  -- recTm[] (σ , u)       {A} t = cong (tr TmᴹFamₜ (recTy[] (σ , u) A)) [,ˢᴹ]tᴹ
  -- recTm[] (π₁ idS)      {A} t = cong (tr TmᴹFamₜ (recTy[] (π₁ idS) A)) [π₁ᴹidSᴹ]tᴹ
  -- recTm[] (π₁ (π₁ σ))   {A} t = cong (tr TmᴹFamₜ (recTy[] (π₁ (π₁ σ)) A)) [π₁ᴹπ₁ᴹ]tᴹ

  -- recSub↑-tot idS A = begin
  --   ([ idSᴹ ]ᴹ recTy A) ,' (idSᴹ ↑ᴹ recTy A)
  --     ≡⟨ _ ,Σ≡ idSᴹ↑ᴹ ⟩
  --   recTy ([ idS ] A) ,' recSub (idS ↑ A)
  --     ∎
  --   where open ≡-Reasoning
  -- recSub↑-tot {Δ} {Γ} {i} (_⨟_ {Δ = Θ} σ τ) A = begin
  --   [ recSub σ ⨟ᴹ recSub τ ]ᴹ recTy A ,' (recSub σ ⨟ᴹ recSub τ) ↑ᴹ recTy A
  --     ≡⟨ _ ,Σ≡ ⨟ᴹ↑ᴹ ⟩
  --   [ recSub σ ]ᴹ ([ recSub τ ]ᴹ recTy A) ,'
  --   (recSub σ ↑ᴹ ([ recSub τ ]ᴹ recTy A)) ⨟ᴹ (recSub τ ↑ᴹ recTy A)
  --     ≡⟨ apΣ Subᴹ,ᶜᴹFam ([ recSub σ ]ᴹ_) (ap₂Σ (λ {Aᴹ} τᴹ → (recSub σ ↑ᴹ Aᴹ) ⨟ᴹ τᴹ) (recSub↑-tot τ A)) ⟩
  --   [ recSub σ ]ᴹ recTy ([ τ ] A) ,'
  --   (recSub σ ↑ᴹ recTy ([ τ ] A)) ⨟ᴹ recSub (τ ↑ A)
  --     ≡⟨ ap₂Σ (_⨟ᴹ recSub (τ ↑ A)) (recSub↑-tot σ ([ τ ] A)) ⟩
  --   recTy ([ σ ] [ τ ] A) ,' recSub (σ ↑ ([ τ ] A)) ⨟ᴹ recSub (τ ↑ A)
  --     ∎
  --   where open ≡-Reasoning
  
  -- recSub↑-tot {Δ} {Γ} {i} (π₁ (σ , t)) A = begin
  --   [ π₁ᴹ (recSub σ ,ˢᴹ _) ]ᴹ recTy A ,' (π₁ᴹ (recSub σ ,ˢᴹ _) ↑ᴹ recTy A)
  --     ≡⟨ _ ,Σ≡ π₁ᴹ,ˢᴹ↑ᴹ ⟩
  --   [ recSub σ ]ᴹ recTy A ,' recSub σ ↑ᴹ recTy A
  --     ≡⟨ recSub↑-tot σ A ⟩
  --   recTy ([ σ ] A) ,' recSub (σ ↑ A)
  --     ∎
  --   where open ≡-Reasoning
  -- recSub↑-tot (π₁ (σ ⨟ τ)) A = begin
  --   [ π₁ᴹ (recSub σ ⨟ᴹ recSub τ) ]ᴹ recTy A ,' π₁ᴹ (recSub σ ⨟ᴹ recSub τ) ↑ᴹ recTy A
  --     ≡⟨ _ ,Σ≡ π₁ᴹ⨟ᴹ↑ᴹ ⟩
  --   [ recSub σ ]ᴹ ([ π₁ᴹ (recSub τ) ]ᴹ recTy A) ,'
  --   (recSub σ ↑ᴹ ([ π₁ᴹ (recSub τ) ]ᴹ recTy A)) ⨟ᴹ (π₁ᴹ (recSub τ) ↑ᴹ recTy A)
  --     ≡⟨ apΣ Subᴹ,ᶜᴹFam ([ recSub σ ]ᴹ_) (ap₂Σ (λ {Aᴹ} τᴹ → (recSub σ ↑ᴹ Aᴹ) ⨟ᴹ τᴹ) (recSub↑-tot (π₁ τ) A)) ⟩
  --   [ recSub σ ]ᴹ recTy ([ π₁ τ ] A) ,'
  --   (recSub σ ↑ᴹ recTy ([ π₁ τ ] A)) ⨟ᴹ recSub (π₁ τ ↑ A)
  --     ≡⟨ ap₂Σ (_⨟ᴹ recSub (π₁ τ ↑ A)) (recSub↑-tot σ ([ π₁ τ ] A)) ⟩
  --   recTy ([ σ ] [ π₁ τ ] A) ,' recSub (σ ↑ ([ π₁ τ ] A)) ⨟ᴹ recSub (π₁ τ ↑ A)
  --     ∎
  --   where open ≡-Reasoning
  -- recSub↑-tot ∅ A = ≅-to-≡ $ begin
  --   [ ∅ˢᴹ ]ᴹ recTy A ,' ∅ˢᴹ ↑ᴹ recTy A
  --     ≡⟨ _ ,Σ≡ ∅ˢᴹ↑ᴹ ⟩
  --   [ ∅ˢᴹ ]ᴹ recTy A ,' (π₁ᴹ idSᴹ ⨟ᴹ ∅ˢᴹ) ,ˢᴹ tr TmᴹFamₜ (sym $ [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ)
  --     ≡⟨ ap₂Σ ((π₁ᴹ idSᴹ ⨟ᴹ ∅ˢᴹ) ,ˢᴹ_) (recTy[] ∅ A ,Σ≡ ≅-to-≡ heq) ⟩
  --   recTy ([ ∅ ] A) ,' _
  --     ∎
  --     where
  --       open ≅-Reasoning
  --       heq : tr (λ Aᴹ → Tmᴹ (recCtx Δ ,ᶜᴹ Aᴹ) ([ π₁ᴹ idSᴹ ⨟ᴹ ∅ˢᴹ ]ᴹ recTy A))
  --               (recTy[] ∅ A)
  --               (tr TmᴹFamₜ (sym [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ))
  --          ≅ tr TmᴹFamₜ (sym $ recTy[] (wk ⨟ ∅) A)
  --               (tr TmᴹFamₜ (recTy[] wk ([ ∅ ] A)) (π₂ᴹ idSᴹ))
  --       heq {Δ} = begin
  --         tr (λ Aᴹ → Tmᴹ (recCtx Δ ,ᶜᴹ Aᴹ) ([ π₁ᴹ idSᴹ ⨟ᴹ ∅ˢᴹ ]ᴹ recTy A))
  --            (recTy[] ∅ A)
  --            (tr TmᴹFamₜ (sym [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ))
  --           ≅⟨ tr≅ (λ Aᴹ → Tmᴹ (recCtx Δ ,ᶜᴹ Aᴹ) ([ π₁ᴹ idSᴹ ⨟ᴹ ∅ˢᴹ ]ᴹ recTy A)) (recTy[] ∅ A) (tr TmᴹFamₜ (sym [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ)) ⟩
  --         tr TmᴹFamₜ (sym [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ)
  --           ≅⟨ tr≅ TmᴹFamₜ (sym [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ) ⟩
  --         π₂ᴹ {Aᴹ = [ recSub ∅ ]ᴹ recTy A} idSᴹ
  --           ≅⟨ vzᴹ≅ ⟩
  --         π₂ᴹ {Aᴹ = recTy ([ ∅ ] A)} idSᴹ
  --           ≅⟨ tr≅ TmᴹFamₜ (trans (recTy[] wk ([ ∅ ] A)) (sym $ recTy[] (wk ⨟ ∅) A)) (π₂ᴹ idSᴹ) ⟨
  --         tr TmᴹFamₜ (trans (recTy[] wk ([ ∅ ] A)) (sym $ recTy[] (wk ⨟ ∅) A)) (π₂ᴹ idSᴹ)
  --           ≡⟨ tr² {P = TmᴹFamₜ} (recTy[] wk ([ ∅ ] A)) ⟨
  --         tr TmᴹFamₜ (sym $ recTy[] (wk ⨟ ∅) A)
  --           (tr TmᴹFamₜ (recTy[] wk ([ ∅ ] A)) (π₂ᴹ idSᴹ))
  --           ∎
  --           where
  --             vzᴹ≅ : π₂ᴹ {Δᴹ = recCtx Δ ,ᶜᴹ ([ recSub ∅ ]ᴹ recTy A)} {Aᴹ = [ recSub ∅ ]ᴹ recTy A} idSᴹ
  --                   ≅ π₂ᴹ {Δᴹ = recCtx Δ ,ᶜᴹ recTy ([ ∅ ] A)} {Aᴹ = recTy ([ ∅ ] A)} idSᴹ
  --             vzᴹ≅ = hcong (λ Aᴹ → π₂ᴹ {Δᴹ = recCtx Δ ,ᶜᴹ Aᴹ} {Aᴹ = Aᴹ} idSᴹ) (≡-to-≅ $ recTy[] ∅ A)
  
  -- recSub↑-tot {Δ} (_,_ σ {A'} t) A = ≅-to-≡ $ begin
  --   [ recSub σ ,ˢᴹ tᴹ ]ᴹ recTy A
  --     ,' (recSub σ ,ˢᴹ tᴹ) ↑ᴹ recTy A
  --     ≡⟨ _ ,Σ≡ ,ˢᴹ↑ᴹ {σᴹ = recSub σ} {tᴹ = tᴹ} ⟩
  --   [ recSub σ ,ˢᴹ tᴹ ]ᴹ recTy A
  --     ,' (π₁ᴹ idSᴹ ⨟ᴹ (recSub σ ,ˢᴹ tᴹ)) ,ˢᴹ tr TmᴹFamₜ (sym $ [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ)
  --     ≡⟨ ap₂Σ ((π₁ᴹ idSᴹ ⨟ᴹ (recSub σ ,ˢᴹ tᴹ)) ,ˢᴹ_) (recTy[] (σ , t) A ,Σ≡ ≅-to-≡ heq) ⟩
  --   recTy ([ σ , t ] A) ,' _
  --     ∎
  --   where
  --     open ≅-Reasoning
  --     tᴹ = tr TmᴹFamₜ (sym $ recTy[] σ A') (recTm t)
  --     heq : tr (λ Aᴹ → Tmᴹ (recCtx Δ ,ᶜᴹ Aᴹ) ([ π₁ᴹ idSᴹ ⨟ᴹ (recSub σ ,ˢᴹ tᴹ) ]ᴹ recTy A))
  --              (recTy[] (σ , t) A)
  --              (tr TmᴹFamₜ (sym $ [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ))
  --         ≅ tr TmᴹFamₜ (sym $ recTy[] (wk ⨟ (σ , t)) A)
  --             (tr TmᴹFamₜ (recTy[] wk ([ σ , t ] A)) (π₂ᴹ idSᴹ))
  --     heq = begin
  --       tr (λ Aᴹ → Tmᴹ (recCtx Δ ,ᶜᴹ Aᴹ) ([ π₁ᴹ idSᴹ ⨟ᴹ (recSub σ ,ˢᴹ tᴹ) ]ᴹ recTy A))
  --          (recTy[] (σ , t) A)
  --          (tr TmᴹFamₜ (sym $ [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ))
  --         ≅⟨ tr≅ (λ Aᴹ → Tmᴹ (recCtx Δ ,ᶜᴹ Aᴹ) ([ π₁ᴹ idSᴹ ⨟ᴹ (recSub σ ,ˢᴹ tᴹ) ]ᴹ recTy A))
  --                (recTy[] (σ , t) A) _ ⟩
  --       tr TmᴹFamₜ (sym $ [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ)
  --         ≅⟨ tr≅ TmᴹFamₜ (sym $ [⨟ᴹ]ᴹ) _ ⟩
  --       π₂ᴹ {Aᴹ = [ recSub (σ , t) ]ᴹ recTy A} idSᴹ
  --         ≅⟨ vzᴹ≅ ⟩
  --       π₂ᴹ {Aᴹ = recTy ([ σ , t ] A)} idSᴹ
  --         ≅⟨ tr≅ TmᴹFamₜ (trans (recTy[] wk ([ σ , t ] A)) (sym $ recTy[] (wk ⨟ (σ , t)) A)) _ ⟨
  --       tr TmᴹFamₜ (trans (recTy[] wk ([ σ , t ] A)) (sym $ recTy[] (wk ⨟ (σ , t)) A))
  --         (π₂ᴹ idSᴹ)
  --         ≡⟨ tr² {P = TmᴹFamₜ} (recTy[] wk ([ σ , t ] A)) ⟨
  --       tr TmᴹFamₜ (sym $ recTy[] (wk ⨟ (σ , t)) A)
  --         (tr TmᴹFamₜ (recTy[] wk ([ σ , t ] A)) (π₂ᴹ idSᴹ))
  --         ∎
  --         where
  --           vzᴹ≅ : π₂ᴹ {Δᴹ = recCtx Δ ,ᶜᴹ ([ recSub (σ , t) ]ᴹ recTy A)} {Aᴹ = [ recSub (σ , t) ]ᴹ recTy A} idSᴹ
  --                 ≅ π₂ᴹ {Δᴹ = recCtx Δ ,ᶜᴹ recTy ([ σ , t ] A)} {Aᴹ = recTy ([ σ , t ] A)} idSᴹ
  --           vzᴹ≅ = hcong (λ Aᴹ → π₂ᴹ {Δᴹ = recCtx Δ ,ᶜᴹ Aᴹ} {Aᴹ = Aᴹ} idSᴹ) (≡-to-≅ $ recTy[] (σ , t) A)
      
  -- recSub↑-tot {Δ} {Γ} {i} (π₁ {A = A'} idS) A = ≅-to-≡ $ begin
  --   [ π₁ᴹ idSᴹ ]ᴹ recTy A ,' (π₁ᴹ idSᴹ ↑ᴹ recTy A)
  --     ≡⟨ _ ,Σ≡ π₁ᴹidSᴹ↑ᴹ ⟩
  --   [ π₁ᴹ idSᴹ ]ᴹ recTy A ,' (π₁ᴹ idSᴹ ⨟ᴹ π₁ᴹ idSᴹ) ,ˢᴹ tr TmᴹFamₜ (sym $ [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ)
  --     ≡⟨ ap₂Σ ((π₁ᴹ idSᴹ ⨟ᴹ π₁ᴹ idSᴹ) ,ˢᴹ_) (recTy[] (π₁ idS) A ,Σ≡ ≅-to-≡ heq) ⟩
  --   recTy ([ wk ] A) ,' _
  --     ∎
  --   where
  --     open ≅-Reasoning
  --     heq : tr (λ Aᴹ → Tmᴹ ((recCtx Γ ,ᶜᴹ recTy A') ,ᶜᴹ Aᴹ) ([ π₁ᴹ idSᴹ ⨟ᴹ π₁ᴹ idSᴹ ]ᴹ recTy A))
  --             (recTy[] wk A)
  --             (tr TmᴹFamₜ (sym $ [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ))
  --        ≅ tr TmᴹFamₜ (sym $ recTy[] (wk ⨟ π₁ {Γ , A'} idS) A)
  --             (tr TmᴹFamₜ (recTy[] wk ([ wk ] A)) (π₂ᴹ idSᴹ))
  --     heq = begin
  --       tr (λ Aᴹ → Tmᴹ ((recCtx Γ ,ᶜᴹ recTy A') ,ᶜᴹ Aᴹ) ([ π₁ᴹ idSᴹ ⨟ᴹ π₁ᴹ idSᴹ ]ᴹ recTy A))
  --          (recTy[] wk A)
  --          (tr TmᴹFamₜ (sym $ [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ))
  --         ≅⟨ tr≅ (λ Aᴹ → Tmᴹ ((recCtx Γ ,ᶜᴹ recTy A') ,ᶜᴹ Aᴹ) ([ π₁ᴹ idSᴹ ⨟ᴹ π₁ᴹ idSᴹ ]ᴹ recTy A))
  --                (recTy[] wk A) _ ⟩
  --       tr TmᴹFamₜ (sym $ [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ)
  --         ≅⟨ tr≅ TmᴹFamₜ (sym $ [⨟ᴹ]ᴹ) _ ⟩
  --       π₂ᴹ {Aᴹ = [ recSub wk ]ᴹ recTy A} idSᴹ
  --         ≅⟨ vzᴹ≅ ⟩
  --       π₂ᴹ {Aᴹ = recTy ([ wk ] A)} idSᴹ
  --         ≅⟨ tr≅ TmᴹFamₜ (trans (recTy[] wk ([ wk ] A)) (sym $ recTy[] (wk ⨟ π₁ {Γ , A'} idS) A)) _ ⟨
  --       tr TmᴹFamₜ (trans (recTy[] wk ([ wk ] A)) (sym $ recTy[] (wk ⨟ π₁ idS) A))
  --          (π₂ᴹ idSᴹ)
  --         ≡⟨ tr² (recTy[] wk ([ wk ] A)) ⟨
  --       tr TmᴹFamₜ (sym $ recTy[] (wk ⨟ π₁ idS) A)
  --          (tr TmᴹFamₜ (recTy[] wk ([ wk ] A)) (π₂ᴹ idSᴹ))
  --         ∎
  --       where
  --         vzᴹ≅ : π₂ᴹ {Δᴹ = (_ ,ᶜᴹ recTy A') ,ᶜᴹ _} {Aᴹ = [ recSub wk ]ᴹ recTy A} idSᴹ
  --              ≅ π₂ᴹ {Δᴹ = (_ ,ᶜᴹ recTy A') ,ᶜᴹ _} {Aᴹ = recTy ([ wk ] A)} idSᴹ
  --         vzᴹ≅ = hcong (λ Aᴹ → π₂ᴹ {Aᴹ = Aᴹ} idSᴹ) (≡-to-≅ $ recTy[] wk A)
          
  -- recSub↑-tot {Δ} (π₁ (π₁ σ)) A = ≅-to-≡ $ begin
  --   [ π₁ᴹ (π₁ᴹ (recSub σ)) ]ᴹ recTy A ,' (π₁ᴹ (π₁ᴹ (recSub σ)) ↑ᴹ recTy A)
  --     ≡⟨ _ ,Σ≡ π₁ᴹπ₁ᴹ↑ᴹ {σᴹ = recSub σ} ⟩
  --   [ π₁ᴹ (π₁ᴹ (recSub σ)) ]ᴹ recTy A ,'
  --     ((π₁ᴹ idSᴹ ⨟ᴹ π₁ᴹ (π₁ᴹ (recSub σ))) ,ˢᴹ tr TmᴹFamₜ (sym [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ))
  --     ≡⟨ ap₂Σ ((π₁ᴹ idSᴹ ⨟ᴹ π₁ᴹ (π₁ᴹ (recSub σ))) ,ˢᴹ_) (recTy[] (π₁ (π₁ σ)) A ,Σ≡ ≅-to-≡ heq) ⟩
  --   recTy ([ π₁ (π₁ σ) ] A) ,' _
  --     ∎
  --   where
  --     open ≅-Reasoning
  --     heq : tr (λ Aᴹ → Tmᴹ (recCtx Δ ,ᶜᴹ Aᴹ) ([ π₁ᴹ idSᴹ ⨟ᴹ π₁ᴹ (π₁ᴹ (recSub σ)) ]ᴹ recTy A))
  --              (recTy[] (π₁ (π₁ σ)) A)
  --              (tr TmᴹFamₜ (sym [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ))
  --         ≅ tr TmᴹFamₜ (sym $ recTy[] (wk ⨟ π₁ (π₁ σ)) A)
  --              (tr TmᴹFamₜ (recTy[] wk ([ π₁ (π₁ σ) ] A)) (π₂ᴹ idSᴹ))
  --     heq = begin
  --       tr (λ Aᴹ → Tmᴹ (recCtx Δ ,ᶜᴹ Aᴹ) ([ π₁ᴹ idSᴹ ⨟ᴹ π₁ᴹ (π₁ᴹ (recSub σ)) ]ᴹ recTy A))
  --          (recTy[] (π₁ (π₁ σ)) A)
  --          (tr TmᴹFamₜ (sym [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ))
  --         ≅⟨ tr≅ (λ Aᴹ → Tmᴹ (recCtx Δ ,ᶜᴹ Aᴹ) ([ π₁ᴹ idSᴹ ⨟ᴹ π₁ᴹ (π₁ᴹ (recSub σ)) ]ᴹ recTy A))
  --                (recTy[] (π₁ (π₁ σ)) A) _ ⟩
  --       tr TmᴹFamₜ (sym [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ)
  --         ≅⟨ tr≅ TmᴹFamₜ (sym [⨟ᴹ]ᴹ) _ ⟩
  --       π₂ᴹ {Aᴹ = [ recSub (π₁ (π₁ σ)) ]ᴹ recTy A} idSᴹ
  --         ≅⟨ vzᴹ≅ ⟩
  --       π₂ᴹ {Aᴹ = recTy ([ π₁ (π₁ σ) ] A)} idSᴹ
  --         ≅⟨ tr≅ TmᴹFamₜ (trans (recTy[] wk ([ π₁ (π₁ σ) ] A)) (sym $ recTy[] (wk ⨟ π₁ (π₁ σ)) A)) _ ⟨
  --       tr TmᴹFamₜ _ (π₂ᴹ idSᴹ)
  --         ≡⟨ tr² (recTy[] wk ([ π₁ (π₁ σ) ] A)) ⟨
  --       tr TmᴹFamₜ (sym $ recTy[] (wk ⨟ π₁ (π₁ σ)) A) _
  --         ∎
  --       where
  --         vzᴹ≅ : π₂ᴹ {Aᴹ = [ recSub (π₁ (π₁ σ)) ]ᴹ recTy A} idSᴹ
  --              ≅ π₂ᴹ {Aᴹ = recTy ([ π₁ (π₁ σ) ] A)} idSᴹ
  --         vzᴹ≅ = hcong (λ Aᴹ → π₂ᴹ {Aᴹ = Aᴹ} idSᴹ) (≡-to-≅ $ recTy[] (π₁ (π₁ σ)) A)
