-- Recursion for SC+U+Pi+Id
open import Prelude

module SC+U+Pi+Id.Recursion.Rec where

open import SC+U+Pi+Id.Recursion.Recursor.Motive
open import SC+U+Pi+Id.Recursion.Recursor.Method

record Recursor {ℓ ℓ′ : Level} : Set (lsuc (ℓ ⊔ ℓ′)) where
  field
    mot : Motive ℓ ℓ′
    met : Method mot

  open Motive mot public
  open Method met public

module _ {ℓ ℓ′ : Level} (rec : Recursor {ℓ} {ℓ′}) where
  open Recursor rec
  import SC+U+Pi+Id.QIIT.Syntax as I
  import SC+U+Pi+Id.QIIRT.Base as IR
  import SC+U+Pi+Id.QIIRT.Properties as IR

  module _ where
    private variable
      i j k : ℕ
      Γ Δ Θ : I.Ctx
      A B C : I.Ty _ _
      σ τ γ : I.Sub _ _
      t u v : I.Tm _ _
    
    {-# TERMINATING #-}
    recCtxᴵ
      : (Γ : I.Ctx) → Ctxᴹ
    recTyᴵ
      : (A : I.Ty Γ i) → Tyᴹ (recCtxᴵ Γ) i
    recSubᴵ
      : (σ : I.Sub Δ Γ) → Subᴹ (recCtxᴵ Δ) (recCtxᴵ Γ)
    recTmᴵ
      : (t : I.Tm Γ A) → Tmᴹ (recCtxᴵ Γ) (recTyᴵ A)
    
    recCtxᴵ I.∅ = ∅ᶜᴹ
    recCtxᴵ (Γ I., A) = recCtxᴵ Γ ,ᶜᴹ recTyᴵ A
    recTyᴵ (I.[ σ ] A) = [ recSubᴵ σ ]ᴹ recTyᴵ A
    recTyᴵ (I.U i) = Uᴹ i
    recTyᴵ (I.El u) = Elᴹ (recTmᴵ u)
    recTyᴵ (I.Lift A) = Liftᴹ (recTyᴵ A)
    recTyᴵ (I.Π A B) = Πᴹ (recTyᴵ A) (recTyᴵ B)
    recTyᴵ (I.Id a t u) = Idᴹ (recTmᴵ a) (recTmᴵ t) (recTmᴵ u)
    recSubᴵ I.∅ = ∅ˢᴹ
    recSubᴵ (σ I., t) = recSubᴵ σ ,ˢᴹ recTmᴵ t
    recSubᴵ I.idS = idSᴹ
    recSubᴵ (τ I.⨟ σ) = recSubᴵ τ ⨟ᴹ recSubᴵ σ
    recSubᴵ (I.π₁ σ) = π₁ᴹ (recSubᴵ σ)
    recTmᴵ (I.π₂ σ) = π₂ᴹ (recSubᴵ σ)
    recTmᴵ (I.[ σ ]tm t) = [ recSubᴵ σ ]tmᴹ recTmᴵ t
    recTmᴵ (I.c A) = cᴹ (recTyᴵ A)
    recTmᴵ (I.mk t) = mkᴹ (recTmᴵ t)
    recTmᴵ (I.un t) = unᴹ (recTmᴵ t)
    recTmᴵ (I.ƛ t) = ƛᴹ recTmᴵ t
    recTmᴵ (I.app t) = appᴹ (recTmᴵ t)

  module _ where
    private variable
      i j k : ℕ
      Γ Δ Θ : IR.Ctx
      A B C : IR.Ty _ _
      σ τ γ : IR.Sub _ _
      t u v : IR.Tm _ _
    
    {-# TERMINATING #-}
    recCtxᴵᴿ
      : (Γ : IR.Ctx) → Ctxᴹ
    recTyᴵᴿ
      : (A : IR.Ty Γ i) → Tyᴹ (recCtxᴵᴿ Γ) i
    recSubᴵᴿ
      : (σ : IR.Sub Δ Γ) → Subᴹ (recCtxᴵᴿ Δ) (recCtxᴵᴿ Γ)
    recTmᴵᴿ
      : (t : IR.Tm Γ A) → Tmᴹ (recCtxᴵᴿ Γ) (recTyᴵᴿ A)
    recTyᴵᴿ[]
      : (σ : IR.Sub Γ Δ)(A : IR.Ty Δ i)
      → [ recSubᴵᴿ σ ]ᴹ recTyᴵᴿ A ≡ recTyᴵᴿ (IR.[ σ ] A)
    recTmᴵᴿ[]
      : (σ : IR.Sub Γ Δ){A : IR.Ty Δ i}(t : IR.Tm Δ A)
      → tr TmᴹFam (recTyᴵᴿ[] σ A) ([ recSubᴵᴿ σ ]tmᴹ recTmᴵᴿ t)
      ≡ recTmᴵᴿ (IR.[ σ ]t t)
    
    recCtxᴵᴿ IR.∅ = ∅ᶜᴹ
    recCtxᴵᴿ (Γ IR., A) = recCtxᴵᴿ Γ ,ᶜᴹ recTyᴵᴿ A
    recTyᴵᴿ (IR.U i) = Uᴹ i
    recTyᴵᴿ (IR.El u) = Elᴹ (recTmᴵᴿ u)
    recTyᴵᴿ (IR.Lift A) = Liftᴹ (recTyᴵᴿ A)
    recTyᴵᴿ (IR.Π A B) = Πᴹ (recTyᴵᴿ A) (recTyᴵᴿ B)
    recTyᴵᴿ (IR.Id a t u) = Idᴹ (recTmᴵᴿ a) (recTmᴵᴿ t) (recTmᴵᴿ u)
    recSubᴵᴿ IR.∅ = ∅ˢᴹ
    recSubᴵᴿ (IR._,_ σ {A} t) = recSubᴵᴿ σ ,ˢᴹ tr TmᴹFam (sym $ recTyᴵᴿ[] σ A) (recTmᴵᴿ t)
    recSubᴵᴿ IR.idS = idSᴹ
    recSubᴵᴿ (τ IR.⨟ σ) = recSubᴵᴿ τ ⨟ᴹ recSubᴵᴿ σ
    recSubᴵᴿ (IR.π₁ σ) = π₁ᴹ (recSubᴵᴿ σ)
    recTmᴵᴿ (IR.π₂ {A = A} σ) = tr TmᴹFam (recTyᴵᴿ[] (IR.π₁ σ) A) (π₂ᴹ (recSubᴵᴿ σ))
    recTmᴵᴿ (IR.[_]tm_ σ {A} t) = tr TmᴹFam (recTyᴵᴿ[] σ A) ([ recSubᴵᴿ σ ]tmᴹ recTmᴵᴿ t)
    recTmᴵᴿ (IR.c A) = cᴹ (recTyᴵᴿ A)
    recTmᴵᴿ (IR.mk t) = mkᴹ (recTmᴵᴿ t) 
    recTmᴵᴿ (IR.un t) = unᴹ (recTmᴵᴿ t)
    recTmᴵᴿ (IR.ƛ t) = ƛᴹ recTmᴵᴿ t
    recTmᴵᴿ (IR.app t) = appᴹ (recTmᴵᴿ t)

    recSubᴵᴿ↑ : {i : ℕ}(σ : IR.Sub Γ Δ)(A : IR.Ty Δ i)
              → tr Subᴹ,ᶜᴹFam (recTyᴵᴿ[] σ A) (recSubᴵᴿ σ ↑ᴹ recTyᴵᴿ A) ≡ recSubᴵᴿ (σ IR.↑ A)

    recTyᴵᴿ[] σ (IR.U i) = []ᴹUᴹ
    recTyᴵᴿ[] σ (IR.El u) = begin
      [ recSubᴵᴿ σ ]ᴹ Elᴹ (recTmᴵᴿ u)
        ≡⟨ []ᴹElᴹ (recSubᴵᴿ σ) (recTmᴵᴿ u) ⟩
      Elᴹ (tr TmᴹFam []ᴹUᴹ ([ recSubᴵᴿ σ ]tmᴹ recTmᴵᴿ u))
        ≡⟨ cong Elᴹ (recTmᴵᴿ[] σ u) ⟩
      Elᴹ (recTmᴵᴿ (IR.[ σ ]t u))
        ∎
      where open ≡-Reasoning
    recTyᴵᴿ[] σ (IR.Lift A) = []ᴹLiftᴹ ∙ cong Liftᴹ (recTyᴵᴿ[] σ A)
    recTyᴵᴿ[] {Γ} {Δ} {i} σ (IR.Π A B) = []ᴹΠᴹ ∙ cong (uncurry Πᴹ) (recTyᴵᴿ[] σ A ,Σ≡ eq)
      where
        open ≡-Reasoning
        eq : tr (λ Aᴹ → Tyᴹ (recCtxᴵᴿ Γ ,ᶜᴹ Aᴹ) i) (recTyᴵᴿ[] σ A) ([ recSubᴵᴿ σ ↑ᴹ recTyᴵᴿ A ]ᴹ recTyᴵᴿ B)
           ≡ recTyᴵᴿ (IR.[ σ IR.↑ A ] B)
        eq = begin
          tr (λ Aᴹ → Tyᴹ (recCtxᴵᴿ Γ ,ᶜᴹ Aᴹ) i) (recTyᴵᴿ[] σ A) ([ recSubᴵᴿ σ ↑ᴹ recTyᴵᴿ A ]ᴹ recTyᴵᴿ B)
            ≡⟨ tr-nat Subᴹ,ᶜᴹFam (λ _ σᴹ → [ σᴹ ]ᴹ recTyᴵᴿ B) (recTyᴵᴿ[] σ A) ⟩
          [ tr Subᴹ,ᶜᴹFam (recTyᴵᴿ[] σ A) (recSubᴵᴿ σ ↑ᴹ recTyᴵᴿ A) ]ᴹ recTyᴵᴿ B
            ≡⟨ cong ([_]ᴹ recTyᴵᴿ B) (recSubᴵᴿ↑ σ A) ⟩
          [ recSubᴵᴿ (σ IR.↑ A) ]ᴹ recTyᴵᴿ B
            ≡⟨ recTyᴵᴿ[] (σ IR.↑ A) B ⟩
          recTyᴵᴿ (IR.[ σ IR.↑ A ] B)
            ∎
    recTyᴵᴿ[] σ (IR.Id a t u) = []ᴹIdᴹ ∙ cong₃ Idᴹ (recTmᴵᴿ[] σ a) (eqtm t) (eqtm u)
      where
        open ≡-Reasoning
        eqtm : (t : IR.Tm _ (IR.El a))
             → tr (λ x → TmᴹFam (Elᴹ x)) (recTmᴵᴿ[] σ a)
                  (tr TmᴹFam ([]ᴹElᴹ (recSubᴵᴿ σ) (recTmᴵᴿ a))
                      ([ recSubᴵᴿ σ ]tmᴹ recTmᴵᴿ t))
             ≡ recTmᴵᴿ (IR.[ σ ]t t)
        eqtm t = begin
          tr (λ x → TmᴹFam (Elᴹ x)) (recTmᴵᴿ[] σ a)
             (tr TmᴹFam ([]ᴹElᴹ (recSubᴵᴿ σ) (recTmᴵᴿ a))
                 ([ recSubᴵᴿ σ ]tmᴹ recTmᴵᴿ t))
            ≡⟨ tr-cong {P = TmᴹFam} (recTmᴵᴿ[] σ a) ⟩
          tr TmᴹFam (cong Elᴹ (recTmᴵᴿ[] σ a))
             (tr TmᴹFam ([]ᴹElᴹ (recSubᴵᴿ σ) (recTmᴵᴿ a))
                 ([ recSubᴵᴿ σ ]tmᴹ recTmᴵᴿ t))
            ≡⟨ tr² ([]ᴹElᴹ (recSubᴵᴿ σ) (recTmᴵᴿ a)) {cong Elᴹ (recTmᴵᴿ[] σ a)} ⟩
          tr TmᴹFam ([]ᴹElᴹ (recSubᴵᴿ σ) (recTmᴵᴿ a) ∙ cong Elᴹ (recTmᴵᴿ[] σ a))
             ([ recSubᴵᴿ σ ]tmᴹ recTmᴵᴿ t)
            ≡⟨ cong (λ p → tr TmᴹFam p ([ recSubᴵᴿ σ ]tmᴹ recTmᴵᴿ t))
                    (uip ([]ᴹElᴹ (recSubᴵᴿ σ) (recTmᴵᴿ a) ∙ cong Elᴹ (recTmᴵᴿ[] σ a))
                         (recTyᴵᴿ[] σ (IR.El a))) ⟩
          tr TmᴹFam (recTyᴵᴿ[] σ (IR.El a)) ([ recSubᴵᴿ σ ]tmᴹ recTmᴵᴿ t)
            ≡⟨ recTmᴵᴿ[] σ t ⟩
          recTmᴵᴿ (IR.[ σ ]t t)
            ∎
    
    recTmᴵᴿ[] σ t = cong recTmᴵᴿ (IR.[]tm≡[]t t σ)

    recSubᴵᴿ↑ σ A = ≅-to-≡ $ begin
      tr Subᴹ,ᶜᴹFam (recTyᴵᴿ[] σ A) (recSubᴵᴿ σ ↑ᴹ recTyᴵᴿ A)
        ≅⟨ tr≅ Subᴹ,ᶜᴹFam (recTyᴵᴿ[] σ A) (recSubᴵᴿ σ ↑ᴹ recTyᴵᴿ A) ⟩
      (π₁ᴹ idSᴹ ⨟ᴹ recSubᴵᴿ σ) ,ˢᴹ tr TmᴹFam (sym [⨟ᴹ]ᴹ) (π₂ᴹ {Aᴹ = [ recSubᴵᴿ σ ]ᴹ recTyᴵᴿ A} idSᴹ)
        ≅⟨ hcong₂ (λ Aᴹ tᴹ → (π₁ᴹ {Aᴹ = Aᴹ} idSᴹ ⨟ᴹ recSubᴵᴿ σ) ,ˢᴹ tᴹ)
                  (≡-to-≅ $ recTyᴵᴿ[] σ A)
                  heq ⟩
      (π₁ᴹ idSᴹ ⨟ᴹ recSubᴵᴿ σ) ,ˢᴹ
        tr TmᴹFam (sym $ recTyᴵᴿ[] (IR.π₁ IR.idS IR.⨟ σ) A)
           (tr TmᴹFam (recTyᴵᴿ[] (IR.π₁ IR.idS) (IR.[ σ ] A))
               (π₂ᴹ idSᴹ))
        ≡⟨ sym $ cong recSubᴵᴿ (IR.↑=⁺ A σ) ⟩
      recSubᴵᴿ (σ IR.↑ A)
        ∎
      where
        open ≅-Reasoning
        heq : tr TmᴹFam (sym [⨟ᴹ]ᴹ) (π₂ᴹ {Aᴹ = [ recSubᴵᴿ σ ]ᴹ recTyᴵᴿ A} idSᴹ)
            ≅ tr TmᴹFam (sym $ recTyᴵᴿ[] (IR.π₁ {A = IR.[ σ ] A} IR.idS IR.⨟ σ) A)
                 (tr TmᴹFam (recTyᴵᴿ[] (IR.π₁ IR.idS) (IR.[ σ ] A))
                     (π₂ᴹ idSᴹ))
        heq = begin
          tr TmᴹFam (sym [⨟ᴹ]ᴹ) (π₂ᴹ {Aᴹ = [ recSubᴵᴿ σ ]ᴹ recTyᴵᴿ A} idSᴹ)
            ≅⟨ tr≅ TmᴹFam (sym [⨟ᴹ]ᴹ) (π₂ᴹ idSᴹ) ⟩
          π₂ᴹ {Aᴹ = [ recSubᴵᴿ σ ]ᴹ recTyᴵᴿ A} idSᴹ
            ≅⟨ HEq.cong (λ Aᴹ → π₂ᴹ {Aᴹ = Aᴹ} idSᴹ) (≡-to-≅ $ recTyᴵᴿ[] σ A) ⟩
          π₂ᴹ {Aᴹ = recTyᴵᴿ (IR.[ σ ] A)} idSᴹ
            ≅⟨ tr≅ TmᴹFam (recTyᴵᴿ[] (IR.π₁ {A = IR.[ σ ] A} IR.idS) (IR.[ σ ] A))
                   (π₂ᴹ idSᴹ) ⟨
          tr TmᴹFam (recTyᴵᴿ[] (IR.π₁ IR.idS) (IR.[ σ ] A)) (π₂ᴹ idSᴹ)
            ≅⟨ tr≅ TmᴹFam (sym $ recTyᴵᴿ[] (IR.π₁ {A = IR.[ σ ] A} IR.idS IR.⨟ σ) A)
                   (tr TmᴹFam (recTyᴵᴿ[] (IR.π₁ IR.idS) (IR.[ σ ] A)) (π₂ᴹ idSᴹ)) ⟨
          tr TmᴹFam (sym $ recTyᴵᴿ[] (IR.π₁ IR.idS IR.⨟ σ) A)
             (tr TmᴹFam (recTyᴵᴿ[] (IR.π₁ IR.idS) (IR.[ σ ] A))
                 (π₂ᴹ idSᴹ))
            ∎