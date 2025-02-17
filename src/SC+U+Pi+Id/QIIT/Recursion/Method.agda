-- Methods of SC+U+Pi+Id.QIIT Recursor
module SC+U+Pi+Id.QIIT.Recursion.Method where

open import Prelude
open import SC+U+Pi+Id.QIIT.Recursion.Motive

module _ {ℓ ℓ′}(Mot : Motive ℓ ℓ′) where
  open Motive Mot
  private variable
    i j k : ℕ
    Γᴹ Δᴹ Θᴹ Φᴹ : Ctxᴹ
    σᴹ τᴹ γᴹ    : Subᴹ Γᴹ Δᴹ
    Aᴹ Bᴹ Cᴹ    : Tyᴹ Γᴹ i
    aᴹ tᴹ uᴹ    : Tmᴹ Γᴹ Aᴹ

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
      [idS]ᴹ
        : [ idSᴹ ]ᴹ Aᴹ ≡ Aᴹ
      [⨟]ᴹ
        : [ σᴹ ⨟ᴹ τᴹ ]ᴹ Aᴹ ≡ [ σᴹ ]ᴹ ([ τᴹ ]ᴹ Aᴹ)
      π₂ᴹ
        : (σᴹ : Subᴹ Γᴹ (Δᴹ ,ᶜᴹ Aᴹ))
        → Tmᴹ Γᴹ ([ π₁ᴹ σᴹ ]ᴹ Aᴹ)
      [_]tmᴹ_
        : (σᴹ : Subᴹ Γᴹ Δᴹ){Aᴹ : Tyᴹ Δᴹ i}
        → (tᴹ : Tmᴹ Δᴹ Aᴹ)
        → Tmᴹ Γᴹ ([ σᴹ ]ᴹ Aᴹ)
    
    _↑ᴹ_
      : (σᴹ : Subᴹ Γᴹ Δᴹ)(Aᴹ : Tyᴹ Δᴹ i)
      → Subᴹ (Γᴹ ,ᶜᴹ ([ σᴹ ]ᴹ Aᴹ)) (Δᴹ ,ᶜᴹ Aᴹ)
    _↑ᴹ_ {Γᴹ} {Δᴹ} σᴹ Aᴹ
      = (π₁ᴹ idSᴹ ⨟ᴹ σᴹ) ,ˢᴹ tr TmᴹFam (sym [⨟]ᴹ) (π₂ᴹ idSᴹ)
    
    Subᴹ,ᶜᴹFam
      : {i : ℕ}{Γᴹ Δᴹ : Ctxᴹ} → Tyᴹ Γᴹ i → Set ℓ′
    Subᴹ,ᶜᴹFam {_} {Γᴹ} {Δᴹ} Aᴹ = Subᴹ (Γᴹ ,ᶜᴹ Aᴹ) Δᴹ

    field
      _⨟idSᴹ
        : (σᴹ : Subᴹ Γᴹ Δᴹ)
        → σᴹ ⨟ᴹ idSᴹ ≡ σᴹ
      idS⨟ᴹ_
        : (σᴹ : Subᴹ Γᴹ Δᴹ)
        → idSᴹ ⨟ᴹ σᴹ ≡ σᴹ
      ⨟-assocᴹ
        : σᴹ ⨟ᴹ (τᴹ ⨟ᴹ γᴹ) ≡ (σᴹ ⨟ᴹ τᴹ) ⨟ᴹ γᴹ
      π₁,ᴹ
        : π₁ᴹ (σᴹ ,ˢᴹ tᴹ) ≡ σᴹ
      ⨟,ᴹ
        : {Γᴹ Δᴹ Θᴹ : Ctxᴹ}{Aᴹ : Tyᴹ Θᴹ i}
          {σᴹ : Subᴹ Γᴹ Δᴹ}{τᴹ : Subᴹ Δᴹ Θᴹ}{tᴹ : Tmᴹ Δᴹ ([ τᴹ ]ᴹ Aᴹ)}
        → σᴹ ⨟ᴹ (τᴹ ,ˢᴹ tᴹ) ≡ (σᴹ ⨟ᴹ τᴹ) ,ˢᴹ tr TmᴹFam (sym [⨟]ᴹ) ([ σᴹ ]tmᴹ tᴹ)
      η∅ᴹ
        : σᴹ ≡ ∅ˢᴹ
      η,ᴹ
        : σᴹ ≡ π₁ᴹ σᴹ ,ˢᴹ π₂ᴹ σᴹ
      [idS]tmᴹ
        : tr TmᴹFam [idS]ᴹ ([ idSᴹ ]tmᴹ tᴹ) ≡ tᴹ
      [⨟]tmᴹ
        : tr TmᴹFam [⨟]ᴹ ([ σᴹ ⨟ᴹ τᴹ ]tmᴹ tᴹ) ≡ [ σᴹ ]tmᴹ ([ τᴹ ]tmᴹ tᴹ)
      π₂,ᴹ
        : {Aᴹ : Tyᴹ Δᴹ i}{σᴹ : Subᴹ Γᴹ Δᴹ}{tᴹ : Tmᴹ Γᴹ ([ σᴹ ]ᴹ Aᴹ)}
        → tr (λ τᴹ → TmᴹFam ([ τᴹ ]ᴹ Aᴹ)) π₁,ᴹ (π₂ᴹ (σᴹ ,ˢᴹ tᴹ)) ≡ tᴹ

    -----------
    -- derived equalities of CwF
    π₁⨟ᴹ 
      : {Aᴹ : Tyᴹ Θᴹ i}(τᴹ : Subᴹ Γᴹ Δᴹ)(σᴹ : Subᴹ Δᴹ (Θᴹ ,ᶜᴹ Aᴹ))
      → π₁ᴹ (τᴹ ⨟ᴹ σᴹ) ≡ τᴹ ⨟ᴹ π₁ᴹ σᴹ
    π₁⨟ᴹ τᴹ σᴹ = begin
      π₁ᴹ (τᴹ ⨟ᴹ σᴹ)
        ≡⟨ cong (λ x → π₁ᴹ (τᴹ ⨟ᴹ x)) η,ᴹ ⟩
      π₁ᴹ (τᴹ ⨟ᴹ (π₁ᴹ σᴹ ,ˢᴹ π₂ᴹ σᴹ))
        ≡⟨ cong π₁ᴹ ⨟,ᴹ ⟩
      π₁ᴹ ((τᴹ ⨟ᴹ π₁ᴹ σᴹ) ,ˢᴹ tr TmᴹFam (sym [⨟]ᴹ) ([ τᴹ ]tmᴹ π₂ᴹ σᴹ))
        ≡⟨ π₁,ᴹ ⟩
      τᴹ ⨟ᴹ π₁ᴹ σᴹ
        ∎
      where open ≡-Reasoning
    
    π₂⨟ᴹ : (σᴹ : Subᴹ Γᴹ Δᴹ){Aᴹ : Tyᴹ Θᴹ i}(τᴹ : Subᴹ Δᴹ (Θᴹ ,ᶜᴹ Aᴹ))
         → tr TmᴹFam (cong ([_]ᴹ Aᴹ) (π₁⨟ᴹ σᴹ τᴹ) ∙ [⨟]ᴹ) (π₂ᴹ (σᴹ ⨟ᴹ τᴹ))
         ≡ [ σᴹ ]tmᴹ (π₂ᴹ τᴹ)
    π₂⨟ᴹ σᴹ {Aᴹ} τᴹ = ≅-to-≡ $ begin
      tr TmᴹFam (cong ([_]ᴹ Aᴹ) (π₁⨟ᴹ σᴹ τᴹ) ∙ [⨟]ᴹ) (π₂ᴹ (σᴹ ⨟ᴹ τᴹ))
        ≅⟨ tr≅ TmᴹFam (cong ([_]ᴹ Aᴹ) (π₁⨟ᴹ σᴹ τᴹ) ∙ [⨟]ᴹ) (π₂ᴹ (σᴹ ⨟ᴹ τᴹ)) ⟩
      π₂ᴹ (σᴹ ⨟ᴹ τᴹ)
        ≅⟨ hcong (λ x → π₂ᴹ (σᴹ ⨟ᴹ x)) (≡-to-≅ η,ᴹ) ⟩
      π₂ᴹ (σᴹ ⨟ᴹ (π₁ᴹ τᴹ ,ˢᴹ π₂ᴹ τᴹ))
        ≅⟨ hcong π₂ᴹ (≡-to-≅ ⨟,ᴹ) ⟩
      π₂ᴹ ((σᴹ ⨟ᴹ π₁ᴹ τᴹ) ,ˢᴹ tr TmᴹFam (sym [⨟]ᴹ) ([ σᴹ ]tmᴹ π₂ᴹ τᴹ))
        ≅⟨ tr≅ (TmᴹFam ∘ ([_]ᴹ Aᴹ)) π₁,ᴹ (π₂ᴹ ((σᴹ ⨟ᴹ π₁ᴹ τᴹ) ,ˢᴹ _)) ⟨
      tr (TmᴹFam ∘ ([_]ᴹ Aᴹ)) π₁,ᴹ
         (π₂ᴹ ((σᴹ ⨟ᴹ π₁ᴹ τᴹ) ,ˢᴹ tr TmᴹFam (sym [⨟]ᴹ) ([ σᴹ ]tmᴹ π₂ᴹ τᴹ)))
        ≅⟨ ≡-to-≅ $ π₂,ᴹ ⟩
      tr TmᴹFam (sym [⨟]ᴹ) ([ σᴹ ]tmᴹ π₂ᴹ τᴹ)
        ≅⟨ tr≅ TmᴹFam (sym [⨟]ᴹ) _ ⟩
      [ σᴹ ]tmᴹ π₂ᴹ τᴹ
        ∎
      where open ≅-Reasoning
    
    _⨟π₁idSᴹ : (σᴹ : Subᴹ Γᴹ (Δᴹ ,ᶜᴹ Aᴹ)) → π₁ᴹ σᴹ ≡ σᴹ ⨟ᴹ π₁ᴹ idSᴹ
    σᴹ ⨟π₁idSᴹ = sym (cong π₁ᴹ (σᴹ ⨟idSᴹ)) ∙ π₁⨟ᴹ σᴹ idSᴹ
    
    ↑⨟wkᴹ : (σᴹ : Subᴹ Γᴹ Δᴹ){Aᴹ : Tyᴹ Δᴹ i} → (σᴹ ↑ᴹ Aᴹ) ⨟ᴹ π₁ᴹ idSᴹ ≡ π₁ᴹ idSᴹ ⨟ᴹ σᴹ
    ↑⨟wkᴹ {Γᴹ} {Δᴹ} {i} σᴹ {Aᴹ} = begin
      (σᴹ ↑ᴹ Aᴹ) ⨟ᴹ π₁ᴹ idSᴹ                                     ≡⟨ (σᴹ ↑ᴹ Aᴹ) ⨟π₁idSᴹ ⟨
      π₁ᴹ ((π₁ᴹ idSᴹ ⨟ᴹ σᴹ) ,ˢᴹ tr TmᴹFam (sym [⨟]ᴹ) (π₂ᴹ idSᴹ)) ≡⟨ π₁,ᴹ ⟩
      π₁ᴹ idSᴹ ⨟ᴹ σᴹ ∎
      where open ≡-Reasoning
    
    [↑]vzᴹ : (σᴹ : Subᴹ Γᴹ Δᴹ)(Aᴹ : Tyᴹ Δᴹ i)
           → [ σᴹ ↑ᴹ Aᴹ ]tmᴹ π₂ᴹ idSᴹ ≅ π₂ᴹ {Aᴹ = [ σᴹ ]ᴹ Aᴹ} idSᴹ
    [↑]vzᴹ σᴹ Aᴹ = begin
      [ σᴹ ↑ᴹ Aᴹ ]tmᴹ π₂ᴹ idSᴹ
        ≅⟨ ≡-to-≅ $ π₂⨟ᴹ (σᴹ ↑ᴹ Aᴹ) idSᴹ ⟨
      tr TmᴹFam (cong ([_]ᴹ Aᴹ) (π₁⨟ᴹ (σᴹ ↑ᴹ Aᴹ) idSᴹ) ∙ [⨟]ᴹ) (π₂ᴹ ((σᴹ ↑ᴹ Aᴹ) ⨟ᴹ idSᴹ))
        ≅⟨ tr≅ TmᴹFam (cong ([_]ᴹ Aᴹ) (π₁⨟ᴹ (σᴹ ↑ᴹ Aᴹ) idSᴹ) ∙ [⨟]ᴹ) _ ⟩
      π₂ᴹ ((σᴹ ↑ᴹ Aᴹ) ⨟ᴹ idSᴹ)
        ≅⟨ hcong π₂ᴹ (≡-to-≅ $ (σᴹ ↑ᴹ Aᴹ) ⨟idSᴹ) ⟩
      π₂ᴹ ((π₁ᴹ idSᴹ ⨟ᴹ σᴹ) ,ˢᴹ tr TmᴹFam (sym [⨟]ᴹ) (π₂ᴹ idSᴹ))
        ≅⟨ tr≅ (TmᴹFam ∘ ([_]ᴹ Aᴹ)) π₁,ᴹ _ ⟨
      tr (TmᴹFam ∘ ([_]ᴹ Aᴹ)) π₁,ᴹ _
        ≅⟨ ≡-to-≅ $ π₂,ᴹ ⟩
      tr TmᴹFam (sym [⨟]ᴹ) (π₂ᴹ idSᴹ)
        ≅⟨ tr≅ TmᴹFam (sym [⨟]ᴹ) _ ⟩
      π₂ᴹ idSᴹ
        ∎
      where open ≅-Reasoning
    
    idS↑ᴹ
      : tr Subᴹ,ᶜᴹFam [idS]ᴹ (idSᴹ ↑ᴹ Aᴹ) ≡ idSᴹ
    idS↑ᴹ {Γᴹ} {_} {Aᴹ} = begin
      tr Subᴹ,ᶜᴹFam [idS]ᴹ
         ((π₁ᴹ idSᴹ ⨟ᴹ idSᴹ) ,ˢᴹ tr TmᴹFam (sym [⨟]ᴹ) (π₂ᴹ idSᴹ))
        ≡⟨ tr-nat (λ Bᴹ → Tmᴹ (Γᴹ ,ᶜᴹ Bᴹ) ([ π₁ᴹ idSᴹ ⨟ᴹ idSᴹ ]ᴹ Aᴹ))
                  (λ _ tᴹ → (π₁ᴹ idSᴹ ⨟ᴹ idSᴹ) ,ˢᴹ tᴹ)
                  [idS]ᴹ ⟩
      (π₁ᴹ idSᴹ ⨟ᴹ idSᴹ) ,ˢᴹ
        tr (λ Bᴹ → Tmᴹ (Γᴹ ,ᶜᴹ Bᴹ) ([ π₁ᴹ idSᴹ ⨟ᴹ idSᴹ ]ᴹ Aᴹ)) [idS]ᴹ
           (tr TmᴹFam (sym [⨟]ᴹ) (π₂ᴹ idSᴹ))
        ≡⟨ apd₂ (λ σᴹ tᴹ → σᴹ ,ˢᴹ tᴹ) (π₁ᴹ idSᴹ ⨟idSᴹ) eq ⟩
      π₁ᴹ idSᴹ ,ˢᴹ π₂ᴹ idSᴹ
        ≡⟨ sym η,ᴹ ⟩
      idSᴹ
        ∎
      where
        open ≡-Reasoning
        eq : tr (λ τᴹ → TmᴹFam ([ τᴹ ]ᴹ Aᴹ)) (π₁ᴹ idSᴹ ⨟idSᴹ)
                (tr (λ Bᴹ → Tmᴹ (Γᴹ ,ᶜᴹ Bᴹ) ([ π₁ᴹ idSᴹ ⨟ᴹ idSᴹ ]ᴹ Aᴹ)) [idS]ᴹ
                    (tr TmᴹFam (sym [⨟]ᴹ) (π₂ᴹ idSᴹ)))
           ≡ π₂ᴹ {Γᴹ ,ᶜᴹ Aᴹ} idSᴹ
        eq = ≅-to-≡ $
          HEq.trans (tr≅ (λ τᴹ → TmᴹFam ([ τᴹ ]ᴹ Aᴹ)) (π₁ᴹ idSᴹ ⨟idSᴹ)
                         (tr (λ Bᴹ → Tmᴹ (Γᴹ ,ᶜᴹ Bᴹ) ([ π₁ᴹ idSᴹ ⨟ᴹ idSᴹ ]ᴹ Aᴹ)) [idS]ᴹ
                             (tr TmᴹFam (sym [⨟]ᴹ) (π₂ᴹ idSᴹ))))
         (HEq.trans (tr≅ (λ Bᴹ → Tmᴹ (Γᴹ ,ᶜᴹ Bᴹ) ([ π₁ᴹ idSᴹ ⨟ᴹ idSᴹ ]ᴹ Aᴹ)) [idS]ᴹ
                         (tr TmᴹFam (sym [⨟]ᴹ) (π₂ᴹ idSᴹ)))
         (HEq.trans (tr≅ TmᴹFam (sym [⨟]ᴹ) (π₂ᴹ idSᴹ))
                    (hcong (λ Bᴹ → π₂ᴹ {Γᴹ ,ᶜᴹ Bᴹ} idSᴹ) (≡-to-≅ [idS]ᴹ))))
    
    ⨟↑ᴹ
      : tr Subᴹ,ᶜᴹFam [⨟]ᴹ ((σᴹ ⨟ᴹ τᴹ) ↑ᴹ Aᴹ) ≡ (σᴹ ↑ᴹ ([ τᴹ ]ᴹ Aᴹ)) ⨟ᴹ (τᴹ ↑ᴹ Aᴹ)
    ⨟↑ᴹ {Γᴹ} {Δᴹ} {σᴹ} {Θᴹ} {τᴹ} {i} {Aᴹ} = ≅-to-≡ $ begin
      tr Subᴹ,ᶜᴹFam [⨟]ᴹ
          ((π₁ᴹ idSᴹ ⨟ᴹ (σᴹ ⨟ᴹ τᴹ)) ,ˢᴹ tr TmᴹFam (sym [⨟]ᴹ) (π₂ᴹ {Aᴹ = [ σᴹ ⨟ᴹ τᴹ ]ᴹ Aᴹ} idSᴹ))
        ≡⟨ tr-nat (λ Bᴹ → Tmᴹ (Γᴹ ,ᶜᴹ Bᴹ) ([ π₁ᴹ idSᴹ ⨟ᴹ (σᴹ ⨟ᴹ τᴹ) ]ᴹ Aᴹ))
                  (λ _ tᴹ → (π₁ᴹ idSᴹ ⨟ᴹ (σᴹ ⨟ᴹ τᴹ)) ,ˢᴹ tᴹ) [⨟]ᴹ ⟩
      (π₁ᴹ idSᴹ ⨟ᴹ (σᴹ ⨟ᴹ τᴹ)) ,ˢᴹ
        tr (λ Bᴹ → Tmᴹ (Γᴹ ,ᶜᴹ Bᴹ) ([ π₁ᴹ idSᴹ ⨟ᴹ (σᴹ ⨟ᴹ τᴹ) ]ᴹ Aᴹ)) [⨟]ᴹ
           (tr TmᴹFam (sym [⨟]ᴹ) (π₂ᴹ idSᴹ))
        ≡⟨ eq ≡,≅ heq ⟩
      ((σᴹ ↑ᴹ ([ τᴹ ]ᴹ Aᴹ)) ⨟ᴹ (π₁ᴹ idSᴹ ⨟ᴹ τᴹ)) ,ˢᴹ
          tr TmᴹFam (sym [⨟]ᴹ)
             ([ σᴹ ↑ᴹ ([ τᴹ ]ᴹ Aᴹ) ]tmᴹ tr TmᴹFam (sym [⨟]ᴹ) (π₂ᴹ idSᴹ))
        ≡⟨ ⨟,ᴹ ⟨
      (σᴹ ↑ᴹ ([ τᴹ ]ᴹ Aᴹ)) ⨟ᴹ (τᴹ ↑ᴹ Aᴹ)
        ∎
      where
        open ≅-Reasoning
        _≡,≅_
          : ∀{Γᴹ Δᴹ i}{Aᴹ : Tyᴹ Δᴹ i}
            {σᴹ σ'ᴹ : Subᴹ Γᴹ Δᴹ}{tᴹ : Tmᴹ Γᴹ ([ σᴹ ]ᴹ Aᴹ)}{t'ᴹ : Tmᴹ Γᴹ ([ σ'ᴹ ]ᴹ Aᴹ)}
          → σᴹ ≡ σ'ᴹ → tᴹ ≅ t'ᴹ
          → _≡_ {A = Subᴹ Γᴹ (Δᴹ ,ᶜᴹ Aᴹ)} (σᴹ ,ˢᴹ tᴹ) (σ'ᴹ ,ˢᴹ t'ᴹ)
        refl ≡,≅ eq = cong (_ ,ˢᴹ_) (≅-to-≡ eq)

        eq : π₁ᴹ idSᴹ ⨟ᴹ (σᴹ ⨟ᴹ τᴹ) ≡ (σᴹ ↑ᴹ ([ τᴹ ]ᴹ Aᴹ)) ⨟ᴹ (π₁ᴹ idSᴹ ⨟ᴹ τᴹ)
        eq = ≅-to-≡ $ begin
          π₁ᴹ idSᴹ ⨟ᴹ (σᴹ ⨟ᴹ τᴹ)
            ≡⟨ ⨟-assocᴹ ⟩
          (π₁ᴹ idSᴹ ⨟ᴹ σᴹ) ⨟ᴹ τᴹ
            ≡⟨ cong (_⨟ᴹ τᴹ) (↑⨟wkᴹ σᴹ) ⟨
          ((σᴹ ↑ᴹ ([ τᴹ ]ᴹ Aᴹ)) ⨟ᴹ π₁ᴹ idSᴹ) ⨟ᴹ τᴹ
            ≡⟨ ⨟-assocᴹ ⟨
          (σᴹ ↑ᴹ ([ τᴹ ]ᴹ Aᴹ)) ⨟ᴹ (π₁ᴹ idSᴹ ⨟ᴹ τᴹ)
            ∎
        
        heq : tr (λ Bᴹ → Tmᴹ (Γᴹ ,ᶜᴹ Bᴹ) ([ π₁ᴹ idSᴹ ⨟ᴹ (σᴹ ⨟ᴹ τᴹ) ]ᴹ Aᴹ)) [⨟]ᴹ
                 (tr TmᴹFam (sym [⨟]ᴹ) (π₂ᴹ idSᴹ))
            ≅ tr TmᴹFam (sym [⨟]ᴹ)
                 ([ σᴹ ↑ᴹ ([ τᴹ ]ᴹ Aᴹ) ]tmᴹ tr TmᴹFam (sym [⨟]ᴹ) (π₂ᴹ idSᴹ))
        heq = begin
          tr (λ Bᴹ → Tmᴹ (Γᴹ ,ᶜᴹ Bᴹ) ([ π₁ᴹ idSᴹ ⨟ᴹ (σᴹ ⨟ᴹ τᴹ) ]ᴹ Aᴹ)) [⨟]ᴹ
             (tr TmᴹFam (sym [⨟]ᴹ) (π₂ᴹ idSᴹ))
            ≅⟨ tr≅ (λ Bᴹ → Tmᴹ (Γᴹ ,ᶜᴹ Bᴹ) ([ π₁ᴹ idSᴹ ⨟ᴹ (σᴹ ⨟ᴹ τᴹ) ]ᴹ Aᴹ)) [⨟]ᴹ
                   (tr TmᴹFam (sym [⨟]ᴹ) (π₂ᴹ idSᴹ)) ⟩
          tr TmᴹFam (sym [⨟]ᴹ) (π₂ᴹ idSᴹ)
            ≅⟨ tr≅ TmᴹFam (sym [⨟]ᴹ) (π₂ᴹ idSᴹ) ⟩
          π₂ᴹ {Aᴹ = [ σᴹ ⨟ᴹ τᴹ ]ᴹ Aᴹ} idSᴹ
            ≅⟨ hcong (λ Aᴹ → π₂ᴹ {Aᴹ = Aᴹ} idSᴹ) (≡-to-≅ [⨟]ᴹ) ⟩
          π₂ᴹ {Aᴹ = [ σᴹ ]ᴹ ([ τᴹ ]ᴹ Aᴹ)} idSᴹ
            ≅⟨ [↑]vzᴹ σᴹ ([ τᴹ ]ᴹ Aᴹ) ⟨
          [ σᴹ ↑ᴹ ([ τᴹ ]ᴹ Aᴹ) ]tmᴹ π₂ᴹ {Aᴹ = [ τᴹ ]ᴹ Aᴹ} idSᴹ
            ≅⟨ icong TmᴹFam [⨟]ᴹ ([ σᴹ ↑ᴹ ([ τᴹ ]ᴹ Aᴹ) ]tmᴹ_)
                     (tr≅ TmᴹFam (sym [⨟]ᴹ) _) ⟨
          [ σᴹ ↑ᴹ ([ τᴹ ]ᴹ Aᴹ) ]tmᴹ tr TmᴹFam (sym [⨟]ᴹ) (π₂ᴹ idSᴹ)
            ≅⟨ tr≅ TmᴹFam (sym [⨟]ᴹ) _ ⟨
          tr TmᴹFam (sym [⨟]ᴹ)
             ([ σᴹ ↑ᴹ ([ τᴹ ]ᴹ Aᴹ) ]tmᴹ tr TmᴹFam (sym [⨟]ᴹ) (π₂ᴹ idSᴹ))
            ∎
    
    π₁,↑ᴹ
      : tr Subᴹ,ᶜᴹFam (cong ([_]ᴹ Aᴹ) π₁,ᴹ) (π₁ᴹ (σᴹ ,ˢᴹ tᴹ) ↑ᴹ Aᴹ)
      ≡ σᴹ ↑ᴹ Aᴹ
    π₁,↑ᴹ {Aᴹ = Aᴹ} {σᴹ = σᴹ} {tᴹ = tᴹ} = begin
      tr Subᴹ,ᶜᴹFam (cong ([_]ᴹ Aᴹ) π₁,ᴹ) (π₁ᴹ (σᴹ ,ˢᴹ tᴹ) ↑ᴹ Aᴹ)
        ≡⟨ tr-cong {P = Subᴹ,ᶜᴹFam} π₁,ᴹ ⟨
      tr (Subᴹ,ᶜᴹFam ∘ [_]ᴹ Aᴹ) π₁,ᴹ (π₁ᴹ (σᴹ ,ˢᴹ tᴹ) ↑ᴹ Aᴹ)
        ≡⟨ apd (_↑ᴹ Aᴹ) π₁,ᴹ ⟩
      σᴹ ↑ᴹ Aᴹ
        ∎
      where open ≡-Reasoning

    π₁⨟↑ᴹ
      : tr Subᴹ,ᶜᴹFam (cong ([_]ᴹ Aᴹ) (π₁⨟ᴹ σᴹ τᴹ) ∙ [⨟]ᴹ)
           ((π₁ᴹ (σᴹ ⨟ᴹ τᴹ)) ↑ᴹ Aᴹ)
      ≡ (σᴹ ↑ᴹ ([ π₁ᴹ τᴹ ]ᴹ Aᴹ)) ⨟ᴹ (π₁ᴹ τᴹ ↑ᴹ Aᴹ)
    π₁⨟↑ᴹ {Aᴹ = Aᴹ} {σᴹ = σᴹ} {τᴹ = τᴹ} = begin
      tr Subᴹ,ᶜᴹFam (cong ([_]ᴹ Aᴹ) (π₁⨟ᴹ σᴹ τᴹ) ∙ [⨟]ᴹ)
         ((π₁ᴹ (σᴹ ⨟ᴹ τᴹ)) ↑ᴹ Aᴹ)
        ≡⟨ tr² (cong ([_]ᴹ Aᴹ) (π₁⨟ᴹ σᴹ τᴹ)) ⟨
      tr Subᴹ,ᶜᴹFam [⨟]ᴹ
        (tr Subᴹ,ᶜᴹFam (cong ([_]ᴹ Aᴹ) (π₁⨟ᴹ σᴹ τᴹ))
            ((π₁ᴹ (σᴹ ⨟ᴹ τᴹ)) ↑ᴹ Aᴹ))
        ≡⟨ cong (tr Subᴹ,ᶜᴹFam [⨟]ᴹ) (tr-cong (π₁⨟ᴹ σᴹ τᴹ)) ⟨
      tr Subᴹ,ᶜᴹFam [⨟]ᴹ
        (tr (Subᴹ,ᶜᴹFam ∘ ([_]ᴹ Aᴹ)) (π₁⨟ᴹ σᴹ τᴹ) ((π₁ᴹ (σᴹ ⨟ᴹ τᴹ)) ↑ᴹ Aᴹ))
        ≡⟨ cong (tr Subᴹ,ᶜᴹFam [⨟]ᴹ) (apd (_↑ᴹ Aᴹ) (π₁⨟ᴹ σᴹ τᴹ)) ⟩
      tr Subᴹ,ᶜᴹFam [⨟]ᴹ ((σᴹ ⨟ᴹ π₁ᴹ τᴹ) ↑ᴹ Aᴹ)
        ≡⟨ ⨟↑ᴹ ⟩
      (σᴹ ↑ᴹ ([ π₁ᴹ τᴹ ]ᴹ Aᴹ)) ⨟ᴹ (π₁ᴹ τᴹ ↑ᴹ Aᴹ)
        ∎
      where open ≡-Reasoning
  
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
        → [ σᴹ ]ᴹ (Elᴹ uᴹ)
        ≡ Elᴹ (tr TmᴹFam []Uᴹ ([ σᴹ ]tmᴹ uᴹ))
      []Liftᴹ
        : [ σᴹ ]ᴹ (Liftᴹ Aᴹ) ≡ Liftᴹ ([ σᴹ ]ᴹ Aᴹ)
      []tcᴹ
        : (σᴹ : Subᴹ Γᴹ Δᴹ)(Aᴹ : Tyᴹ Δᴹ i)
        → tr TmᴹFam []Uᴹ ([ σᴹ ]tmᴹ (cᴹ Aᴹ)) ≡ cᴹ ([ σᴹ ]ᴹ Aᴹ)
      []mkᴹ
        : (σᴹ : Subᴹ Γᴹ Δᴹ){Aᴹ : Tyᴹ Δᴹ i}(tᴹ : Tmᴹ Δᴹ Aᴹ)
        → tr TmᴹFam []Liftᴹ ([ σᴹ ]tmᴹ mkᴹ tᴹ) ≡ mkᴹ ([ σᴹ ]tmᴹ tᴹ)
      []unᴹ
        : (σᴹ : Subᴹ Γᴹ Δᴹ)(Aᴹ : Tyᴹ Δᴹ i)(tᴹ : Tmᴹ Δᴹ (Liftᴹ Aᴹ))
        → [ σᴹ ]tmᴹ unᴹ tᴹ ≡ unᴹ (tr TmᴹFam []Liftᴹ ([ σᴹ ]tmᴹ tᴹ))
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
        : [ σᴹ ]ᴹ Πᴹ Aᴹ Bᴹ ≡ Πᴹ ([ σᴹ ]ᴹ Aᴹ) ([ σᴹ ↑ᴹ Aᴹ ]ᴹ Bᴹ)
      []ƛᴹ
        : (σᴹ : Subᴹ Γᴹ Δᴹ)(tᴹ : Tmᴹ (Δᴹ ,ᶜᴹ Aᴹ) Bᴹ)
        → tr TmᴹFam []Πᴹ ([ σᴹ ]tmᴹ ƛᴹ tᴹ)
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
        : {σᴹ : Subᴹ Γᴹ Δᴹ}{aᴹ : Tmᴹ Δᴹ (Uᴹ i)}{tᴹ : Tmᴹ Δᴹ (Elᴹ aᴹ)}{uᴹ : Tmᴹ Δᴹ (Elᴹ aᴹ)}
        → [ σᴹ ]ᴹ (Idᴹ aᴹ tᴹ uᴹ)
        ≡ Idᴹ (tr TmᴹFam []Uᴹ ([ σᴹ ]tmᴹ aᴹ))
              (tr TmᴹFam ([]Elᴹ σᴹ aᴹ) ([ σᴹ ]tmᴹ tᴹ))
              (tr TmᴹFam ([]Elᴹ σᴹ aᴹ) ([ σᴹ ]tmᴹ uᴹ))
      reflᴹ
        : (tᴹ : Tmᴹ Γᴹ (Elᴹ aᴹ))
        → Tmᴹ Γᴹ (Idᴹ aᴹ tᴹ tᴹ)
      []reflᴹ
          : (σᴹ : Subᴹ Δᴹ Γᴹ){aᴹ : Tmᴹ Γᴹ (Uᴹ i)}(tᴹ : Tmᴹ Γᴹ (Elᴹ aᴹ))
          → tr (Tmᴹ Δᴹ) []Idᴹ ([ σᴹ ]tmᴹ (reflᴹ tᴹ))
          ≡ reflᴹ (tr TmᴹFam ([]Elᴹ σᴹ aᴹ) ([ σᴹ ]tmᴹ tᴹ))
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
