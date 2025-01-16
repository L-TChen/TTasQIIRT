module Theory.SC+El+Pi+Id.QIIRT.Coherence where

open import Prelude
  hiding (_,_)

open import Theory.SC+El+Pi+Id.QIIRT.Syntax
open import Theory.SC+El+Pi+Id.QIIRT.Properties

coh↑ : (σ τ : Sub Γ Δ) (A : Ty Δ)
  → σ ≡ τ
  → σ ↑ A ≅ τ ↑ A
coh↑ σ τ A σ=τ = begin
  σ ↑ A ≅⟨ ≡-to-≅ $ ↑=⁺ A σ ⟩
  σ ⁺   ≅⟨ hcong (λ σ → σ ⁺) (≡-to-≅ σ=τ) ⟩
  τ ⁺   ≡⟨ ↑=⁺ A τ ⟨
  τ ↑ A ∎
  where open ≅-Reasoning
  
-- Coherence property for the term substitution
module _ {Γ Δ : Ctx} {σ γ : Sub Γ Δ} where
  open ≅-Reasoning
  coh[]tm
    : {A : Ty Δ} {t : Tm Δ A} → σ ≅ γ → [ σ ]t t ≅ [ γ ]t t
  coh[]tm {A} {t} σ=γ = begin
    [ σ ]t  t ≅⟨ ≡-to-≅ $ []tm≡[]t t σ ⟨
    [ σ ]tm t ≅⟨ hcong (λ σ → [ σ ]tm t) σ=γ ⟩
    [ γ ]tm t ≡⟨ []tm≡[]t t γ ⟩
    [ γ ]t  t ∎

  coh[⇈]tm
    : (Ξ : Tel Δ) {A : Ty (Δ ⧺ Ξ)} {t : Tm (Δ ⧺ Ξ) A}
    → σ ≡ γ
    → [ σ ⇈ Ξ ]t t ≅ [ γ ⇈ Ξ ]t t
  coh[⇈]tm Ξ {A} {t} σ=γ = begin
    [ σ ⇈ Ξ ]t  t ≅⟨ ≡-to-≅ $ []tm≡[]t t _ ⟨
    [ σ ⇈ Ξ ]tm t ≅⟨ icong (λ σ → Sub (_ ⧺ [ σ ]l Ξ) (_ ⧺ Ξ)) σ=γ ([_]tm t) (⇈-cong σ=γ Ξ) ⟩
    [ γ ⇈ Ξ ]tm t ≡⟨ []tm≡[]t t _ ⟩
    [ γ ⇈ Ξ ]t  t ∎
  
coh[idS⨟]
  : [ idS ⨟ σ ] A ≡ [ σ ] A
coh[idS⨟] = refl

coh[⨟idS]
  : [ σ ⨟ idS ] A ≡ [ σ ] A
coh[⨟idS] = refl

coh[assocS]
  : [ (σ ⨟ τ) ⨟ γ ] A ≡ [ σ ⨟ (τ ⨟ γ) ] A
coh[assocS] = refl

module _ (σ : Sub Γ Δ) (τ : Sub Δ Θ) (A : Ty Θ) (t : Tm Δ ([ τ ] A)) where
  open ≅-Reasoning
  coh[⨟,]l
    : (Ξ : Tel (Θ , A))
    → [ σ ⨟ (τ , t) ]l Ξ ≅ [ σ ⨟ τ , [ σ ]t t ]l Ξ
  coh[⨟,]'
    : (Ξ : Tel (Θ , A))
    → [ σ ⨟ (τ , t) ]l Ξ ≅ [ σ ⨟ τ , [ σ ]t t ]l Ξ
    → (B : Ty ((Θ , A) ⧺ Ξ))
    → [ (σ ⨟ (τ , t)) ⇈ Ξ ] B ≅ [ ((σ ⨟ τ) , [ σ ]t t) ⇈ Ξ ] B
  coh[⨟,]l ∅       = refl
  coh[⨟,]l (Ξ , B) = hcong₂ _,_ (coh[⨟,]l Ξ) (coh[⨟,]' Ξ (coh[⨟,]l Ξ) B)

  coh[⨟,]' Ξ eq U      = cong-U (hcong (Γ ⧺_) eq)
  coh[⨟,]' Ξ eq (El u)     = icong (λ Γ → Tm Γ U) (cong (Γ ⧺_) (≅-to-≡ eq)) El
    (coh[⇈]tm Ξ ⨟,)
  coh[⨟,]' Ξ eq (Π B C)    = icong₂ Ty (cong (Γ ⧺_) (≅-to-≡ eq)) Π
    (coh[⨟,]' Ξ eq B)
    (coh[⨟,]' (Ξ , B) (hcong₂ _,_ eq (coh[⨟,]' Ξ eq B)) C)
  coh[⨟,]' Ξ eq (Id a u v) = icong₃ (λ Γ → Tm Γ _) (cong (Γ ⧺_) (≅-to-≡ eq)) Id
    (coh[⇈]tm Ξ ⨟,) (coh[⇈]tm Ξ ⨟,) (coh[⇈]tm Ξ ⨟,)

  coh[⨟,]
    : (Ξ : Tel (Θ , A))
    → (B : Ty ((Θ , A) ⧺ Ξ))
    → [ (σ ⨟ (τ , t)) ⇈ Ξ ] B ≅ [ ((σ ⨟ τ) , [ σ ]t t) ⇈ Ξ ] B
  coh[⨟,] Ξ B = coh[⨟,]' Ξ (coh[⨟,]l Ξ) B

coh[βπ₁] : [ π₁ (σ , t) ] A ≡ [ σ ] A
coh[βπ₁] = refl

module _ {Γ : Ctx} (σ : Sub Γ ∅) where
  open ≅-Reasoning

  coh[η∅]l : (Ξ : Tel ∅)
    → [ σ ]l Ξ ≅ [ ∅ {Γ} ]l Ξ
  coh[η∅]' : (Ξ : Tel ∅)
    → [ σ ]l Ξ ≅ [ ∅ {Γ} ]l Ξ
    → (A : Ty (∅ ⧺ Ξ))
    → [ σ ⇈ Ξ ] A ≅ [ (∅ {Γ}) ⇈ Ξ ] A

  coh[η∅]l ∅       = refl
  coh[η∅]l (Ξ , A) = hcong₂ _,_ (coh[η∅]l Ξ) (coh[η∅]' Ξ (coh[η∅]l Ξ) A)

  coh[η∅]' Ξ eq U      = cong-U (hcong (Γ ⧺_) eq)
  coh[η∅]' Ξ eq (El u)     = icong (λ Γ → Tm Γ U) (cong (Γ ⧺_) (≅-to-≡ eq)) El (coh[⇈]tm Ξ η∅)
  coh[η∅]' Ξ eq (Π B C)    = icong₂ (λ Γ → Ty Γ) (cong (Γ ⧺_) (≅-to-≡ eq)) Π
    (coh[η∅]' Ξ eq B)
    (coh[η∅]' (Ξ , B) (hcong₂ _,_ eq (coh[η∅]' Ξ eq B)) C)
  coh[η∅]' Ξ eq (Id a t u) = icong₃ (λ Γ → Tm Γ _) (cong (Γ ⧺_) (≅-to-≡ eq)) Id
    (coh[⇈]tm Ξ η∅) (coh[⇈]tm Ξ η∅) (coh[⇈]tm Ξ η∅)

  coh[η∅] : (Ξ : Tel ∅)
    → (A : Ty (∅ ⧺ Ξ))
    → [ σ ⇈ Ξ ] A ≅ [ (∅ {Γ}) ⇈ Ξ ] A
  coh[η∅] Ξ A = coh[η∅]' Ξ (coh[η∅]l Ξ) A

module _ {Γ Δ : Ctx} {A : Ty Δ} (σ : Sub Γ (Δ , A)) where
  open ≅-Reasoning

  coh[η,]l
    : (Ξ : Tel (Δ , A)) → [ σ ]l Ξ ≅ [ π₁ σ , π₂ σ ]l Ξ
   
  coh[η,]'
    : (Ξ : Tel (Δ , A))
    → [ σ ]l Ξ ≅ [ π₁ σ , π₂ σ ]l Ξ
    → (B : Ty ((Δ , A) ⧺ Ξ))
    → [ σ ⇈ Ξ ] B ≅ [ (π₁ σ , π₂ σ) ⇈ Ξ ] B

  coh[η,]' Ξ eq U      = cong-U (hcong (Γ ⧺_) eq)
  coh[η,]' Ξ eq (El u)     = icong  (λ Γ → Tm Γ _) (≅-to-≡ $ hcong (Γ ⧺_) eq) El (coh[⇈]tm Ξ η,)
  coh[η,]' Ξ eq (Π B C)    = icong₂ (λ Γ → Ty Γ) (cong (Γ ⧺_) (≅-to-≡ eq)) Π
    (coh[η,]' Ξ eq B)
    (coh[η,]' (Ξ , B) (hcong₂ _,_ eq (coh[η,]' Ξ eq B)) C)
  coh[η,]' Ξ eq (Id a t u) = icong₃ (λ Γ → Tm Γ _) (cong (Γ ⧺_) (≅-to-≡ eq)) Id
    (coh[⇈]tm Ξ η,) (coh[⇈]tm Ξ η,) (coh[⇈]tm Ξ η,)

  coh[η,]l ∅       = refl
  coh[η,]l (Ξ , A) = hcong₂ _,_ (coh[η,]l Ξ) (coh[η,]' Ξ (coh[η,]l Ξ) A)

  coh[η,]
    : (Ξ : Tel (Δ , A)) (B : Ty ((Δ , A) ⧺ Ξ))
    → [ σ ⇈ Ξ ] B ≅ [ (π₁ σ , π₂ σ) ⇈ Ξ ] B
  coh[η,] Ξ B = coh[η,]' Ξ (coh[η,]l Ξ) B
