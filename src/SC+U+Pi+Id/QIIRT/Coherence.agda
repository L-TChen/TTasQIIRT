module SC+U+Pi+Id.QIIRT.Coherence where

open import Prelude
  hiding (_,_)

open import SC+U+Pi+Id.QIIRT.Base
open import SC+U+Pi+Id.QIIRT.Properties

coh↑ : (σ τ : Sub Γ Δ) (A : Ty Δ i)
  → σ ≡ τ
  → σ ↑ A ≅ τ ↑ A
coh↑ {Γ} {Δ} σ τ A σ=τ = begin
  σ ↑ A ≅⟨ ≡-to-≅ $ ↑=⁺ A σ ⟩
  σ ⁺   ≅⟨ hcong (λ σ → σ ⁺) (≡-to-≅ σ=τ) ⟩
  τ ⁺   ≡⟨ ↑=⁺ A τ ⟨
  τ ↑ A ∎
  where open ≅-Reasoning
  
-- Coherence property for the term substitution
module _ {Γ Δ : Ctx} {A : Ty Δ i} {t u : Tm Δ A} {σ γ : Sub Γ Δ} where
  open ≅-Reasoning
  coh[σ]tm
    : σ ≅ γ → t ≅ u → [ σ ]t t ≅ [ γ ]t u
  coh[σ]tm σ=γ t=u = begin
    [ σ ]t  t ≅⟨ ≡-to-≅ $ []tm≡[]t t σ ⟨
    [ σ ]tm t ≅⟨ hcong₂ (λ σ t → [ σ ]tm t) σ=γ t=u ⟩
    [ γ ]tm u ≡⟨ []tm≡[]t u γ ⟩
    [ γ ]t  u ∎
  
coh[idS⨟]
  : [ idS ⨟ σ ] A ≡ [ σ ] A
coh[idS⨟] = refl

coh[⨟idS]
  : [ σ ⨟ idS ] A ≡ [ σ ] A
coh[⨟idS] = refl

coh[assocS]
  : [ (σ ⨟ τ) ⨟ γ ] A ≡ [ σ ⨟ (τ ⨟ γ) ] A
coh[assocS] = refl

module _ (σ : Sub Γ Δ) (τ : Sub Δ Θ) {i : ℕ} (A : Ty Θ i) (t : Tm Δ ([ τ ] A)) where
  open ≅-Reasoning
  coh[⨟,]l
    : (Ξ : Tel (Θ , A))
    → [ σ ⨟ (τ , t) ]l Ξ ≅ [ σ ⨟ τ , [ σ ]tm t ]l Ξ
  coh[⨟,]'
    : (Ξ : Tel (Θ , A))
    → [ σ ⨟ (τ , t) ]l Ξ ≅ [ σ ⨟ τ , [ σ ]tm t ]l Ξ
    → (B : Ty ((Θ , A) ⧺ Ξ) j)
    → [ (σ ⨟ (τ , t)) ⇈ Ξ ] B ≅ [ ((σ ⨟ τ) , [ σ ]tm t) ⇈ Ξ ] B
  coh[⨟,]l ∅       = refl
  coh[⨟,]l (Ξ , B) = hcong₂ _,_ (coh[⨟,]l Ξ) (coh[⨟,]' Ξ (coh[⨟,]l Ξ) B)

  coh[⨟,]' Ξ eq (U j)      = cong-U (hcong (Γ ⧺_) eq)
  coh[⨟,]' Ξ eq (El u)     = icong (λ Γ → Tm Γ (U _)) (cong (Γ ⧺_) (≅-to-≡ eq)) El $ begin
    [ (σ ⨟ (τ , t)) ⇈ Ξ ]t u
      ≅⟨ ≡-to-≅ ([]tm≡[]t u ((σ ⨟ (τ , t)) ⇈ Ξ)) ⟨
    [ (σ ⨟ (τ , t)) ⇈ Ξ ]tm u
      ≅⟨ icong (λ σ → Sub (_ ⧺ [ σ ]l Ξ) (_ ⧺ Ξ)) ⨟, ([_]tm u) (⨟,⇈ Ξ) ⟩
    [ (σ ⨟ τ , [ σ ]tm t) ⇈ Ξ ]tm u
      ≡⟨ []tm≡[]t u ((σ ⨟ τ , [ σ ]tm t) ⇈ Ξ) ⟩
    [ (σ ⨟ τ , [ σ ]tm t) ⇈ Ξ ]t u
      ∎
  coh[⨟,]' Ξ eq (Lift B)   = icong (λ Γ → Ty Γ _) (cong (Γ ⧺_) (≅-to-≡ eq)) Lift $ begin
    [ (σ ⨟ (τ , t)) ⇈ Ξ ] B
      ≅⟨ coh[⨟,]' Ξ eq B ⟩
    [ ((σ ⨟ τ) , [ σ ]tm t) ⇈ Ξ ] B
      ∎
  coh[⨟,]' Ξ eq (Π B C)    = icong₂ (λ Γ → Ty Γ _) (cong (Γ ⧺_) (≅-to-≡ eq)) Π
    (coh[⨟,]' Ξ eq B)
    (coh[⨟,]' (Ξ , B) (hcong₂ _,_ eq (coh[⨟,]' Ξ eq B)) C)
  coh[⨟,]' Ξ eq (Id a u v) = {!!} -- we need icong₃

  coh[⨟,]
    : (Ξ : Tel (Θ , A))
    → (B : Ty ((Θ , A) ⧺ Ξ) j)
    → [ (σ ⨟ (τ , t)) ⇈ Ξ ] B ≅ [ ((σ ⨟ τ) , [ σ ]tm t) ⇈ Ξ ] B
  coh[⨟,] Ξ B = coh[⨟,]' Ξ (coh[⨟,]l Ξ) B

coh[βπ₁] : [ π₁ (σ , t) ] A ≡ [ σ ] A
coh[βπ₁] = refl

module _ {Γ : Ctx} (σ : Sub Γ ∅) where
  open ≅-Reasoning

  coh[η∅]l : (Ξ : Tel ∅)
    → [ σ ]l Ξ ≅ [ ∅ {Γ} ]l Ξ
  coh[η∅]' : (Ξ : Tel ∅)
    → [ σ ]l Ξ ≅ [ ∅ {Γ} ]l Ξ
    → (A : Ty (∅ ⧺ Ξ) i)
    → [ σ ⇈ Ξ ] A ≅ [ (∅ {Γ}) ⇈ Ξ ] A

  coh[η∅]l ∅       = refl
  coh[η∅]l (Ξ , A) = hcong₂ _,_ (coh[η∅]l Ξ) (coh[η∅]' Ξ (coh[η∅]l Ξ) A)

  coh[η∅]' Ξ eq (U i)      = cong-U (hcong (Γ ⧺_) eq)
  coh[η∅]' Ξ eq (El u)     = icong (λ Γ → Tm Γ (U _)) (cong (Γ ⧺_) (≅-to-≡ eq)) El $ begin
    [ σ ⇈ Ξ ]t u
      ≅⟨ ≡-to-≅ ([]tm≡[]t u (σ ⇈ Ξ)) ⟨
    [ σ ⇈ Ξ ]tm u
      ≅⟨ icong (λ σ → Sub (_ ⧺ [ σ ]l Ξ) (∅ ⧺ Ξ)) η∅ ([_]tm u) (η∅⇈ Ξ) ⟩ 
    [ ∅ ⇈ Ξ ]tm u
      ≡⟨ []tm≡[]t u (∅ ⇈ Ξ) ⟩ 
    [ ∅ ⇈ Ξ ]t u ∎
  coh[η∅]' Ξ eq (Lift A)   = icong (λ Γ → Ty Γ _) (cong (Γ ⧺_) (≅-to-≡ eq)) Lift (coh[η∅]' Ξ eq A)
  coh[η∅]' Ξ eq (Π B C)    = icong₂ (λ Γ → Ty Γ _) (cong (Γ ⧺_) (≅-to-≡ eq)) Π
    (coh[η∅]' Ξ eq B)
    (coh[η∅]' (Ξ , B) (hcong₂ _,_ eq (coh[η∅]' Ξ eq B)) C)
  coh[η∅]' Ξ eq (Id a t u) = {!!}

  coh[η∅] : (Ξ : Tel ∅)
    → (A : Ty (∅ ⧺ Ξ) i)
    → [ σ ⇈ Ξ ] A ≅ [ (∅ {Γ}) ⇈ Ξ ] A
  coh[η∅] Ξ A = coh[η∅]' Ξ (coh[η∅]l Ξ) A

module _ {Γ Δ : Ctx} {A : Ty Δ i} (σ : Sub Γ (Δ , A)) where
  open ≅-Reasoning

  coh[η,]l
    : (Ξ : Tel (Δ , A)) → [ σ ]l Ξ ≅ [ π₁ σ , π₂ σ ]l Ξ
   
  coh[η,]'
    : (Ξ : Tel (Δ , A))
    → [ σ ]l Ξ ≅ [ π₁ σ , π₂ σ ]l Ξ
    → (B : Ty ((Δ , A) ⧺ Ξ) j)
    → [ σ ⇈ Ξ ] B ≅ [ (π₁ σ , π₂ σ) ⇈ Ξ ] B
  coh[η,]' Ξ eq (U i)      = cong-U (hcong (Γ ⧺_) eq)
  coh[η,]' Ξ eq (El u)     = icong (λ Γ → Tm Γ _) (≅-to-≡ $ hcong (Γ ⧺_) eq) El $ begin
    [ σ ⇈ Ξ ]t u
      ≅⟨ ≡-to-≅ $ []tm≡[]t u (σ ⇈ Ξ) ⟨
    [ σ ⇈ Ξ ]tm u
      ≅⟨ icong (λ σ → Sub (_ ⧺ [ σ ]l Ξ) (_ ⧺ Ξ)) η, ([_]tm u) (η,⇈ Ξ) ⟩
    [ (π₁ σ , π₂ σ) ⇈ Ξ ]tm u
      ≡⟨ []tm≡[]t u ((π₁ σ , π₂ σ) ⇈ Ξ) ⟩
    [ (π₁ σ , π₂ σ) ⇈ Ξ ]t u
      ∎
  coh[η,]' Ξ eq (Lift B)   = icong (λ Γ → Ty Γ _) (≅-to-≡ $ hcong (Γ ⧺_) eq) Lift $ begin 
    [ σ ⇈ Ξ ] B
      ≅⟨ coh[η,]' Ξ eq B ⟩
    [ (π₁ σ , π₂ σ) ⇈ Ξ ] B
      ∎
  coh[η,]' Ξ eq (Π B C)    = icong₂ (λ Γ → Ty Γ _) (cong (Γ ⧺_) (≅-to-≡ eq)) Π
    (coh[η,]' Ξ eq B)
    (coh[η,]' (Ξ , B) (hcong₂ _,_ eq (coh[η,]' Ξ eq B)) C)
  coh[η,]' Ξ eq (Id a t u) = {!!}

  coh[η,]l ∅       = refl
  coh[η,]l (Ξ , A) = hcong₂ _,_ (coh[η,]l Ξ) (coh[η,]' Ξ (coh[η,]l Ξ) A)

  coh[η,]
    : (Ξ : Tel (Δ , A)) (B : Ty ((Δ , A) ⧺ Ξ) i)
    → [ σ ⇈ Ξ ] B ≅ [ (π₁ σ , π₂ σ) ⇈ Ξ ] B
  coh[η,] Ξ B = coh[η,]' Ξ (coh[η,]l Ξ) B
