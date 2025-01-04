module SC+U+Pi.QIIRT.Coherence where

open import Prelude
  hiding (_,_)

open import SC+U+Pi.QIIRT.Base
open import SC+U+Pi.QIIRT.Properties

coh↑ : (σ τ : Sub Γ Δ) (A : Ty Δ i)
  → σ ≡ τ
  → σ ↑ A ≅ τ ↑ A
coh↑ {Γ} {Δ} σ τ A σ=τ = begin
  σ ↑ A ≅⟨ ≡-to-≅ $ ↑=⁺ A σ ⟩
  σ ⁺   ≅⟨ hcong (λ σ → σ ⁺) (≡-to-≅ σ=τ) ⟩
  τ ⁺   ≡⟨ ↑=⁺ A τ ⟨
  τ ↑ A ∎
  where open ≅-Reasoning
  
coh[idS⨟]
  : [ idS ⨟ σ ] A ≡ [ σ ] A
coh[idS⨟] = refl

coh[⨟idS]
  : [ σ ⨟ idS ] A ≡ [ σ ] A
coh[⨟idS] = refl

coh[assocS]
  : [ (σ ⨟ τ) ⨟ γ ] A ≡ [ σ ⨟ (τ ⨟ γ) ] A
coh[assocS] = refl

coh[⨟,]
  : (σ : Sub Γ Δ) (τ : Sub Δ Θ) (A : Ty Θ i) (t : Tm Δ ([ τ ] A)) (B : Ty (Θ , A) i)
  → [ σ ⨟ (τ , t) ] B ≅ [ (σ ⨟ τ) , [ σ ]t t ] B
coh[⨟,] σ τ A t (U i)   = refl
coh[⨟,] σ τ A t (Π B C) = hcong₂ Π
  (coh[⨟,] σ τ A t B)
  {!!}
coh[⨟,] σ τ A t (El u)  = hcong El $ begin
  [ σ ⨟ (τ , t) ]t u            ≅⟨ refl ⟩
  [ σ ]t  [ τ , t ]tm u         ≅⟨ ≡-to-≅ $ {![]tm≡[]t!} ⟨ -- []tm≡[]t _ _) ⟩
  [ σ ]tm [ τ , t ]tm u         ≅⟨ ≡-to-≅ $ [⨟]tm ⟨
  [ σ ⨟ (τ , t) ]tm u           ≅⟨ hcong (λ σ → [ σ ]tm u) (≡-to-≅ ⨟,) ⟩
  [ σ ⨟ τ , [ σ ]t t ]tm u      ∎
  where open ≅-Reasoning

coh[βπ₁] : [ π₁ (σ , t) ] A ≡ [ σ ] A
coh[βπ₁] = refl

module _ {Γ : Ctx} (σ : Sub Γ ∅) where
  open ≅-Reasoning
  coh[η∅]
    : (A : Ty ∅ i)
    → [ σ ] A ≅ [ (∅ {Γ}) ] A 

  coh[η∅] (U i)   = refl
  coh[η∅] (Π A B) = hcong₂ Π
    (coh[η∅] A)
    {!!}
    -- (icong₂ (λ σ → Sub (Γ , [ σ ] A) (∅ , A)) {i = σ} η∅ [_]_ (cong-↑ σ ∅ η∅) (refl {x = B}))
  coh[η∅]  (El u)  = hcong El $ begin
    [ σ ]t  u ≅⟨ {!!} ⟩ -- ≡-to-≅ (sym ([]tm≡[]t u σ)) ⟩
    [ σ ]tm u ≅⟨ hcong ([_]tm u) (≡-to-≅ η∅) ⟩
    [ ∅ ]tm u ∎

module _ {Γ Δ : Ctx} {A : Ty Δ i} (σ : Sub Γ (Δ , A)) where 
  open ≅-Reasoning
  coh[η,] 
    : (B : Ty (Δ , A) i)
    → [ σ ] B ≅ [ π₁ σ , π₂ σ ] B
  coh[η,] (U i)   = refl
  coh[η,] (Π B C) = hcong₂ Π
    (coh[η,] B)
    {!!}
    -- (icong₂ (λ σ → Sub (Γ , [ σ ] B) (Δ , A , B)) {i = σ} η, [_]_ (cong-↑ σ (π₁ σ , π₂ σ) η,) (refl {x = C}))
  coh[η,] (El u)  = hcong El $ begin
    [ σ ]t            u ≅⟨ {!!} ⟨ -- ≡-to-≅ (sym ([]tm≡[]t u σ)) ⟩
    [ σ ]tm           u ≅⟨ hcong ([_]tm u) (≡-to-≅ η,) ⟩
    [ π₁ σ , π₂ σ ]tm u ∎

-- -- Coherence property for the term substitution
-- module _ {Γ Δ : Ctx} {A : Ty Δ i} {t u : Tm Δ A} {σ γ : Sub Γ Δ} where
--   open ≅-Reasoning
--   coh[σ]tm
--     : σ ≅ γ → t ≅ u → [ σ ]t t ≅ [ γ ]t u
--   coh[σ]tm σ=γ t=u = begin
--     [ σ ]t  t ≅⟨ ≡-to-≅ (sym ([]tm≡[]t t σ)) ⟩
--     [ σ ]tm t ≅⟨ hcong₂ (λ σ t → [ σ ]tm t) σ=γ t=u ⟩
--     [ γ ]tm u ≅⟨ ≡-to-≅ ([]tm≡[]t u γ) ⟩
--     [ γ ]t  u ∎

-- coh↑ : (σ τ : Sub Γ Δ) (A : Ty Δ i)
--   → σ ≡ τ
--   → σ ↑ A ≅ τ ↑ A
-- coh↑ σ τ A σ=τ = begin
--   σ ↑ A ≅⟨ ≡-to-≅ $ ↑=⁺ A σ ⟩
--   σ ⁺   ≅⟨ {!!} ⟩
--   τ ⁺   ≅⟨ ≡-to-≅ $ ↑=⁺ A τ ⟨
--   τ ↑ A ∎
--   where open ≅-Reasoning
