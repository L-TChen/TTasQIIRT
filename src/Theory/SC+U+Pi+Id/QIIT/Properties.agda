open import Prelude
  
module Theory.SC+U+Pi+Id.QIIT.Properties where

open import Theory.SC+U+Pi+Id.QIIT.Syntax

cong-U : Γ ≅ Δ → U {Γ} i ≅ U {Δ} i
cong-U refl = refl

[]tapp : (σ : Sub Γ Δ)
  → (A : Ty Δ i) (B : Ty (Δ , A) i) (t : Tm Δ (Π A B))
  → app (tr (Tm Γ) []Π ([ σ ]tm t)) ≡ [ σ ⁺ ]tm app t
[]tapp {Γ} σ A B t = begin
  app (tr (Tm Γ) []Π ([ σ ]tm t))
    ≡⟨ cong (λ z → app (tr (Tm Γ) []Π ([ σ ]tm z))) (sym Πη) ⟩
  app (tr (Tm Γ) []Π ([ σ ]tm (ƛ app t)))
    ≡⟨ cong app ([]ƛ σ (app t)) ⟩
  app (ƛ ([ σ ⁺ ]tm app t))
    ≡⟨ Πβ ⟩
  [ σ ⁺ ]tm app t
    ∎
  where open ≡-Reasoning

π,
  : (σ : Sub Γ Δ) (t : Tm Γ ([ σ ] A))
  → _≡_ {_} {A = Σ (Sub Γ Δ) (λ σ → Tm Γ ([ σ ] A))}
  (π₁ (σ , t) , π₂ (σ , t))
  (σ , t)
π, σ t = begin
  π₁ (σ , t) , π₂ (σ , t)
    ≡⟨ Σ-≡,≡→≡ (π₁, , π₂,) ⟩
  σ , t
    ∎
  where open ≡-Reasoning

π⨟
  : (σ : Sub Γ Δ) (τ : Sub Δ (Θ , A))
  → _≡_ {A = Σ (Sub Γ Θ) (λ σ → Tm Γ ([ σ ] A))}
    (π₁ (σ ⨟ τ) , π₂ (σ ⨟ τ))
    (σ ⨟ π₁ τ , tr (Tm Γ) (sym $ [⨟]) ([ σ ]tm (π₂ τ)))
π⨟ {Γ} {Δ} {Θ} {i} {A} σ τ = begin
  π₁ (σ ⨟ τ) , π₂ (σ ⨟ τ)
    ≡⟨ apΣ (λ σ → Tm Γ ([ σ ] A)) (λ τ → π₁ (σ ⨟ τ)) (apdΣ (λ τ → π₂ (σ ⨟ τ)) η,) ⟩
  π₁ (σ ⨟ (π₁ τ , π₂ τ)) , π₂ (σ ⨟ (π₁ τ , π₂ τ))
    ≡⟨ apΣ (λ σ → Tm Γ ([ σ ] A)) π₁ (apdΣ π₂ ⨟,) ⟩
  let t = tr (Tm Γ) (sym $ [⨟]) ([ σ ]tm (π₂ τ)) in
  π₁ (σ ⨟ π₁ τ , t) , π₂ (σ ⨟ π₁ τ , t)
    ≡⟨ π, (σ ⨟ π₁ τ) t ⟩
  σ ⨟ π₁ τ , t
    ∎
  where open ≡-Reasoning

-- derived computation rules on composition
opaque 
  π₁⨟ : (σ : Sub Γ Δ) (τ : Sub Δ (Θ , A)) → π₁ (σ ⨟ τ) ≡ σ ⨟ π₁ τ
  π₁⨟ σ τ = Σ-≡,≡←≡ (π⨟ σ τ) .proj₁

π₂⨟ : (σ : Sub Γ Δ) {A : Ty Θ i} (τ : Sub Δ (Θ , A))
  → _≡_ {_} {∃ (Tm Γ)}
  ([ π₁ (σ ⨟ τ) ] A , π₂ (σ ⨟ τ))
  ([ σ ] [ π₁ τ ] A , [ σ ]tm (π₂ τ))
π₂⨟ {Γ} σ {A} τ = begin
  [ π₁ (σ ⨟ τ) ] A , π₂ (σ ⨟ τ)
    ≡⟨ apΣ (Tm Γ) ([_] A) (π⨟ σ τ) ⟩ 
  [ σ ⨟ π₁ τ ] A , tr (Tm Γ) (sym $ [⨟]) ([ σ ]tm π₂ τ)
    ≡⟨ (sym $ lift (Tm Γ) ([ σ ]tm π₂ τ) (sym [⨟])) ⟩ 
  [ σ ] [ π₁ τ ] A , [ σ ]tm (π₂ τ)
    ∎
  where open ≡-Reasoning

⨟π₁id  : (σ : Sub Γ (Δ , A)) → π₁ σ ≡ σ ⨟ π₁ idS
⨟π₁id σ = begin
  π₁ σ         ≡⟨ sym $ cong π₁ (σ ⨟idS) ⟩
  π₁ (σ ⨟ idS) ≡⟨ π₁⨟ σ idS ⟩
  σ ⨟ π₁ idS   ∎
  where open ≡-Reasoning

⨟π₂id : (σ : Sub Γ (Δ , A)) 
  → _≡_ {_} {∃ (Tm Γ)}
  ([ π₁ σ ] A , π₂ σ)
  ([ σ ] [ wk ] A , [ σ ]tm vz)
⨟π₂id {Γ} {Δ} {i} {A} σ = begin
  [ π₁ σ ] A , π₂ σ
    ≡⟨ apΣ (Tm Γ) (λ σ → [ π₁ σ ] A) (apdΣ π₂ (sym $ σ ⨟idS)) ⟩
  [ π₁ (σ ⨟ idS) ] A , π₂ (σ ⨟ idS)
    ≡⟨ π₂⨟ σ idS ⟩
  [ σ ] [ wk ] A , [ σ ]tm vz
    ∎
  where open ≡-Reasoning

⁺⨟wk : (σ : Sub Γ Δ) {A : Ty Δ i} → (_⁺ σ {A}) ⨟ wk ≡ wk ⨟ σ
⁺⨟wk {Γ} {Δ} σ {A} = begin
  σ ⁺ ⨟ π₁ idS                   ≡⟨ (sym $ ⨟π₁id (σ ⁺)) ⟩
  π₁ (σ ⁺)                       ≡⟨⟩
  π₁ (π₁ idS ⨟ σ , tr (Tm (Γ , [ σ ] A)) (sym [⨟]) vz) ≡⟨ π₁, ⟩
  π₁ idS ⨟ σ ∎
  where open ≡-Reasoning

{-
[⁺]vz : (σ : Sub Γ Δ) (A : Ty Δ i) → [ _⁺ σ {A} ]tm vz ≅ vz
[⁺]vz σ A = begin
  [ σ ⁺ ]tm (π₂ idS)
    ≅⟨ ≡-to-≅ ? ⟨
  π₂ (σ ⁺ ⨟ idS)
    ≅⟨ ? ⟩ -- hcong π₂ (≡-to-≅ (σ ⁺ ⨟idS)) ⟩
  π₂ (σ ⁺)
    ≡⟨ ? ⟩ -- π₂,u ⟩
  π₂ idS
    ∎
  where open ≅-Reasoning
-}
  

opaque
  id⁺
    : (Γ : Ctx) (A : Ty Γ i)
    → tr (λ B → Sub (Γ , B) (Γ , A)) [idS] (idS ⁺)
    ≡ idS {Γ , A}
  id⁺ Γ A = begin
    tr (λ B → Sub (Γ , B) (Γ , A)) [idS] (idS ⁺)
      ≡⟨⟩
    tr (λ B → Sub (Γ , B) (Γ , A)) [idS]
      (wk ⨟ idS , tr (Tm _) (sym [⨟]) (π₂ idS))
      ≡⟨ {!!} ⟩
    wk , π₂ idS
      ≡⟨ sym $ η, ⟩
    idS
      ∎
    where open ≡-Reasoning

  ⨟⁺
    : tr (λ A → Sub (Γ , A) (Δ , B)) [⨟] ((σ ⨟ τ) ⁺) ≡ σ ⁺ ⨟ τ ⁺
  ⨟⁺ = {!!}
  
-- σ⨟τ↑ : (σ : Sub Γ Δ) (τ : Sub Δ Θ) (A : Ty Θ i) → σ ⁺ ⨟ τ ⁺ ≡ (σ ⨟ τ) ⁺
-- σ⨟τ↑ {Γ} {Δ} {Θ} σ τ A = sym $ begin
--   (σ ⨟ τ) ⁺                    ≡⟨⟩
--   wk ⨟ (σ ⨟ τ) , vz            ≡⟨ ≅-to-≡ (hcong₂ (λ σ t → _,_ σ {A} t) (≡-to-≅ ⨟-assoc) refl) ⟩
--   (wk ⨟ σ) ⨟ τ , vz            ≡⟨ ≅-to-≡ $ hcong₂
--                                    {A = Sub (Γ , [ σ ⨟ τ ] A) Δ}
--                                    {B = λ γ → Tm (Γ , [ σ ] [ τ ] A)
--                                    ([ γ ] [ τ ] A)} (λ σ t → _,_ (σ ⨟ τ) {A} t) (≡-to-≅ (⁺⨟wk σ))
--                                    ([⁺]vz σ ([ τ ] A)) ⟨
--   (_⁺ σ {[ τ ] A} ⨟ wk) ⨟ τ , [ _⁺ σ {[ τ ] A} ]t vz
--     ≡⟨ ≅-to-≡ $ hcong₂ (λ σ t → _,_ σ {A} t) (≡-to-≅ ⨟-assoc) refl ⟨
--   σ ⁺ ⨟ (wk ⨟ τ) , [ _⁺ σ {[ τ ] A} ]t vz ≡⟨ ⨟, ⟨
--   σ ⁺ ⨟ ((wk ⨟ τ) , vz)                   ≡⟨⟩
--   σ ⁺ ⨟ τ ⁺                               ∎
--   where open ≡-Reasoning

  π₁,⁺
    : tr (λ A → Sub (Γ , A) (Δ , B)) (cong ([_] B) π₁,) (π₁ (σ , t) ⁺)
    ≡ σ ⁺ 
  π₁,⁺ {Γ} {Δ} {i} {B} {σ} {j} {C} {t} = begin
    tr (λ A → Sub (Γ , A) (Δ , B)) (cong ([_] B) π₁,)
    (π₁ (σ , t) ⁺)
      ≡⟨ tr-cong π₁, ⟨
    tr (λ σ → Sub (Γ , [ σ ] B) (Δ , B)) π₁,
    (π₁ (σ , t) ⁺)
      ≡⟨ apd (λ σ → _⁺ σ {B}) π₁, ⟩
    σ ⁺
      ∎
    where open ≡-Reasoning

  π₁⨟⁺
    : tr (λ A → Sub (Γ , A) (Θ , B)) (cong ([_] B) (π₁⨟ σ τ) ∙ [⨟])
      ((π₁ (σ ⨟ τ)) ⁺)
    ≡ σ ⁺ ⨟ (π₁ τ) ⁺
  π₁⨟⁺ {Γ} {Θ} {i} {B} {Δ} {σ} {j} {A} {τ} = begin
    tr (λ A → Sub (Γ , A) (Θ , B)) (cong ([_] B) (π₁⨟ σ τ) ∙ [⨟])
      ((π₁ (σ ⨟ τ)) ⁺)
      ≡⟨  tr² (cong ([_] B) (π₁⨟ σ τ)) ⟨
    tr (λ A → Sub (Γ , A) (Θ , B)) [⨟] (tr (λ A → Sub (Γ , A) (Θ , B)) (cong ([_] B) (π₁⨟ σ τ))
      ((π₁ (σ ⨟ τ)) ⁺) )
      ≡⟨ cong (tr (λ A → Sub (Γ , A) (Θ , B)) [⨟]) (tr-cong (π₁⨟ σ τ)) ⟨
    tr (λ A → Sub (Γ , A) (Θ , B)) [⨟] (tr (λ σ → Sub (Γ , [ σ ] B) (Θ , B)) (π₁⨟ σ τ)
      ((π₁ (σ ⨟ τ)) ⁺)) 
      ≡⟨ cong (tr (λ A → Sub (Γ , A) (Θ , B)) [⨟]) (apd (λ σ → _⁺ σ {B}) (π₁⨟ σ τ)) ⟩
    tr (λ A → Sub (Γ , A) (Θ , B)) [⨟] ((σ ⨟ π₁ τ) ⁺)
      ≡⟨ ⨟⁺ ⟩
    σ ⁺ ⨟ (π₁ τ) ⁺
      ∎ 
    where open ≡-Reasoning
