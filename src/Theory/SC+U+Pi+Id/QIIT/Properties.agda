open import Prelude
  
module Theory.SC+U+Pi+Id.QIIT.Properties where 

open import Theory.SC+U+Pi+Id.QIIT.Syntax

opaque 
  []tapp : (σ : Sub Γ Δ)
    → (A : Ty Δ i) (B : Ty (Δ , A) i) (t : Tm Δ (Π A B))
    → app (tr (Tm Γ) []Π ([ σ ]tm t)) ≡ [ σ ↑ A ]tm app t
  []tapp {Γ} σ A B t = begin
    app (tr (Tm Γ) []Π ([ σ ]tm t))
      ≡⟨ cong (λ z → app (tr (Tm Γ) []Π ([ σ ]tm z))) (sym Πη) ⟩
    app (tr (Tm Γ) []Π ([ σ ]tm (ƛ app t)))
      ≡⟨ cong app ([]ƛ σ (app t)) ⟩
    app (ƛ ([ σ ↑ A ]tm app t))
      ≡⟨ Πβ ⟩
    [ σ ↑ A ]tm app t
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
  π₁⨟ : (σ : Sub Γ Δ) (τ : Sub Δ (Θ , A)) → π₁ (σ ⨟ τ) ≡ σ ⨟ π₁ τ
  π₁⨟ σ τ = Σ-≡,≡←≡ (π⨟ σ τ) .proj₁

  π₂⨟ : (σ : Sub Γ Δ) {A : Ty Θ i} (τ : Sub Δ (Θ , A))
    → _≡_ {_} {∃ (Tm Γ)}
    ([ π₁ (σ ⨟ τ) ] A , π₂ (σ ⨟ τ))
    ([ σ ] [ π₁ τ ] A , [ σ ]tm (π₂ τ))
  π₂⨟ {Γ} σ {A} τ = begin
    [ π₁ (σ ⨟ τ) ] A , π₂ (σ ⨟ τ)
      ≡⟨ apΣ (Tm Γ) ([_] A) (π⨟ σ τ) ⟩ 
    [ σ ⨟ π₁ τ ] A , tr (Tm Γ) (sym [⨟]) ([ σ ]tm π₂ τ)
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

  ⁺⨟wk : (σ : Sub Γ Δ) {A : Ty Δ i} → (σ ↑ A) ⨟ wk ≡ wk ⨟ σ
  ⁺⨟wk {Γ} {Δ} σ {A} = begin
    (σ ↑ A) ⨟ π₁ idS               ≡⟨ (sym $ ⨟π₁id (σ ↑ A)) ⟩
    π₁ (σ ↑ A)                     ≡⟨⟩
    π₁ (π₁ idS ⨟ σ , tr (Tm (Γ , [ σ ] A)) (sym [⨟]) vz) ≡⟨ π₁, ⟩
    π₁ idS ⨟ σ ∎
    where open ≡-Reasoning

  [↑][wk]=[wk][]
    : [ σ ↑ A ] [ wk ] A ≡ [ wk ] [ σ ] A
  [↑][wk]=[wk][] {σ = σ} {A = A} = sym [⨟] ∙ cong ([_] A) (⁺⨟wk σ) ∙ [⨟]

  [⁺]vz : (σ : Sub Γ Δ) (A : Ty Δ i)
    → [ σ ↑ A ]tm (π₂ idS)
    ≅ π₂ idS
  [⁺]vz {Γ} {Δ} σ A = begin
    [ σ ↑ A ]tm (π₂ idS)
      ≅⟨ ≡-to-≅ $ from-Σ≡ (π₂⨟ (σ ↑ A) idS) .proj₂ ⟨
    tr (Tm (Γ , [ σ ] A)) (from-Σ≡ (π₂⨟ (σ ↑ A) idS) .proj₁) (π₂ ((σ ↑ A) ⨟ idS))
      ≅⟨ {!!} ⟩
    π₂ idS
      ∎
    where open ≅-Reasoning

  
  id⁺
    : (Γ : Ctx) (A : Ty Γ i)
    → tr (λ B → Sub (Γ , B) (Γ , A)) [idS] (idS {Γ} ↑ A)
    ≡ idS {Γ , A}
  id⁺ Γ A = begin
      let vz' = tr (Tm _) (sym [⨟]) vz in
    tr (λ B → Sub (Γ , B) (Γ , A)) [idS]
      (wk ⨟ idS , vz')
      ≡⟨ {!wk ⨟ idS!} ⟩
    wk , π₂ idS
      ≡⟨ sym $ η, ⟩
    idS
      ∎
    where open ≡-Reasoning

  ⨟⁺
    : (σ : Sub Γ Δ) (τ : Sub Δ Θ) (B : Ty Θ i)
    → tr (λ A → Sub (Γ , A) (Θ , B)) [⨟] ((σ ⨟ τ) ↑ B) ≡ (σ ↑ ([ τ ] B))  ⨟ (τ ↑ B)
  ⨟⁺ {Γ} {Δ} {Θ} σ τ B = begin
    tr (λ A → Sub (Γ , A) (Θ , B)) [⨟] ((σ ⨟ τ) ↑ B)
      ≡⟨ {!!} ⟩
    (σ ↑ ([ τ ] B))  ⨟ (τ ↑ B)
      ∎
    where open ≡-Reasoning
  
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
    : tr (λ A → Sub (Γ , A) (Δ , B)) (cong ([_] B) π₁,) (π₁ (σ , t) ↑ B)
    ≡ σ ↑ B 
  π₁,⁺ {Γ} {Δ} {i} {B} {σ} {j} {C} {t} = begin
    tr (λ A → Sub (Γ , A) (Δ , B)) (cong ([_] B) π₁,)
    (π₁ (σ , t) ↑ B)
      ≡⟨ tr-cong π₁, ⟨
    tr (λ σ → Sub (Γ , [ σ ] B) (Δ , B)) π₁,
    (π₁ (σ , t) ↑ B)
      ≡⟨ apd (λ σ → σ ↑ B) π₁, ⟩
    σ ↑ B
      ∎
    where open ≡-Reasoning

  π₁⨟⁺
    : tr (λ A → Sub (Γ , A) (Θ , B)) (cong ([_] B) (π₁⨟ σ τ) ∙ [⨟])
      ((π₁ (σ ⨟ τ)) ↑ B)
    ≡ (σ ↑ ([ π₁ τ ] B)) ⨟ (π₁ τ) ↑ B
  π₁⨟⁺ {Γ} {Θ} {i} {B} {Δ} {σ} {j} {A} {τ} = begin
    tr (λ A → Sub (Γ , A) (Θ , B)) (cong ([_] B) (π₁⨟ σ τ) ∙ [⨟])
      ((π₁ (σ ⨟ τ)) ↑ B)
      ≡⟨  tr² (cong ([_] B) (π₁⨟ σ τ)) ⟨
    tr (λ A → Sub (Γ , A) (Θ , B)) [⨟] (tr (λ A → Sub (Γ , A) (Θ , B)) (cong ([_] B) (π₁⨟ σ τ))
      ((π₁ (σ ⨟ τ)) ↑ B) )
      ≡⟨ cong (tr (λ A → Sub (Γ , A) (Θ , B)) [⨟]) (tr-cong (π₁⨟ σ τ)) ⟨
    tr (λ A → Sub (Γ , A) (Θ , B)) [⨟] (tr (λ σ → Sub (Γ , [ σ ] B) (Θ , B)) (π₁⨟ σ τ)
      ((π₁ (σ ⨟ τ)) ↑ B)) 
      ≡⟨ cong (tr (λ A → Sub (Γ , A) (Θ , B)) [⨟]) (apd (λ σ → σ ↑ B) (π₁⨟ σ τ)) ⟩
    tr (λ A → Sub (Γ , A) (Θ , B)) [⨟] ((σ ⨟ π₁ τ) ↑ B)
      ≡⟨ ⨟⁺ _ _ _ ⟩
    (σ ↑ ([ π₁ τ ] B)) ⨟ ((π₁ τ) ↑ B)
      ∎ 
    where open ≡-Reasoning
