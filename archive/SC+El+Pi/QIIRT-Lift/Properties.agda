open import Prelude
  hiding (_,_)
  
module SC+El+Pi.QIIRT-Lift.Properties where

open import SC+El+Pi.QIIRT-Lift.Base

[]tapp : (σ : Sub Γ Δ) (Ξ : Lift Δ)
  → (A : Ty (Δ ++ Ξ)) (B : Ty (Δ ++ Ξ , A)) (t : Tm (Δ ++ Ξ) (Π A B))
  → app ([ σ ⇈ Ξ ]t t) ≡ [ σ ⇈ Ξ , A ]t (app t)
[]tapp σ Ξ A B t = begin
  app ([ σ ⇈ Ξ ]t t)                 ≡⟨ cong app (cong ([ σ ⇈ Ξ ]t_) (sym Πη)) ⟩
  app ([ σ ⇈ Ξ ]t (abs (app t)))     ≡⟨ cong app ([]tabs {σ = σ}) ⟩
  app (abs ([ σ ⇈ Ξ , A ]t (app t))) ≡⟨ Πβ ⟩
  [ σ ⇈ Ξ , A ]t (app t)             ∎
  where open ≡-Reasoning

-- derived computation rules on composition
π₁⨟ : (σ : Sub Γ Δ) (τ : Sub Δ (Θ , A)) → π₁ (σ ⨟ τ) ≡ σ ⨟ π₁ τ
π₁⨟ σ τ = begin
  π₁ (σ ⨟ τ)                    ≡⟨ cong (λ τ → π₁ (σ ⨟ τ)) η, ⟩
  π₁ (σ ⨟ (π₁ τ , π₂ τ))        ≡⟨ cong π₁ ⨟, ⟩ 
  π₁ (σ ⨟ π₁ τ , [ σ ]t π₂ τ)   ≡⟨ π₁, ⟩
  σ ⨟ π₁ τ                      ∎
  where open ≡-Reasoning

π₂⨟ : (σ : Sub Γ Δ) (τ : Sub Δ (Θ , A))
  → π₂ (σ ⨟ τ) ≡ [ σ ]t (π₂ τ)
π₂⨟ {Γ} {Δ} {Θ} {A} σ τ = ≅-to-≡ $ begin
  π₂ (σ ⨟ τ)                      ≅⟨ hcong (λ ν → π₂ (σ ⨟ ν)) (≡-to-≅ η,) ⟩
  π₂ (σ ⨟ (π₁ τ , π₂ τ))          ≅⟨ hcong π₂ (≡-to-≅ ⨟,) ⟩
  π₂ ((σ ⨟ π₁ τ) , [ σ ]t (π₂ τ)) ≡⟨ π₂, ⟩
  [ σ ]t π₂ τ ∎
  where open ≅-Reasoning

π₁idS⨟ : (σ : Sub Γ (Δ , A)) → σ ⨟ π₁ idS ≡ π₁ σ
π₁idS⨟ σ = begin
  σ ⨟ π₁ idS   ≡⟨ sym (π₁⨟ σ idS) ⟩
  π₁ (σ ⨟ idS) ≡⟨ cong π₁ (σ ⨟idS) ⟩
  π₁ σ         ∎
  where open ≡-Reasoning

-- Soundness of term substitution
[]tm≡[]t : (Ξ : Lift Δ){A : Ty (Δ ++ Ξ)}(u : Tm (Δ ++ Ξ) A)(σ : Sub Γ Δ)
  → [ σ ⇈ Ξ ]tm u ≡ [ σ ⇈ Ξ ]t u
[]tm≡[]t Ξ u ∅            = refl
[]tm≡[]t Ξ u (σ , t)      = refl
[]tm≡[]t Ξ u wk           = refl
[]tm≡[]t Ξ u (π₁ (π₁ σ))  = refl
[]tm≡[]t Ξ u (π₁ (σ ⨟ τ)) = begin
  [ π₁ (σ ⨟ τ)  ⇈ Ξ ]tm u                 ≡⟨ ≅-to-≡ (hcong ([_⇈ Ξ ]tm u) (≡-to-≅ (π₁⨟ σ τ))) ⟩
  [ σ ⨟ π₁ τ    ⇈ Ξ ]tm u                 ≡⟨ [⨟]tm ⟩
  [ σ ⇈ [ π₁ τ ]l Ξ ]tm [ π₁ τ ⇈ Ξ ]tm u  ≡⟨ cong ([ σ ⇈ [ π₁ τ ]l Ξ ]tm_) ([]tm≡[]t Ξ u (π₁ τ)) ⟩
  [ σ ⇈ [ π₁ τ ]l Ξ ]tm [ π₁ τ ⇈ Ξ ]t  u  ≡⟨ []tm≡[]t ([ π₁ τ ]l Ξ) ([ π₁ τ ⇈ Ξ ]t u) σ ⟩
  [ σ ⇈ [ π₁ τ ]l Ξ ]t  [ π₁ τ ⇈ Ξ ]t  u  ≡⟨⟩
  [ π₁ (σ ⨟ τ) ⇈ Ξ ]t u ∎

  where open ≡-Reasoning
[]tm≡[]t Ξ u idS          = [id]tm
[]tm≡[]t Ξ u (σ ⨟ τ) = begin
  [ σ ⨟ τ ⇈ Ξ ]tm u                ≡⟨ [⨟]tm ⟩
  [ σ ⇈ [ τ ]l Ξ ]tm [ τ ⇈ Ξ ]tm u ≡⟨ cong ([ σ ⇈ [ τ ]l Ξ ]tm_) ([]tm≡[]t Ξ u τ) ⟩
  [ σ ⇈ [ τ ]l Ξ ]tm [ τ ⇈ Ξ ]t  u ≡⟨ []tm≡[]t ([ τ ]l Ξ) ([ τ ⇈ Ξ ]t u) σ ⟩
  [ σ ⇈ [ τ ]l Ξ ]t  [ τ ⇈ Ξ ]t  u ∎
  where open ≡-Reasoning
[]tm≡[]t Ξ u (π₁ (σ , t)) = begin
  [ π₁ (σ , t) ⇈ Ξ ]tm u ≡⟨ ≅-to-≡ (hcong (λ σ → [ σ ⇈ Ξ ]tm u) (≡-to-≅ π₁,)) ⟩
  [ σ ⇈ Ξ ]tm u          ≡⟨ []tm≡[]t Ξ u σ ⟩
  [ σ ⇈ Ξ ]t  u          ∎
  where open ≡-Reasoning
