open import Prelude
  hiding (_,_)
  
module SC+U+Pi+Id.QIIRT.Properties where

open import SC+U+Pi+Id.QIIRT.Base

cong-U : Γ ≅ Δ → U {Γ} i ≅ U {Δ} i
cong-U refl = refl

[]tapp : (σ : Sub Γ Δ)
  → (A : Ty Δ i) (B : Ty (Δ , A) i) (t : Tm Δ (Π A B))
  → app ([ σ ]tm t) ≡ [ σ ↑ A ]tm (app t)
[]tapp σ A B t = begin
  app ([ σ ]tm t)               ≡⟨ cong app (cong ([ σ ]tm_) Πη) ⟨
  app ([ σ ]tm (ƛ (app t)))     ≡⟨ cong app ([]ƛ σ (app t)) ⟩
  app (ƛ ([ σ ↑ A ]tm (app t))) ≡⟨ Πβ ⟩
  [ σ ↑ A ]tm (app t)           ∎
  where open ≡-Reasoning

-- derived computation rules on composition
π₁⨟ : (σ : Sub Γ Δ) (τ : Sub Δ (Θ , A)) → π₁ (σ ⨟ τ) ≡ σ ⨟ π₁ τ
π₁⨟ σ τ = begin
  π₁ (σ ⨟ τ)                   ≡⟨ cong (λ τ → π₁ (σ ⨟ τ)) η, ⟩
  π₁ (σ ⨟ (π₁ τ , π₂ τ))       ≡⟨ cong π₁ ⨟, ⟩ 
  π₁ (σ ⨟ π₁ τ , [ σ ]tm π₂ τ)  ≡⟨ π₁, ⟩
  σ ⨟ π₁ τ                     ∎
  where open ≡-Reasoning

π₁idS⨟ : (σ : Sub Γ (Δ , A)) → π₁ σ ≡ σ ⨟ π₁ idS
π₁idS⨟ σ = begin
  π₁ σ         ≡⟨ cong π₁ (σ ⨟idS) ⟨
  π₁ (σ ⨟ idS) ≡⟨ π₁⨟ σ idS ⟩
  σ ⨟ π₁ idS   ∎
  where open ≡-Reasoning

π₂⨟ : (σ : Sub Γ Δ) (τ : Sub Δ (Θ , A))
  → π₂ (σ ⨟ τ) ≡ [ σ ]tm (π₂ τ)
π₂⨟ {Γ} {Δ} {Θ} {A} σ τ = begin
  π₂ (σ ⨟ τ)                       ≡⟨ ≅-to-≡ $ hcong (λ ν → π₂ (σ ⨟ ν)) (≡-to-≅ η,) ⟩
  π₂ (σ ⨟ (π₁ τ , π₂ τ))           ≡⟨ ≅-to-≡ $ hcong π₂ (≡-to-≅ ⨟,) ⟩
  π₂ ((σ ⨟ π₁ τ) , [ σ ]tm (π₂ τ)) ≡⟨ π₂, ⟩
  [ σ ]tm π₂ τ ∎
  where open ≡-Reasoning

⁺⨟wk : (σ : Sub Γ Δ) {A : Ty Δ i} → (_⁺ σ {A}) ⨟ wk ≡ wk ⨟ σ
⁺⨟wk σ = begin
  σ ⁺ ⨟ π₁ idS             ≡⟨ π₁idS⨟ (σ ⁺) ⟨
  π₁ (σ ⁺)                 ≡⟨⟩
  π₁ (π₁ idS ⨟ σ , π₂ idS) ≡⟨ π₁, ⟩
  π₁ idS ⨟ σ ∎
  where open ≡-Reasoning

[⁺]vz : (σ : Sub Γ Δ) (A : Ty Δ i) → [ _⁺ σ {A} ]t vz ≅ vz
[⁺]vz σ A = begin
  [ σ ⁺ ]t (π₂ idS)
    ≅⟨ ≡-to-≅ (π₂⨟ (σ ⁺) idS) ⟨
  π₂ (σ ⁺ ⨟ idS)
    ≅⟨ hcong π₂ (≡-to-≅ ((σ ⁺) ⨟idS)) ⟩
  π₂ (σ ⁺)
    ≡⟨ π₂, ⟩
  π₂ idS
    ∎
  where open ≅-Reasoning
  
id↑ : (Γ : Ctx) (A : Ty Γ i) → idS {Γ , A} ≡ idS ⁺
id↑ Γ A = begin
  idS                   ≡⟨ η, ⟩
  π₁ idS , π₂ idS       ≡⟨ ≅-to-≡ $ hcong₂ (λ σ t → _,_ σ {A} t) (≡-to-≅ $ π₁ idS ⨟idS) refl ⟨
  π₁ idS ⨟ idS , π₂ idS ≡⟨⟩
  idS ⁺ ∎
  where open ≡-Reasoning

σ⨟τ↑ : (σ : Sub Γ Δ) (τ : Sub Δ Θ) (A : Ty Θ i) → σ ⁺ ⨟ τ ⁺ ≡ (σ ⨟ τ) ⁺
σ⨟τ↑ {Γ} {Δ} {Θ} σ τ A = sym $ begin
  (σ ⨟ τ) ⁺                    ≡⟨⟩
  wk ⨟ (σ ⨟ τ) , vz            ≡⟨ ≅-to-≡ (hcong₂ (λ σ t → _,_ σ {A} t) (≡-to-≅ ⨟-assoc) refl) ⟩
  (wk ⨟ σ) ⨟ τ , vz            ≡⟨ ≅-to-≡ $ hcong₂
                                   {A = Sub (Γ , [ σ ⨟ τ ] A) Δ}
                                   {B = λ γ → Tm (Γ , [ σ ] [ τ ] A)
                                   ([ γ ] [ τ ] A)} (λ σ t → _,_ (σ ⨟ τ) {A} t) (≡-to-≅ (⁺⨟wk σ))
                                   ([⁺]vz σ ([ τ ] A)) ⟨
  (_⁺ σ {[ τ ] A} ⨟ wk) ⨟ τ , [ _⁺ σ {[ τ ] A} ]t vz
    ≡⟨ ≅-to-≡ $ hcong₂ (λ σ t → _,_ σ {A} t) (≡-to-≅ ⨟-assoc) refl ⟨
  σ ⁺ ⨟ (wk ⨟ τ) , [ _⁺ σ {[ τ ] A} ]t vz ≡⟨ ⨟, ⟨
  σ ⁺ ⨟ ((wk ⨟ τ) , vz)                   ≡⟨⟩
  σ ⁺ ⨟ τ ⁺                               ∎
  where open ≡-Reasoning

↑=⁺ : (A : Ty Δ i) (σ : Sub Γ Δ) → σ ↑ A ≡ σ ⁺
↑=⁺ A ∅            = refl
↑=⁺ A (σ , t)      = refl
↑=⁺ A wk           = refl
↑=⁺ A (π₁ (π₁ σ))  = refl
↑=⁺ {Γ} A idS      = id↑ _ _
↑=⁺ A (σ ⨟ τ)      = begin
  (σ ⨟ τ) ↑ A                 ≡⟨ refl ⟩
  (σ ↑ ([ τ ] A)) ⨟ (τ ↑ A)   ≡⟨ cong₂ _⨟_ (↑=⁺ _ σ) (↑=⁺ A τ) ⟩
  σ ⁺ ⨟ τ ⁺                   ≡⟨ σ⨟τ↑ σ τ A ⟩
  (σ ⨟ τ) ⁺                   ∎
  where open ≡-Reasoning
↑=⁺ A (π₁ (σ , t)) = begin
  σ ↑ A        ≡⟨ ↑=⁺ A σ ⟩
  σ ⁺          ≡⟨ ≅-to-≡ (hcong (λ σ → _⁺ σ {A}) (≡-to-≅ π₁,)) ⟨
  π₁ (σ , t) ⁺ ∎
  where open ≡-Reasoning
↑=⁺ {Δ} {i} {Γ} A (π₁ (_⨟_ {Δ = Θ} σ τ)) = begin
  (σ ↑ _) ⨟ (π₁ τ ↑ _)               ≡⟨ cong₂ _⨟_ (↑=⁺ _ σ) (↑=⁺ _ (π₁ τ)) ⟩
  σ ⁺ ⨟ π₁ τ ⁺                       ≡⟨⟩
  σ ⁺ ⨟ (wk ⨟ π₁ τ , vz)             ≡⟨ ⨟, ⟩
  σ ⁺ ⨟ (wk ⨟ π₁ τ) , [ _⁺ σ {[ π₁ τ ] A} ]t vz ≡⟨ ≅-to-≡ $ hcong₂ (λ σ t → _,_ σ {A} t) (≡-to-≅ ⨟-assoc) refl ⟩
  (σ ⁺ ⨟ wk) ⨟ π₁ τ , [ _⁺ σ {[ π₁ τ ] A} ]t vz

    ≡⟨ ≅-to-≡ $ hcong₂
       {A = Sub (Γ , [ σ ] [ π₁ τ ] A) Θ} {B = λ γ → Tm (Γ , [ σ ⨟ π₁ τ ] A)
       ([ γ ⨟ π₁ τ ] A)} (λ σ t → _,_ (σ ⨟ π₁ τ) {A} t) (≡-to-≅ (⁺⨟wk σ)) ([⁺]vz σ ([ π₁ τ ] A)) ⟩

  (wk ⨟ σ) ⨟ π₁ τ   , vz           ≡⟨ ≅-to-≡ $ hcong₂ (λ σ t → _,_ σ {A} t) (≡-to-≅ ⨟-assoc) refl ⟨
  wk ⨟ (σ ⨟ π₁ τ)   , vz           ≡⟨
    (≅-to-≡ $ hcong₂ {A = Sub Γ Δ} {B = λ γ → Tm (Γ , [ σ ⨟ π₁ τ ] A) ([ wk ] [ γ ] A)} (λ σ t → _,_ (wk ⨟ σ) {A} t) (≡-to-≅ (π₁⨟ σ τ))  refl)  ⟨
  wk ⨟ π₁ (σ ⨟ τ)   , vz           ∎
  where open ≡-Reasoning

-- Soundness of term substitution
[]tm≡[]t : {A : Ty Δ i}(u : Tm Δ A)(σ : Sub Γ Δ)
  → [ σ ]tm u ≡ [ σ ]t u
[]tm≡[]t u ∅            = refl
[]tm≡[]t u (σ , t)      = refl
[]tm≡[]t u wk           = refl
[]tm≡[]t u (π₁ (π₁ σ))  = refl
[]tm≡[]t u (π₁ (σ ⨟ τ)) = begin
  [ π₁ (σ ⨟ τ) ]tm u    ≡⟨ ≅-to-≡ (hcong ([_]tm u) (≡-to-≅ (π₁⨟ σ τ))) ⟩
  [ σ ⨟ π₁ τ   ]tm u    ≡⟨ [⨟]tm ⟩
  [ σ ]tm [ π₁ τ ]tm u  ≡⟨ cong ([ σ ]tm_) ([]tm≡[]t u (π₁ τ)) ⟩
  [ σ ]tm [ π₁ τ ]t  u  ≡⟨ []tm≡[]t ([ π₁ τ ]t u) σ ⟩
  [ σ ]t  [ π₁ τ ]t  u  ≡⟨⟩
  [ π₁ (σ ⨟ τ) ]t u ∎
  where open ≡-Reasoning
[]tm≡[]t u idS      = [id]tm
[]tm≡[]t u (σ ⨟ τ) = begin
  [ σ ⨟ τ ]tm u     ≡⟨ [⨟]tm ⟩
  [ σ ]tm [ τ ]tm u ≡⟨ cong ([ σ ]tm_) ([]tm≡[]t u τ) ⟩
  [ σ ]tm [ τ ]t  u ≡⟨ []tm≡[]t ([ τ ]t u) σ ⟩
  [ σ ]t  [ τ ]t  u ∎
  where open ≡-Reasoning
[]tm≡[]t u (π₁ (σ , t)) = begin
  [ π₁ (σ , t) ]tm u ≡⟨ ≅-to-≡ (hcong (λ σ → [ σ ]tm u) (≡-to-≅ π₁,)) ⟩
  [ σ ]tm u          ≡⟨ []tm≡[]t u σ ⟩
  [ σ ]t  u          ∎
  where open ≡-Reasoning

{-
-- WRONG: the congruence rule for telescope substitution is used
module _ {σ γ : Sub Γ Δ} (σ=γ : σ ≡ γ) where
  open ≅-Reasoning

  ⇈-cong
    : (Ξ : Tel Δ)
    → σ ⇈ Ξ ≅ γ ⇈ Ξ
  ⇈-cong ∅       = ≡-to-≅ σ=γ
  ⇈-cong (Ξ , A) = begin
    σ ⇈ Ξ ↑ A
      ≅⟨ ≡-to-≅ (↑=⁺ A (σ ⇈ Ξ)) ⟩
    (σ ⇈ Ξ) ⁺
      ≅⟨ icong (λ σ → Sub (Γ ⧺ [ σ ]l Ξ) (Δ ⧺ Ξ)) σ=γ (λ σ → _⁺ σ {A}) (⇈-cong Ξ) ⟩
    (γ ⇈ Ξ) ⁺
      ≡⟨ ↑=⁺ A (_ ⇈ Ξ) ⟨
    γ ⇈ Ξ ↑ A
      ∎
-}

module _ {Γ : Ctx} where
  open ≅-Reasoning
  [idS]l
    : (Ξ : Tel Γ)
    → [ idS ]l Ξ ≡ Ξ
  idS⇈
    : (Ξ : Tel Γ)
    →  idS ⇈ Ξ ≅  idS {Γ ⧺ Ξ} 
  [idS]l ∅       = refl
  [idS]l (Ξ , A) = ≅-to-≡ $ hcong₂ {A = Tel Γ} {B = λ Ξ → Ty (Γ ⧺ Ξ) _} {C = λ _ _ → Tel Γ} _,_ (≡-to-≅ $ [idS]l Ξ) $ begin
    [ idS ⇈ Ξ ] A ≅⟨ icong (λ Ξ → Sub (Γ ⧺ Ξ) _) ([idS]l Ξ) ([_] A) (idS⇈ Ξ) ⟩
    [ idS ] A     ≡⟨⟩
    A             ∎

  idS⇈ ∅       = refl
  idS⇈ (Ξ , A) = icong (λ Ξ' → Sub (Γ ⧺ Ξ') (Γ ⧺ Ξ)) ([idS]l Ξ) (_↑ A) (idS⇈ Ξ)

module _ {Γ Δ Θ : Ctx} (σ : Sub Γ Δ) (τ : Sub Δ Θ) where
  open ≅-Reasoning
  [⨟]l
    : (Ξ : Tel Θ)
    → [ σ ⨟ τ ]l Ξ ≡ [ σ ]l [ τ ]l Ξ
  ⨟⇈
    : (Ξ : Tel Θ) 
    → (σ ⨟ τ) ⇈ Ξ ≅ (σ ⇈ ([ τ ]l Ξ)) ⨟ (τ ⇈ Ξ)
  [⨟]l ∅       = refl
  [⨟]l (Ξ , A) = ≅-to-≡ $ hcong₂ {B = λ Ξ → Ty (_ ⧺ Ξ) _} {C = λ _ _ → Tel Γ} _,_ (≡-to-≅ $ [⨟]l Ξ) $ begin
    [ (σ ⨟ τ) ⇈ Ξ ] A               ≅⟨ icong (λ Ξ → Sub (_ ⧺ Ξ) _) ([⨟]l Ξ) ([_] A) (⨟⇈ Ξ) ⟩
    [ (σ ⇈ [ τ ]l Ξ) ⨟ (τ ⇈ Ξ) ] A  ≡⟨⟩ 
    [ σ ⇈ [ τ ]l Ξ ] [ τ ⇈ Ξ ] A    ∎ 
  ⨟⇈ ∅         = refl
  ⨟⇈ (Ξ , A)   = icong (λ Ξ → Sub (_ ⧺ Ξ) _) ([⨟]l Ξ) (_↑ A) (⨟⇈ Ξ)
