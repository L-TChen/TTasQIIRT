module SC+El+Pi.QIIRT-Lift.Coherence where

open import Prelude
  hiding (_,_)

open import SC+El+Pi.QIIRT-Lift.Base

[]tm≡[]t : (Ξ : Lift Δ){A : Ty (Δ ++ Ξ)}(u : Tm (Δ ++ Ξ) A)(σ : Sub Γ Δ)
  → [ Ξ ⇈ σ ]tm u ≡ [ Ξ ⇈ σ ]t u
[]tm≡[]t Ξ u ∅            = refl
[]tm≡[]t Ξ u (σ , t)      = refl
[]tm≡[]t Ξ u wk           = refl
[]tm≡[]t Ξ u (π₁ (π₁ σ))  = refl
[]tm≡[]t Ξ u (π₁ (σ ⨟ τ)) = begin
  [ Ξ ⇈ π₁ (σ ⨟ τ) ]tm u                 ≡⟨ ≅-to-≡ (hcong ([ Ξ ⇈_]tm u) (≡-to-≅ (π₁⨟ σ τ))) ⟩
  [ Ξ ⇈ σ ⨟ π₁ τ   ]tm u                 ≡⟨ [⨟]tm ⟩
  [ [ π₁ τ ]l Ξ ⇈ σ ]tm [ Ξ ⇈ π₁ τ ]tm u ≡⟨ cong ([ [ π₁ τ ]l Ξ ⇈ σ ]tm_) ([]tm≡[]t Ξ u (π₁ τ)) ⟩
  [ [ π₁ τ ]l Ξ ⇈ σ ]tm [ Ξ ⇈ π₁ τ ]t  u ≡⟨ []tm≡[]t ([ π₁ τ ]l Ξ) ([ Ξ ⇈ π₁ τ ]t u) σ ⟩
  [ [ π₁ τ ]l Ξ ⇈ σ ]t  [ Ξ ⇈ π₁ τ ]t  u ≡⟨⟩
  [ Ξ ⇈ π₁ (σ ⨟ τ) ]t u  ∎
  where open ≡-Reasoning
[]tm≡[]t Ξ u idS          = [id]tm
[]tm≡[]t Ξ u (σ ⨟ τ) = begin
  [ Ξ ⇈ σ ⨟ τ ]tm u                ≡⟨ [⨟]tm ⟩
  [ [ τ ]l Ξ ⇈ σ ]tm [ Ξ ⇈ τ ]tm u ≡⟨ cong ([ [ τ ]l Ξ ⇈ σ ]tm_) ([]tm≡[]t Ξ u τ) ⟩
  [ [ τ ]l Ξ ⇈ σ ]tm [ Ξ ⇈ τ ]t  u ≡⟨ []tm≡[]t ([ τ ]l Ξ) ([ Ξ ⇈ τ ]t u) σ ⟩
  [ [ τ ]l Ξ ⇈ σ ]t  [ Ξ ⇈ τ ]t  u ∎
  where open ≡-Reasoning
[]tm≡[]t Ξ u (π₁ (σ , t)) = begin
  [ Ξ ⇈ π₁ (σ , t) ]tm u ≡⟨ ≅-to-≡ (hcong (λ σ → [ Ξ ⇈ σ ]tm u) (≡-to-≅ π₁,)) ⟩
  [ Ξ ⇈ σ ]tm u          ≡⟨ []tm≡[]t Ξ u σ ⟩
  [ Ξ ⇈ σ ]t  u          ∎
  where open ≡-Reasoning

cong-U : Γ ≅ Δ → U {Γ} ≅ U {Δ}
cong-U refl = refl

coh[idS⨟]
  : [ Ξ ⇈ idS ⨟ σ ] A ≡ [ Ξ ⇈ σ ] A
coh[idS⨟] = refl

coh[⨟idS]
  : [ Ξ ⇈ σ ⨟ idS ] A ≡ [ Ξ ⇈ σ ] A
coh[⨟idS] = refl

coh[assocS]
  : [ Ξ ⇈ (σ ⨟ τ) ⨟ γ ] A ≡ [ Ξ ⇈ σ ⨟ (τ ⨟ γ) ] A
coh[assocS] = refl

module _ (σ : Sub Γ Δ) (τ : Sub Δ Θ) (A : Ty Θ) (t : Tm Δ ([ τ ] A)) where
  open ≅-Reasoning
  coh[⨟,]l
    : (Ξ : Lift (Θ , A))
    → [ σ ⨟ (τ , t) ]l Ξ ≅ [ σ ⨟ τ , [ σ ]t t ]l Ξ
  coh[⨟,]'
    : (Ξ : Lift (Θ , A))
    → [ σ ⨟ (τ , t) ]l Ξ ≅ [ σ ⨟ τ , [ σ ]t t ]l Ξ
    → (B : Ty ((Θ , A) ++ Ξ))
    → [ Ξ ⇈ σ ⨟ (τ , t) ] B ≅ [ Ξ ⇈ (σ ⨟ τ) , [ σ ]t t ] B

  coh[⨟,]l ∅        = refl
  coh[⨟,]l (Ξ , A) = hcong₂ _,_ (coh[⨟,]l Ξ) (coh[⨟,]' Ξ (coh[⨟,]l Ξ) A)

  coh[⨟,]' Ξ eq U       = cong-U (hcong (Γ ++_) eq)
  coh[⨟,]' Ξ eq (Π B C) = icong₂ Ty (cong (Γ ++_) (≅-to-≡ eq)) Π
    (coh[⨟,]' Ξ eq B)
    (coh[⨟,]' (Ξ , B) (hcong₂ _,_ eq (coh[⨟,]' Ξ eq B)) C)
  coh[⨟,]' Ξ eq (El u)  = icong (λ Γ → Tm Γ U) (cong (Γ ++_) (≅-to-≡ eq)) El $ begin
    [ Ξ ⇈ σ ⨟ (τ , t) ]t u                   ≅⟨ refl ⟩
    [ [ τ , t ]l Ξ ⇈ σ ]t  [ Ξ ⇈ τ , t ]tm u ≅⟨ HEq.sym (≡-to-≅ $ []tm≡[]t _ _ _) ⟩
    [ [ τ , t ]l Ξ ⇈ σ ]tm [ Ξ ⇈ τ , t ]tm u ≅⟨ HEq.sym (≡-to-≅ $ [⨟]tm) ⟩
    [ Ξ ⇈ σ ⨟ (τ , t) ]tm u                  ≅⟨ hcong (λ σ → [ Ξ ⇈ σ ]tm u) (≡-to-≅ ⨟,) ⟩
    [ Ξ ⇈ σ ⨟ τ , [ σ ]t t ]tm u             ∎

coh[βπ₁] : [ Ξ ⇈ π₁ (σ , t) ] A ≡ [ Ξ ⇈ σ ] A
coh[βπ₁] = refl

module _ {Γ : Ctx} (σ : Sub Γ ∅) where
  open ≅-Reasoning

  coh[η∅]l : (Ξ : Lift ∅)
    → [ σ ]l Ξ ≅ [ ∅ {Γ} ]l Ξ
  coh[η∅] : (Ξ : Lift ∅) → [ σ ]l Ξ ≅ [ ∅ {Γ} ]l Ξ
    → (A : Ty (∅ ++ Ξ))
    → [ Ξ ⇈ σ ] A ≅ [ Ξ ⇈ (∅ {Γ}) ] A 

  coh[η∅]l ∅        = refl
  coh[η∅]l (Ξ , A) = hcong₂ _,_ (coh[η∅]l Ξ) (coh[η∅] Ξ (coh[η∅]l Ξ) A)

  coh[η∅] Ξ eq U       = cong-U (hcong (Γ ++_) eq)
  coh[η∅] Ξ eq (Π A B) = icong₂ Ty (cong (Γ ++_) (≅-to-≡ eq)) Π
    (coh[η∅] Ξ eq A)
    (coh[η∅] (Ξ , A) ((hcong₂ _,_ eq (coh[η∅] Ξ eq A))) B)
  coh[η∅] Ξ eq (El u)  = icong (λ Γ → Tm Γ U) (cong (Γ ++_) (≅-to-≡ eq)) El $ begin
    [ Ξ ⇈ σ ]t  u ≅⟨ ≡-to-≅ (sym ([]tm≡[]t Ξ u σ)) ⟩
    [ Ξ ⇈ σ ]tm u ≅⟨ hcong ([ Ξ ⇈_]tm u) (≡-to-≅ η∅) ⟩
    [ Ξ ⇈ ∅ ]tm u ∎

module _ {Γ Δ : Ctx} {A : Ty Δ} (σ : Sub Γ (Δ , A)) where 
  open ≅-Reasoning
  coh[η,]l
    : (Ξ : Lift (Δ , A)) → [ σ ]l Ξ ≅ [ π₁ σ , π₂ σ ]l Ξ
  coh[η,] 
    : (Ξ : Lift (Δ , A))
    → [ σ ]l Ξ ≅ [ π₁ σ , π₂ σ ]l Ξ
    → (B : Ty ((Δ , A) ++ Ξ))
    → [ Ξ ⇈ σ ] B ≅ [ Ξ ⇈ π₁ σ , π₂ σ ] B

  coh[η,]l ∅       = refl
  coh[η,]l (Ξ , A) = hcong₂ _,_ (coh[η,]l Ξ) (coh[η,] Ξ (coh[η,]l Ξ) A)

  coh[η,] Ξ eq U       = cong-U (hcong (Γ ++_) eq)
  coh[η,] Ξ eq (Π A B) = icong₂ Ty (cong (Γ ++_) (≅-to-≡ eq)) Π
    (coh[η,] Ξ eq A)
    (coh[η,] (Ξ , A) (hcong₂ _,_ eq (coh[η,] Ξ eq A)) B)
  coh[η,] Ξ eq (El u)  = icong (λ Γ → Tm Γ U) (cong (Γ ++_) (≅-to-≡ eq)) El $ begin
    [ Ξ ⇈ σ ]t            u ≅⟨ ≡-to-≅ (sym ([]tm≡[]t Ξ u σ)) ⟩
    [ Ξ ⇈ σ ]tm           u ≅⟨ hcong ([ Ξ ⇈_]tm u) (≡-to-≅ η,) ⟩
    [ Ξ ⇈ π₁ σ , π₂ σ ]tm u ∎

module _  (Ξ : Lift Δ) (τ : Sub (Δ ++ Ξ) Θ) (u : Tm (Δ ++ Ξ) ([ τ ] A)) where
  open ≡-Reasoning
  coh[βπ₂]
    : (σ : Sub Γ Δ)
    → [ Ξ ⇈ σ ]t π₂ (_,_ τ {A} u) ≡ [ Ξ ⇈ σ ]t u
  coh[βπ₂] σ = begin
    [ Ξ ⇈ σ ]t  π₂ (τ , u)       ≡⟨ sym ([]tm≡[]t Ξ (π₂ (τ , u)) σ) ⟩
    [ Ξ ⇈ σ ]tm π₂ (_,_ τ {A} u) ≡⟨ cong ([ Ξ ⇈ σ ]tm_) π₂, ⟩
    [ Ξ ⇈ σ ]tm u                ≡⟨ []tm≡[]t Ξ u σ ⟩
    [ Ξ ⇈ σ ]t  u                ∎
 {-
  coh[βπ₂] ∅            = cong ([_⇈_]tm_ _ ∅) π₂,
  coh[βπ₂] (σ , t)      = cong ([_⇈_]tm_ _ (σ , t)) π₂,
  coh[βπ₂] idS          = π₂,
  coh[βπ₂] (σ ⨟ γ)      = cong [ [ γ ]l Ξ ⇈ σ ]t_ (coh[βπ₂] γ)
  coh[βπ₂] wk           = cong ([_⇈_]tm_ _ wk) π₂,
  coh[βπ₂] (π₁ (π₁ σ))  = cong ([_⇈_]tm_ _ (π₁ (π₁ σ))) π₂,
  coh[βπ₂] (π₁ (σ , _)) = coh[βπ₂] σ
  coh[βπ₂] (π₁ (σ ⨟ γ)) = cong [ [ π₁ γ ]l Ξ ⇈ σ ]t_ (coh[βπ₂] (π₁ γ))
-}

module _ (Ξ : Lift Δ) {A : Ty (Δ ++ Ξ)} (t : Tm (Δ ++ Ξ) A) (σ : Sub Γ Δ) where
  open ≡-Reasoning
  coh[][id]tm
    : [ Ξ ⇈ σ ]t [ Ξ ⇈ idS ]tm t ≡ [ Ξ ⇈ σ ]t t
  coh[][id]tm = begin
    [ Ξ ⇈ σ ]t  [ Ξ ⇈ idS ]tm t ≡⟨ sym ([]tm≡[]t Ξ ([ Ξ ⇈ idS ]tm t) σ) ⟩
    [ Ξ ⇈ σ ]tm [ Ξ ⇈ idS ]tm t ≡⟨ cong ([ Ξ ⇈ σ ]tm_) [id]tm ⟩
    [ Ξ ⇈ σ ]tm t               ≡⟨ []tm≡[]t Ξ t σ ⟩
    [ Ξ ⇈ σ ]t  t               ∎

module _ (Ξ : Lift Δ) {A : Ty (Δ ++ Ξ)} (σ : Sub Γ Δ) where
  open ≡-Reasoning
  coh[]tm
    : t ≡ u → [ Ξ ⇈ σ ]t t ≡ [ Ξ ⇈ σ ]t u
  coh[]tm {t = t} {u = u} eq = begin
    [ Ξ ⇈ σ ]t  t        ≡⟨ sym ([]tm≡[]t Ξ t σ) ⟩
    [ Ξ ⇈ σ ]tm t        ≡⟨ cong ([ Ξ ⇈ σ ]tm_) eq ⟩
    [ Ξ ⇈ σ ]tm u        ≡⟨ []tm≡[]t Ξ u σ ⟩
    [ Ξ ⇈ σ ]t  _        ∎
