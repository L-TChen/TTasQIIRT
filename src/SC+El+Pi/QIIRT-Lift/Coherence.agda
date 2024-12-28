module SC+El+Pi.QIIRT-Lift.Coherence where

open import Prelude
  hiding (_,_)

open import SC+El+Pi.QIIRT-Lift.Base
open import SC+El+Pi.QIIRT-Lift.Properties

cong-U : Γ ≅ Δ → U {Γ} ≅ U {Δ}
cong-U refl = refl

coh[idS⨟]
  : [ idS ⨟ σ ⇈ Ξ ] A ≡ [ σ ⇈ Ξ ] A
coh[idS⨟] = refl

coh[⨟idS]
  : [ σ ⨟ idS ⇈ Ξ ] A ≡ [ σ ⇈ Ξ ] A
coh[⨟idS] = refl

coh[assocS]
  : [ (σ ⨟ τ) ⨟ γ ⇈ Ξ ] A ≡ [ σ ⨟ (τ ⨟ γ) ⇈ Ξ ] A
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
    → [ σ ⨟ (τ , t) ⇈ Ξ ] B ≅ [ (σ ⨟ τ) , [ σ ]t t ⇈ Ξ ] B

  coh[⨟,]l ∅        = refl
  coh[⨟,]l (Ξ , A) = hcong₂ _,_ (coh[⨟,]l Ξ) (coh[⨟,]' Ξ (coh[⨟,]l Ξ) A)

  coh[⨟,]' Ξ eq U       = cong-U (hcong (Γ ++_) eq)
  coh[⨟,]' Ξ eq (Π B C) = icong₂ Ty (cong (Γ ++_) (≅-to-≡ eq)) Π
    (coh[⨟,]' Ξ eq B)
    (coh[⨟,]' (Ξ , B) (hcong₂ _,_ eq (coh[⨟,]' Ξ eq B)) C)
  coh[⨟,]' Ξ eq (El u)  = icong (λ Γ → Tm Γ U) (cong (Γ ++_) (≅-to-≡ eq)) El $ begin
    [ σ ⨟ (τ , t) ⇈ Ξ ]t u                   ≅⟨ refl ⟩
    [ σ ⇈ [ τ , t ]l Ξ ]t  [ τ , t ⇈ Ξ ]tm u ≅⟨ HEq.sym (≡-to-≅ $ []tm≡[]t _ _ _) ⟩
    [ σ ⇈ [ τ , t ]l Ξ ]tm [ τ , t ⇈ Ξ ]tm u ≅⟨ HEq.sym (≡-to-≅ $ [⨟]tm) ⟩
    [ σ ⨟ (τ , t) ⇈ Ξ ]tm u                  ≅⟨ hcong (λ σ → [ σ ⇈ Ξ ]tm u) (≡-to-≅ ⨟,) ⟩
    [ σ ⨟ τ , [ σ ]t t ⇈ Ξ ]tm u             ∎

coh[βπ₁] : [ π₁ (σ , t) ⇈ Ξ ] A ≡ [ σ ⇈ Ξ ] A
coh[βπ₁] = refl

module _ {Γ : Ctx} (σ : Sub Γ ∅) where
  open ≅-Reasoning

  coh[η∅]l : (Ξ : Lift ∅)
    → [ σ ]l Ξ ≅ [ ∅ {Γ} ]l Ξ
  coh[η∅] : (Ξ : Lift ∅) → [ σ ]l Ξ ≅ [ ∅ {Γ} ]l Ξ
    → (A : Ty (∅ ++ Ξ))
    → [ σ ⇈ Ξ ] A ≅ [ (∅ {Γ}) ⇈ Ξ ] A 

  coh[η∅]l ∅       = refl
  coh[η∅]l (Ξ , A) = hcong₂ _,_ (coh[η∅]l Ξ) (coh[η∅] Ξ (coh[η∅]l Ξ) A)

  coh[η∅] Ξ eq U       = cong-U (hcong (Γ ++_) eq)
  coh[η∅] Ξ eq (Π A B) = icong₂ Ty (cong (Γ ++_) (≅-to-≡ eq)) Π
    (coh[η∅] Ξ eq A)
    (coh[η∅] (Ξ , A) ((hcong₂ _,_ eq (coh[η∅] Ξ eq A))) B)
  coh[η∅] Ξ eq (El u)  = icong (λ Γ → Tm Γ U) (cong (Γ ++_) (≅-to-≡ eq)) El $ begin
    [ σ ⇈ Ξ ]t  u ≅⟨ ≡-to-≅ (sym ([]tm≡[]t Ξ u σ)) ⟩
    [ σ ⇈ Ξ ]tm u ≅⟨ hcong ([_⇈ Ξ ]tm u) (≡-to-≅ η∅) ⟩
    [ ∅ ⇈ Ξ ]tm u ∎

module _ {Γ Δ : Ctx} {A : Ty Δ} (σ : Sub Γ (Δ , A)) where 
  open ≅-Reasoning
  coh[η,]l
    : (Ξ : Lift (Δ , A)) → [ σ ]l Ξ ≅ [ π₁ σ , π₂ σ ]l Ξ
  coh[η,] 
    : (Ξ : Lift (Δ , A))
    → [ σ ]l Ξ ≅ [ π₁ σ , π₂ σ ]l Ξ
    → (B : Ty ((Δ , A) ++ Ξ))
    → [ σ ⇈ Ξ ] B ≅ [ π₁ σ , π₂ σ ⇈ Ξ ] B

  coh[η,]l ∅       = refl
  coh[η,]l (Ξ , A) = hcong₂ _,_ (coh[η,]l Ξ) (coh[η,] Ξ (coh[η,]l Ξ) A)

  coh[η,] Ξ eq U       = cong-U (hcong (Γ ++_) eq)
  coh[η,] Ξ eq (Π A B) = icong₂ Ty (cong (Γ ++_) (≅-to-≡ eq)) Π
    (coh[η,] Ξ eq A)
    (coh[η,] (Ξ , A) (hcong₂ _,_ eq (coh[η,] Ξ eq A)) B)
  coh[η,] Ξ eq (El u)  = icong (λ Γ → Tm Γ U) (cong (Γ ++_) (≅-to-≡ eq)) El $ begin
    [ σ ⇈ Ξ ]t            u ≅⟨ ≡-to-≅ (sym ([]tm≡[]t Ξ u σ)) ⟩
    [ σ ⇈ Ξ ]tm           u ≅⟨ hcong ([_⇈ Ξ ]tm u) (≡-to-≅ η,) ⟩
    [ π₁ σ , π₂ σ ⇈ Ξ ]tm u ∎

-- Coherence property for the term substitution
module _ {Γ Δ : Ctx} (Ξ : Lift Δ) {A : Ty (Δ ++ Ξ)} {t u : Tm (Δ ++ Ξ) A} {σ γ : Sub Γ Δ} where
  open ≅-Reasoning
  coh[σ]tm
    : σ ≅ γ → t ≅ u → [ σ ⇈ Ξ ]t t ≅ [ γ ⇈ Ξ ]t u
  coh[σ]tm σ=γ t=u = begin
    [ σ ⇈ Ξ ]t  t ≅⟨ ≡-to-≅ (sym ([]tm≡[]t Ξ t σ)) ⟩
    [ σ ⇈ Ξ ]tm t ≅⟨ hcong₂ [_⇈ Ξ ]tm_ σ=γ t=u ⟩
    [ γ ⇈ Ξ ]tm u ≅⟨ ≡-to-≅ ([]tm≡[]t Ξ u γ) ⟩
    [ γ ⇈ Ξ ]t  u ∎
{-
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
-}
