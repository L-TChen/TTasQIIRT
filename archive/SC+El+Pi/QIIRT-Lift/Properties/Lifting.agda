open import Prelude
  hiding (_,_)
  
module SC+El+Pi.QIIRT-Lift.Properties.Lifting where

open import SC+El+Pi.QIIRT-Lift.Base
open import SC+El+Pi.QIIRT-Lift.Properties

id↑=id : (A : Ty Γ) → idS {Γ} ↑ A ≅ idS {Γ , A}
id↑=id {Γ} A = begin
  wk ⨟ idS , π₂ (idS {Γ , A}) ≅⟨ hcong₂ (λ σ t → _,_ σ {A} t) (≡-to-≅ (wk ⨟idS)) refl ⟩
  wk , vz                     ≡⟨ sym η, ⟩
  idS                         ∎
  where open ≅-Reasoning

postulate
  [↑S]=[↑]   : (σ : Sub Γ Δ) (A : Ty Δ) (B : Ty (Δ , A))
      → [ σ ⇈ ∅ , A ] B ≡ [ σ ↑ A ] B
  [↑S]t=[↑]t : (σ : Sub Γ Δ) (A : Ty Δ) (B : Ty (Δ , A)) (u : Tm (Δ , A) B)
    → [ σ ⇈ ∅ , A ]tm u ≅ [ σ ↑ A ⇈ ∅ ]tm u

--   {-# TERMINATING #-}
_⇈S_
  : (σ : Sub Γ Δ) (Ξ : Lift Δ) → Sub (Γ ++ [ σ ]l Ξ) (Δ ++ Ξ)
[⇈S]=[⇈]
  : (σ : Sub Γ Δ) (Ξ : Lift Δ) (B : Ty (Δ ++ Ξ))
  → [ σ ⇈ Ξ ] B ≅  [ σ ⇈S Ξ ] B
[⇈S]tm≅[⇈]tm
  : (σ : Sub Γ Δ) (Ξ : Lift Δ) (B : Ty (Δ ++ Ξ)) (u : Tm (Δ ++ Ξ) B) 
  → [ σ ⇈ Ξ ]tm u ≅ [ σ ⇈S Ξ ]tm u
[⇈S]t=[⇈]t
  : (σ : Sub Γ Δ) (Ξ : Lift Δ) (B : Ty (Δ ++ Ξ)) (u : Tm (Δ ++ Ξ) B)
  → [ σ ⇈ Ξ ]t u ≅ [ σ ⇈S Ξ ]t u

σ ⇈S ∅       = σ
σ ⇈S (Ξ , A) = {! (σ ⇈S Ξ) ↑ A !}

[⇈S]=[⇈] σ Ξ U       = refl
[⇈S]=[⇈] σ Ξ (Π B C) = hcong₂ Π ([⇈S]=[⇈] σ Ξ B) {!≡-to-≅ ?!}
[⇈S]=[⇈] σ Ξ (El u)  = hcong El ([⇈S]t=[⇈]t σ Ξ U u)

[⇈S]t=[⇈]t σ Ξ B u = begin
  [ σ ⇈ Ξ  ]t  u  ≅⟨ ≡-to-≅ $ sym ([]tm≡[]t Ξ u σ) ⟩
  [ σ ⇈ Ξ  ]tm u  ≅⟨ [⇈S]tm≅[⇈]tm σ Ξ B u ⟩
  [ σ ⇈S Ξ ]tm u  ≅⟨ ≡-to-≅ ([]tm≡[]t ∅ u (σ ⇈S Ξ)) ⟩
  [ σ ⇈S Ξ ]t  u  ∎ 
  where open ≅-Reasoning

[⇈S]tm≅[⇈]tm σ Ξ B u = {!!}

-- id⇈S=id
--   : (Ξ : Lift Γ)
--   → idS ⇈S Ξ ≅ idS {Γ ++ Ξ}
-- id⇈S=id = {!!}
