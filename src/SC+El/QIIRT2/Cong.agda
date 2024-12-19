module SC+El.QIIRT2.Cong where
 
open import Prelude
  hiding (_,_)
open import SC+El.QIIRT2.Base

variable
  Γ' Δ' : Ctx

-- congruence rules for declations
Ty` : Γ ≡ Γ' → Ty Γ ≡ Ty Γ'
Ty` = cong Ty

Sub` : Γ ≡ Γ' → Δ ≡ Δ' → Sub Γ Δ ≡ Sub Γ' Δ'
Sub` = cong₂ Sub

TmΓ` : {A A' : Ty Γ} → A ≡ A' → Tm Γ A ≡ Tm Γ A'
TmΓ` {Γ = Γ} = cong (Tm Γ)

-- congruence rule for recursions
[]` : (Γ≡Γ' : Γ ≡ Γ')(Δ≡Δ' : Δ ≡ Δ')(A≡A' : conv (Ty` Δ≡Δ') A ≡ A')
    → conv (Sub` Γ≡Γ' Δ≡Δ') σ ≡ σ'
    → conv (Ty` Γ≡Γ') (A [ σ ]) ≡ A' [ σ' ]
[]` refl refl refl refl = refl

-- congruence rules for constructors
,Ctx` : (Γ≡Γ' : Γ ≡ Γ')(A≡A' : conv (Ty` Γ≡Γ') A ≡ A') → (Γ , A) ≡ (Γ' , A')
,Ctx` refl refl = refl