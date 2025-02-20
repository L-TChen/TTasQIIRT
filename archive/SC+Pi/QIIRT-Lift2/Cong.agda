module SC+Pi.QIIRT-Lift2.Cong where
 
open import Prelude
  hiding (_,_)
open import SC+Pi.QIIRT-Lift2.Base

variable
  A' B' : Ty _
  Γ' Δ' : Ctx
  Ξ' : Lift _
  σ' : Sub _ _

-- congruence rules for declations
Ty` : Γ ≡ Γ' → Ty Γ ≡ Ty Γ'
Ty` = cong Ty

Lift` : Γ ≡ Γ' → Lift Γ ≡ Lift Γ'
Lift` = cong Lift

Sub` : Γ ≡ Γ' → Δ ≡ Δ' → Sub Γ Δ ≡ Sub Γ' Δ'
Sub` = cong₂ Sub

TmΓ` : {A A' : Ty Γ} → A ≡ A' → Tm Γ A ≡ Tm Γ A'
TmΓ` {Γ = Γ} = cong (Tm Γ)

Tm` : (Γ≡Γ' : Γ ≡ Γ') → conv (Ty` Γ≡Γ') A ≡ A' → Tm Γ A ≡ Tm Γ' A'
Tm` {Γ} refl = TmΓ`

-- congruence rule for recursions
[]l` : (Γ≡Γ' : Γ ≡ Γ')(Δ≡Δ' : Δ ≡ Δ')(Ξ≡Ξ' : conv (Lift` Δ≡Δ') Ξ ≡ Ξ')
     → conv (Sub` Γ≡Γ' Δ≡Δ') σ ≡ σ'
     → conv (Lift` Γ≡Γ') ([ σ ]l Ξ) ≡ [ σ' ]l Ξ'
[]l` refl refl = cong₂ λ Ξ σ → [ σ ]l Ξ

[]` : (Γ≡Γ' : Γ ≡ Γ')(Δ≡Δ' : Δ ≡ Δ')(A≡A' : conv (Ty` Δ≡Δ') A ≡ A')
    → conv (Sub` Γ≡Γ' Δ≡Δ') σ ≡ σ'
    → conv (Ty` Γ≡Γ') ([ σ ] A) ≡ [ σ' ] A'
[]` refl refl refl refl = refl

[]A` : {A : Ty Δ}{σ σ' : Sub Γ Δ} → σ ≡ σ' → [ σ ] A ≡ [ σ' ] A
[]A` {A = A} = []` {A = A} refl refl refl

[]lΞ` : {Ξ : Lift Δ}{σ σ' : Sub Γ Δ} → σ ≡ σ' → [ σ ]l Ξ ≡ [ σ' ]l Ξ
[]lΞ` {Ξ = Ξ} = cong λ σ → [ σ ]l Ξ

-- congruence rules for constructors
,C` : (Γ≡Γ' : Γ ≡ Γ')(A≡A' : conv (Ty` Γ≡Γ') A ≡ A') → (Γ , A) ≡ (Γ' , A')
,C` refl refl = refl

,L` : {Ξ Ξ' : Lift Γ}{A : Ty (Γ ++ Ξ)}{A' : Ty (Γ ++ Ξ')}
    → (Ξ≡Ξ' : Ξ ≡ Ξ')(A≡A' : conv (Ty` (cong (Γ ++_) Ξ≡Ξ')) A ≡ A')
    → Ξ , A ≡ Ξ' , A'
,L` {Ξ = Ξ} refl = cong (Ξ ,_)

-- ,Sub` : {σ σ' : Sub Δ Γ}{A A' : Ty Γ}{t : Tm Δ (A [ σ ])}{t' : Tm Δ (A' [ σ' ])}
--       → (A≡A' : A ≡ A')(σ≡σ' : σ ≡ σ') → conv (TmΓ` ([]` {Δ} refl refl A≡A' σ≡σ')) t ≡ t'
--       → conv (Sub` refl (,Ctx` refl A≡A')) (_,_ {A = A} σ t) ≡ _,_ {A = A'} σ' t'
-- ,Sub` {σ = σ} refl refl = cong (σ ,_)

Π` : {A A' : Ty Γ}{B : Ty (Γ , A)}{B' : Ty (Γ , A')}
   → (A≡A' : A ≡ A') → conv (Ty` (,C` refl A≡A')) B ≡ B'
   → Π A B ≡ Π A' B'
Π` {A = A} refl = cong (Π A)

⨟` : {σ σ' : Sub Γ Δ}{τ τ' : Sub Δ Θ}
   → σ ≡ σ' → τ ≡ τ'
   → σ ⨟ τ ≡ σ' ⨟ τ'
⨟` = cong₂ _⨟_