-- Congruence rules for SC.QIIRT2
module SC.QIIRT2.Cong where

open import Prelude
  hiding (_,_; _∘_)
open import SC.QIIRT2.Base

variable
  Γ' Δ' Θ' : Ctx

congTy : Γ ≡ Γ' → Ty Γ ≡ Ty Γ'
congTy refl = refl

congSub : Γ ≡ Γ' → Δ ≡ Δ' → Sub Γ Δ ≡ Sub Γ' Δ'
congSub refl refl = refl

congTm : (Γ≡Γ' : Γ ≡ Γ'){A : Ty Γ}{A' : Ty Γ'}
  → conv (congTy Γ≡Γ') A ≡ A' → Tm Γ A ≡ Tm Γ' A'
congTm refl refl = refl

congTmΓ : {A A' : Ty Γ} → A ≡ A' → Tm Γ A ≡ Tm Γ A'
congTmΓ = congTm refl

cong,Ctx : (Γ≡Γ' : Γ ≡ Γ'){A : Ty Γ}{A' : Ty Γ'}
         → (A≡A' : conv (congTy Γ≡Γ') A ≡ A')
         → (Γ , A) ≡ (Γ' , A')
cong,Ctx refl refl = refl

cong[] : (Γ≡Γ' : Γ ≡ Γ'){A : Ty Γ}{A' : Ty Γ'}
       → conv (congTy Γ≡Γ') A ≡ A'
       → (Δ≡Δ' : Δ ≡ Δ'){σ : Sub Δ Γ}{σ' : Sub Δ' Γ'}
       → conv (congSub Δ≡Δ' Γ≡Γ') σ ≡ σ'
       → conv (congTy Δ≡Δ') (A [ σ ]) ≡ A' [ σ' ]
cong[] refl refl refl refl = refl

congA[] : {A : Ty Γ}{σ σ' : Sub Δ Γ}
        → σ ≡ σ' → A [ σ ] ≡ A [ σ' ]
congA[] {A = A} = cong[] refl {A} refl refl

cong,Sub' : {σ σ' : Sub Δ Γ}{A A' : Ty Γ}{t : Tm Δ (A [ σ ])}{t' : Tm Δ (A' [ σ' ])}
            → (A≡A' : A ≡ A')(σ≡σ' : σ ≡ σ') → conv (congTmΓ (cong[] {Γ} refl A≡A' refl σ≡σ')) t ≡ t'
            → conv (congSub refl (cong,Ctx refl A≡A')) (_,_ {A = A} σ t) ≡ _,_ {A = A'} σ' t'
cong,Sub' {σ = σ} refl refl t≡t' = cong (σ ,_) t≡t'

cong∘ : (Γ≡Γ' : Γ ≡ Γ')(Δ≡Δ' : Δ ≡ Δ')(Θ≡Θ' : Θ ≡ Θ')
        {σ : Sub Δ Γ}{σ' : Sub Δ' Γ'}{τ : Sub Θ Δ}{τ' : Sub Θ' Δ'}
        (σ≡σ' : conv (congSub Δ≡Δ' Γ≡Γ') σ ≡ σ')(τ≡τ' : conv (congSub Θ≡Θ' Δ≡Δ') τ ≡ τ')
      → conv (congSub Θ≡Θ' Γ≡Γ') (σ ∘ τ) ≡ σ' ∘ τ'
cong∘ refl refl refl refl refl = refl

cong∘' : {σ σ' : Sub Δ Γ}{τ τ' : Sub Θ Δ}
        → σ ≡ σ' → τ ≡ τ'
        → σ ∘ τ ≡ σ' ∘ τ'
cong∘' refl refl = refl
