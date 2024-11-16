{-# OPTIONS --exact-split --rewriting -vtc.cover.splittree:10 #-}
module DTT-QIIRT.Renaming where

open import DTT-QIIRT.Base

data Var : (Γ : Ctx) → Ty Γ → Set where
  ze : Var (Γ ‣ A) (A [ π₁ idS ]) -- (A [ π₁ idS ]ᵀ)
  su : Var Γ A → Var (Γ ‣ B) (A [ π₁ idS ]) -- (A [ π₁ idS ]ᵀ)

infix 40 `_
`_ : Var Γ A → Tm Γ A
` ze = vz 
` su x = vs (` x)

data Ren : Ctx → Ctx → Set
⌞_⌟ : Ren Δ Γ → Sub Δ Γ

data Ren where
  ∅ : Ren Δ ∅
  _‣_ : (ρ : Ren Δ Γ) → Var Δ (A [ ⌞ ρ ⌟ ]) → Ren Δ (Γ ‣ A)

⌞ ∅ ⌟ = ∅ 
⌞ ρ ‣ x ⌟ = ⌞ ρ ⌟ ‣ ` x

data Ne : (Γ : Ctx) → Ty Γ → Set
data Nf : (Γ : Ctx) → Ty Γ → Set
⌜_⌝ne : Ne Γ A → Tm Γ A
⌜_⌝nf : Nf Γ A → Tm Γ A

data Ne where
  var
    : Var Γ A
    → Ne Γ A
  app
    : Ne Γ (Π A B) → (n : Nf Γ A)
    → Ne Γ (B [ vz:= ⌜ n ⌝nf ]) 

data Nf where
  neuU
    : Ne Γ U
    → Nf Γ U
  
  neuEl
    : {u : Tm Γ U} → Ne Γ (El u)
    → Nf Γ (El u)
  
  lam
    : Nf (Γ ‣ A) B
    → Nf Γ (Π A B)

⌜ var x ⌝ne = ` x
⌜ app t s ⌝ne = ⌜ t ⌝ne · ⌜ s ⌝nf
 
⌜ neuU t ⌝nf = ⌜ t ⌝ne 
⌜ neuEl t ⌝nf = ⌜ t ⌝ne
⌜ lam t ⌝nf = ƛ ⌜ t ⌝nf