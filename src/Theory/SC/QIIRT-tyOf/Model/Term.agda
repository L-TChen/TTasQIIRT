open import Prelude

module Theory.SC.QIIRT-tyOf.Model.Term where

open import Theory.SC.QIIRT-tyOf.Syntax
open import Theory.SC.QIIRT-tyOf.Model

TermM : Motive
TermM = record
  { Ctx  = Ctx
  ; Ty   = Ty
  ; Sub  = Sub
  ; Tm   = Tm
  ; tyOf = tyOf
  ; Ty-is-set = Ty-is-set
  ; Sub-is-set = Sub-is-set
  ; Tm-is-set = Tm-is-set
  }

TermIsSC : IsSC TermM
TermIsSC = record
  { ∅       = ∅
  ; _,C_    = _,_
  ; _[_]T   = _[_]
  ; _[_]t   = _[_]
  ; tyOf[]  = refl
  ; ∅S      = ∅
  ; _,_∶[_] = _,_∶[_]
  ; idS     = idS
  ; _∘_     = _∘_
  ; π₁      = π₁
  ; π₂      = π₂
  ; tyOfπ₂  = λ _ → refl
  ; idS∘_   = idS∘_
  ; _∘idS   = _∘idS
  ; assocS  = assocS
  ; [idS]T  = [idS]T
  ; [∘]T    = [∘]T
  ; ,∘      = ,∘
  ; ηπ      = ηπ
  ; η∅      = η∅
  ; βπ₁     = βπ₁
  ; βπ₂     = λ {Γ} {Δ} {A} σ t p
    → βπ₂ σ t p (cong (A [_]) (βπ₁ σ t p) ∙ sym p)
  ; [idS]t  = [idS]t
  ; [∘]t    = [∘]t
  ; U       = U
  ; U[]     = U[]
  ; tyOf[]≡U = λ {σ = σ} p
    → cong (λ A → A [ σ ]) p ∙ U[]
  }

Term : SC _ _ _ _
Term = record { mot = TermM ; isSC = TermIsSC }

Ctx-is-Set : isSet Ctx
Ctx-is-Set = Ctx-is-set
