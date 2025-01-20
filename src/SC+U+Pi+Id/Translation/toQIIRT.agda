open import Prelude
  hiding (_,_)

module SC+U+Pi+Id.Translation.toQIIRT where

open import SC+U+Pi+Id.QIIRT.Base     as QIIRT
open import SC+U+Pi+Id.QIIRT.Properties as QIIRT

import SC+U+Pi+Id.QIIT.Syntax as Q
  hiding (i)

open import SC+U+Pi+Id.QIIT.Elimination

open Eliminator

open ≡-Reasoning
toQIIRT : Eliminator
toQIIRT .mot = record
  { Ctxᴹ = λ Γ → Ctx
  ; Tyᴹ  = λ Γ i A → Ty Γ i
  ; Subᴹ = λ Γ Δ σ → Sub Γ Δ
  ; Tmᴹ  = λ Γ A t → Tm Γ A
  }
toQIIRT .met = record
  { 𝒞 = record
    { C₁ = record
      { [_]ᴹ_ = [_]_
      ; ∅ᶜᴹ = ∅
      ; _,ᶜᴹ_ = _,_
      ; ∅ˢᴹ = ∅
      ; _,ˢᴹ_ = λ σ t → σ , t
      ; idSᴹ = idS
      ; _⨟ᴹ_ = _⨟_
      ; π₁ᴹ = π₁
      ; [idSᴹ] = tr-const Q.[idS]
      ; [⨟ᴹ]ᴹ = tr-const Q.[⨟]
      ; π₂ᴹ = π₂
      ; [_]tmᴹ_ = [_]t_
      }
    ; C₂ = record
      { _⨟ᴹidSᴹ = λ {_} {_} {_} {_} {Qσ} σ → tr-const (Qσ Q.⨟idS) {σ ⨟ idS} ∙ (σ ⨟idS)
      ; idSᴹ⨟ᴹ_ = λ {_} {_} {_} {_} {Qσ} σ → tr-const (Q.idS⨟ Qσ) {idS ⨟ σ} ∙ (idS⨟ σ)
      ; ⨟ᴹ-assoc = tr-const Q.⨟-assoc ∙ ⨟-assoc
      ; π₁ᴹ,ˢᴹ = tr-const Q.π₁, ∙ π₁,
      ; ⨟ᴹ,ˢᴹ = λ {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_}
                  {σ} {τ} {t}
              → tr-const Q.⨟, ∙ ⨟, ∙
                cong (σ ⨟ τ ,_) (sym {!   !})
      ; η∅ˢᴹ = tr-const Q.η∅ ∙ η∅
      ; η,ˢᴹ = tr-const Q.η, ∙ η,
      ; [idSᴹ]tmᴹ = tr-const Q.[idS]tm ∙ {!   !}
      ; [⨟ᴹ]tmᴹ = tr-const Q.[⨟]tm ∙ {!   !}
      ; π₂ᴹ,ˢᴹ = tr-const Q.π₂, ∙ {!   !}
      }
    }
  ; univ = record
    { Uᴹ = U
    ; Elᴹ = El
    ; Liftᴹ = Lift
    ; cᴹ = c
    ; mkᴹ = mk
    ; unᴹ = un
    ; []ᴹUᴹ = λ {_} {_} {_} {_} {_} {σ} {i}
              → tr-const Q.[]U ∙ []U {_} {_} {σ} {i}
    ; []ᴹElᴹ = λ {_} {_} {_} {_} {σ} {_} {u} σᴹ uᴹ
               → tr-const (Q.[]El σ u) ∙ {!   !}
    ; []ᴹLiftᴹ = λ {_} {_} {_} {_} {_} {σᴹ} {_} {_} {Aᴹ}
              → tr-const Q.[]Lift ∙ []Lift {_} {_} {σᴹ} {_} {Aᴹ}
    ; []tᴹcᴹ = λ {_} {_} {_} {_} {σ} {_} {A} σᴹ Aᴹ
               → tr-const (Q.[]tc σ A) ∙ {!   !}
    ; []mkᴹ = λ {_} {_} {_} {_} {_} {_} {_} {t} {tᴹ} σ σᴹ
              → tr-const (Q.[]mk σ t) ∙ {!   !}
    ; []unᴹ = λ {_} {_} {_} {_} {σ} {_} {A} {t} σᴹ {Aᴹ} tᴹ
              → tr-const (Q.[]un σ A t) ∙ []un σᴹ Aᴹ tᴹ ∙ cong un {!   !}
    ; Uᴹβ = tr-const Q.Uβ ∙ Uβ
    ; Uᴹη = tr-const Q.Uη ∙ Uη
    ; Liftᴹβ = tr-const Q.Liftβ ∙ Liftβ
    ; Liftᴹη = tr-const Q.Liftη ∙ Liftη
    }
  ; piTy = record
    { Πᴹ = Π
    ; ƛᴹ_ = ƛ_
    ; appᴹ = app
    ; []ᴹΠᴹ = λ {_} {_} {_} {_} {_} {σᴹ} {_} {_} {Aᴹ} {_} {Bᴹ}
              → tr-const Q.[]Π ∙ cong (Π ([ σᴹ ] Aᴹ)) {!   !}
    ; []ƛᴹ = λ {_} {_} {_} {_} {_} {_} {_} {_} {_} {t} {tᴹ} σ σᴹ 
             → tr-const (Q.[]ƛ σ t) ∙ {!   !}
    ; Πβᴹ = tr-const Q.Πβ ∙ Πβ
    ; Πηᴹ = tr-const Q.Πη ∙ Πη
    }
  ; idTy = record
    { Idᴹ = Id
    ; []ᴹIdᴹ = tr-const Q.[]Id ∙ {!   !} 
    ; reflectᴹ = λ pᴹ → tr-const (Q.reflect _) ∙ reflect pᴹ
    }
  } 