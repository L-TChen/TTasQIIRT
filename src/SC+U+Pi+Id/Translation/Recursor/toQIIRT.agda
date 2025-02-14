{-# OPTIONS --allow-unsolved-metas #-}
open import Prelude

module SC+U+Pi+Id.Translation.Recursor.toQIIRT where

open import SC+U+Pi+Id.QIIT.Syntax
open import SC+U+Pi+Id.QIIT.Properties
open import SC+U+Pi+Id.QIIT.Recursion

import SC+U+Pi+Id.QIIRT.Syntax as IR
  -- hiding (i) 
import SC+U+Pi+Id.QIIRT.Recursion as IR

module _  {ℓ ℓ′}(rec : Recursor {ℓ} {ℓ′}) where
  open Recursor rec
  -- derived equalities of QIIT Recursor
  private
    variable
      Γᴹ Δᴹ Θᴹ Φᴹ : Ctxᴹ
      σᴹ τᴹ γᴹ    : Subᴹ Γᴹ Δᴹ
      Aᴹ Bᴹ Cᴹ    : Tyᴹ Γᴹ i
      aᴹ tᴹ uᴹ    : Tmᴹ Γᴹ Aᴹ
    

  toQIIRT : IR.Recursor {ℓ} {ℓ′}
  toQIIRT .IR.Recursor.mot = record
    { Ctxᴹ = Ctxᴹ
    ; Tyᴹ  = Tyᴹ
    ; Subᴹ = Subᴹ
    ; Tmᴹ  = Tmᴹ
    }
  toQIIRT .IR.Recursor.met = record
    { 𝒞 = record
      { [_]ᴹ_     = [_]ᴹ_
      ; ∅ᶜᴹ       = ∅ᶜᴹ
      ; _,ᶜᴹ_     = _,ᶜᴹ_
      ; ∅ˢᴹ       = ∅ˢᴹ
      ; _,ˢᴹ_     = _,ˢᴹ_
      ; idSᴹ      = idSᴹ
      ; _⨟ᴹ_      = _⨟ᴹ_
      ; π₁ᴹ       = π₁ᴹ
      ; [idS]ᴹ    = [idS]ᴹ
      ; [⨟]ᴹ      = [⨟]ᴹ
      ; [π₁,]ᴹ    = λ {_} {_} {σᴹ} {_} {A'ᴹ} {tᴹ} {_} {Aᴹ}
                  → cong ([_]ᴹ Aᴹ) π₁,ᴹ
      ; [π₁⨟]ᴹ    = λ {_} {_} {σᴹ} {_} {_} {_} {τᴹ} {_} {Aᴹ}
                  → cong ([_]ᴹ Aᴹ) (π₁⨟ᴹ σᴹ τᴹ) ∙ [⨟]ᴹ
      ; π₂ᴹ       = π₂ᴹ
      ; [_]tmᴹ_   = [_]tmᴹ_
      ; _↑ᴹ_      = _↑ᴹ_
      ; idS↑ᴹ     = idS↑ᴹ
      ; ⨟↑ᴹ       = {!   !}
      ; π₁,↑ᴹ     = π₁,↑ᴹ
      ; π₁⨟↑ᴹ     = {!   !}
      ; ∅↑ᴹ       = refl
      ; ,↑ᴹ       = refl
      ; π₁idS↑ᴹ   = refl
      ; π₁π₁↑ᴹ    = refl
      ; [_]tᴹ_    = [_]tmᴹ_
      ; [idS]tᴹ   = [idS]tmᴹ
      ; [⨟]tᴹ     = [⨟]tmᴹ
      ; [π₁,]tᴹ   = λ {Γᴹ} {Δᴹ} {σᴹ} {_} {_} {tᴹ} {_} {Aᴹ} {uᴹ}
                  → sym (tr-cong {P = TmᴹFam} π₁,ᴹ)
                  ∙ tr-nat (λ _ → ⊤) (λ τᴹ _ → [ τᴹ ]tmᴹ uᴹ) π₁,ᴹ
      ; [π₁⨟]tᴹ   = λ {Γᴹ} {Δᴹ} {σᴹ} {Θᴹ} {_} {_} {τᴹ} {_} {Aᴹ} {tᴹ}
                  → sym (tr² (cong ([_]ᴹ Aᴹ) (π₁⨟ᴹ σᴹ τᴹ)))
                  ∙ cong (tr TmᴹFam [⨟]ᴹ) (sym (tr-cong {P = TmᴹFam} (π₁⨟ᴹ σᴹ τᴹ)))
                  ∙ cong (tr TmᴹFam [⨟]ᴹ) (apd ([_]tmᴹ tᴹ) (π₁⨟ᴹ σᴹ τᴹ))
                  ∙ [⨟]tmᴹ
      ; [∅]tᴹ     = refl
      ; [,]tᴹ     = refl
      ; [π₁idS]tᴹ = refl
      ; [π₁π₁]tᴹ  = refl
      ; _⨟idSᴹ    = _⨟idSᴹ
      ; idS⨟ᴹ_    = idS⨟ᴹ_
      ; ⨟-assocᴹ  = ⨟-assocᴹ
      ; π₁,ᴹ      = π₁,ᴹ
      ; ⨟,ᴹ       = ⨟,ᴹ
      ; η∅ᴹ       = η∅ᴹ
      ; η,ᴹ       = η,ᴹ
      ; [idS]tmᴹ  = [idS]tmᴹ
      ; [⨟]tmᴹ    = [⨟]tmᴹ
      ; π₂,ᴹ      = λ {Γᴹ} {Δᴹ} {σᴹ} {_} {Aᴹ} {tᴹ}
                  → (sym $ tr-cong {P = TmᴹFam} π₁,ᴹ) ∙ π₂,ᴹ
      }
    ; univ = record 
      { Uᴹ      = Uᴹ
      ; Elᴹ     = Elᴹ
      ; Liftᴹ   = Liftᴹ
      ; cᴹ      = cᴹ
      ; mkᴹ     = mkᴹ
      ; unᴹ     = unᴹ
      ; []Uᴹ    = []Uᴹ
      ; []Elᴹ   = []Elᴹ
      ; []Liftᴹ = []Liftᴹ
      ; []tcᴹ   = []tcᴹ
      ; []mkᴹ   = []mkᴹ
      ; []unᴹ   = []unᴹ
      ; Uβᴹ     = Uβᴹ
      ; Uηᴹ     = Uηᴹ
      ; Liftβᴹ  = Liftβᴹ
      ; Liftηᴹ  = Liftηᴹ
      }
    ; piTy = record
      { Πᴹ   = Πᴹ
      ; ƛᴹ_  = ƛᴹ_
      ; appᴹ = appᴹ
      ; []Πᴹ = []Πᴹ
      ; []ƛᴹ = []ƛᴹ
      ; Πβᴹ  = Πβᴹ
      ; Πηᴹ  = Πηᴹ
      }
    ; idTy = record
      { Idᴹ      = Idᴹ
      ; []Idᴹ    = []Idᴹ
      ; reflᴹ    = reflᴹ
      ; []reflᴹ  = []reflᴹ
      ; reflectᴹ = reflectᴹ
      }
    }
