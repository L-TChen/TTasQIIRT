open import Prelude

module Translation.SC+U+Pi+Id.Recursor.toQIIT where

open import Theory.SC+U+Pi+Id.QIIRT.Syntax
open import Theory.SC+U+Pi+Id.QIIRT.Properties
open import Theory.SC+U+Pi+Id.QIIRT.Recursion

import Theory.SC+U+Pi+Id.QIIT.Syntax as I
import Theory.SC+U+Pi+Id.QIIT.Recursion as I

module _  {ℓ ℓ′}(rec : Recursor {ℓ} {ℓ′}) where
  open Recursor rec
  toQIIT : I.Recursor {ℓ} {ℓ′}
  toQIIT .I.Recursor.mot = record
    { Ctxᴹ = Ctxᴹ
    ; Tyᴹ  = Tyᴹ
    ; Subᴹ = Subᴹ
    ; Tmᴹ  = Tmᴹ
    }
  toQIIT .I.Recursor.met = record
    { 𝒞 = record
      { [_]ᴹ_   = [_]ᴹ_
      ; ∅ᶜᴹ     = ∅ᶜᴹ
      ; _,ᶜᴹ_   = _,ᶜᴹ_
      ; ∅ˢᴹ     = ∅ˢᴹ
      ; _,ˢᴹ_   = _,ˢᴹ_
      ; idSᴹ    = idSᴹ
      ; _⨟ᴹ_    = _⨟ᴹ_
      ; π₁ᴹ     = π₁ᴹ
      ; [idS]ᴹ  = [idS]ᴹ
      ; [⨟]ᴹ    = [⨟]ᴹ
      ; π₂ᴹ     = π₂ᴹ
      ; [_]tmᴹ_ = [_]tmᴹ_
      ; _⨟idSᴹ   = _⨟idSᴹ
      ; idS⨟ᴹ_   = idS⨟ᴹ_
      ; ⨟-assocᴹ = ⨟-assocᴹ
      ; π₁,ᴹ     = π₁,ᴹ
      ; ⨟,ᴹ      = ⨟,ᴹ
      ; η∅ᴹ      = η∅ᴹ
      ; η,ᴹ      = η,ᴹ
      ; [idS]tmᴹ = [idS]tmᴹ
      ; [⨟]tmᴹ   = [⨟]tmᴹ
      ; π₂,ᴹ     = λ {Δᴹ} {_} {Γᴹ} {Aᴹ} {σᴹ} {tᴹ}
                  → tr-cong {P = Tmᴹ Γᴹ} π₁,ᴹ
                  ∙ cong (λ p → tr (Tmᴹ Γᴹ) p (π₂ᴹ (σᴹ ,ˢᴹ tᴹ))) (uip _ _)
                  ∙ π₂,ᴹ
      }
    ; univ = record 
      { Uᴹ      = Uᴹ
      ; Elᴹ     = Elᴹ
      ; Liftᴹ   = Liftᴹ
      ; cᴹ      = cᴹ
      ; mkᴹ     = mkᴹ
      ; unᴹ     = unᴹ
      ; []Uᴹ    = []Uᴹ
      ; []Elᴹ   = {! []Elᴹ   !} 
      ; []Liftᴹ = []Liftᴹ
      ; []tcᴹ   = []tcᴹ
      ; []mkᴹ   = {!  []mkᴹ !}
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
      ; []Πᴹ = {!   !} -- []Πᴹ
      ; []ƛᴹ = {!   !} -- []ƛᴹ
      ; Πβᴹ  = Πβᴹ
      ; Πηᴹ  = Πηᴹ
      }
    ; idTy = record
      { Idᴹ      = Idᴹ
      ; []Idᴹ    = {!   !} -- []Idᴹ
      ; reflᴹ    = reflᴹ
      ; []reflᴹ  = {!   !} -- []reflᴹ
      ; reflectᴹ = reflectᴹ
      }
    }