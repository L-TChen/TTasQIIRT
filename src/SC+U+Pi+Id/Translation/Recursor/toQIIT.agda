open import Prelude

module SC+U+Pi+Id.Translation.Recursor.toQIIT where

open import SC+U+Pi+Id.QIIRT.Syntax
open import SC+U+Pi+Id.QIIRT.Properties
open import SC+U+Pi+Id.QIIRT.Recursion

import SC+U+Pi+Id.QIIT.Syntax as I
import SC+U+Pi+Id.QIIT.Recursion as I

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
      { C₁ = record
        { [_]ᴹ_ = [_]ᴹ_
        ; ∅ᶜᴹ = ∅ᶜᴹ
        ; _,ᶜᴹ_ = _,ᶜᴹ_
        ; ∅ˢᴹ = ∅ˢᴹ
        ; _,ˢᴹ_ = _,ˢᴹ_
        ; idSᴹ = idSᴹ
        ; _⨟ᴹ_ = _⨟ᴹ_
        ; π₁ᴹ = π₁ᴹ
        ; [idSᴹ] = [idSᴹ]
        ; [⨟ᴹ]ᴹ = [⨟ᴹ]ᴹ
        ; π₂ᴹ = π₂ᴹ
        ; [_]tmᴹ_ = [_]tmᴹ_
        }
      ; C₂ = record
        { _⨟ᴹidSᴹ = _⨟ᴹidSᴹ
        ; idSᴹ⨟ᴹ_ = idSᴹ⨟ᴹ_
        ; ⨟ᴹ-assoc = ⨟ᴹ-assoc
        ; π₁ᴹ,ˢᴹ = π₁ᴹ,ˢᴹ
        ; ⨟ᴹ,ˢᴹ = ⨟ᴹ,ˢᴹ -- ⨟ᴹ,ˢᴹ
        ; η∅ˢᴹ = η∅ˢᴹ
        ; η,ˢᴹ = η,ˢᴹ
        ; [idSᴹ]tmᴹ = [idSᴹ]tmᴹ
        ; [⨟ᴹ]tmᴹ = [⨟ᴹ]tmᴹ
        ; π₂ᴹ,ˢᴹ = λ {Δᴹ} {_} {Γᴹ} {Aᴹ} {σᴹ} {tᴹ}
                 → tr-cong {P = Tmᴹ Γᴹ} π₁ᴹ,ˢᴹ
                 ∙ cong (λ p → tr (Tmᴹ Γᴹ) p (π₂ᴹ (σᴹ ,ˢᴹ tᴹ))) (uip _ _)
                 ∙ π₂ᴹ,ˢᴹ
        }
      }
    ; univ = record 
      { Uᴹ = Uᴹ
      ; Elᴹ = Elᴹ
      ; Liftᴹ = Liftᴹ
      ; cᴹ = cᴹ
      ; mkᴹ = mkᴹ
      ; unᴹ = unᴹ
      ; []ᴹUᴹ = []ᴹUᴹ
      ; []ᴹElᴹ = {! []ᴹElᴹ   !} -- []ᴹElᴹ
      ; []ᴹLiftᴹ = []ᴹLiftᴹ
      ; []tᴹcᴹ = []tᴹcᴹ
      ; []mkᴹ = {!  []mkᴹ !} -- []mkᴹ
      ; []unᴹ = []unᴹ
      ; Uᴹβ = Uᴹβ
      ; Uᴹη = Uᴹη
      ; Liftᴹβ = Liftᴹβ
      ; Liftᴹη = Liftᴹη
      }
    ; piTy = record
      { Πᴹ = Πᴹ
      ; ƛᴹ_ = ƛᴹ_
      ; appᴹ = appᴹ
      ; []ᴹΠᴹ = {!   !} -- []ᴹΠᴹ
      ; []ƛᴹ = {!   !} -- []ƛᴹ
      ; Πβᴹ = Πβᴹ
      ; Πηᴹ = Πηᴹ
      }
    ; idTy = record
      { Idᴹ = Idᴹ
      ; []ᴹIdᴹ = {!   !} -- []ᴹIdᴹ
      ; reflᴹ = reflᴹ
      ; []reflᴹ = {!   !} -- []reflᴹ
      ; reflectᴹ = reflectᴹ
      }
    }