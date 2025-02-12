open import Prelude
-- copy and modify from Theory
module SC+U+Pi+Id.Translation.Syntax.toQIIT where

open import SC+U+Pi+Id.QIIT.Syntax
open import SC+U+Pi+Id.QIIT.Properties
open import SC+U+Pi+Id.Recursion.Rec

open Recursor

toQIIT : Recursor
toQIIT .mot = record
  { Ctxᴹ = Ctx
  ; Tyᴹ  = Ty
  ; Subᴹ = Sub
  ; Tmᴹ  = Tm
  }
toQIIT .met = record
  { 𝒞    = record
    { C₁ = record
      { [_]ᴹ_       = [_]_
      ; ∅ᶜᴹ         = ∅
      ; _,ᶜᴹ_       = _,_
      ; ∅ˢᴹ         = ∅
      ; _,ˢᴹ_       = _,_
      ; idSᴹ        = idS
      ; _⨟ᴹ_        = _⨟_
      ; π₁ᴹ         = π₁
      ; [idSᴹ]      = [idS]
      ; [⨟ᴹ]ᴹ       = [⨟]
      ; π₂ᴹ         = π₂
      ; [_]tmᴹ_     = [_]tm_
      }
    ; C₂ = record
      { _⨟ᴹidSᴹ     = _⨟idS
      ; idSᴹ⨟ᴹ_     = idS⨟_
      ; ⨟ᴹ-assoc    = ⨟-assoc
      ; π₁ᴹ,ˢᴹ      = π₁,
      ; ⨟ᴹ,ˢᴹ       = ⨟,
      ; η∅ˢᴹ        = η∅
      ; η,ˢᴹ        = η,
      ; [idSᴹ]tmᴹ   = [idS]tm
      ; [⨟ᴹ]tmᴹ     = [⨟]tm
      ; π₂ᴹ,ˢᴹ      = π₂,
      }
    }
  ; univ = record
    { Uᴹ       = U
    ; Elᴹ      = El
    ; Liftᴹ    = Lift
    ; cᴹ       = c
    ; mkᴹ      = mk
    ; unᴹ      = un
    ; []ᴹUᴹ    = []U
    ; []ᴹElᴹ   = []El
    ; []ᴹLiftᴹ = []Lift
    ; []tᴹcᴹ   = []tc
    ; []mkᴹ    = []mk
    ; []unᴹ    = []un
    ; Uᴹβ      = Uβ
    ; Uᴹη      = Uη
    ; Liftᴹβ   = Liftβ
    ; Liftᴹη   = Liftη
    }
  ; piTy = record
    { Πᴹ    = Π
    ; ƛᴹ_   = ƛ_
    ; appᴹ  = app
    ; []ᴹΠᴹ = []Π
    ; []ƛᴹ  = []ƛ
    ; Πβᴹ   = Πβ
    ; Πηᴹ   = Πη
    }
  ; idTy = record
    { Idᴹ      = Id
    ; []ᴹIdᴹ   = []Id
    ; reflectᴹ = reflect
    }
  }