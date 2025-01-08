-- Model of Substitution Calculus
module SC+U+Pi+Id.QIIRT.Model where

open import Prelude
  hiding (_,_)
open import Data.Nat hiding (_⊔_)
open import SC+U+Pi+Id.QIIRT.Base
open import SC+U+Pi+Id.QIIRT.Properties

private variable
  Δ' Φ : Ctx
  A' B' C' : Ty Γ i
  σ' τ' γ' : Sub Γ Δ

open import SC+U+Pi+Id.QIIRT.Model.Motives public
open import SC+U+Pi+Id.QIIRT.Model.Methods public

record Model {ℓ ℓ′} : Set (lsuc (ℓ ⊔ ℓ′)) where
  field
    pdc : Pred {ℓ} {ℓ′}
    alg : Method pdc
  
  open Pred   pdc public
  open Method alg public
