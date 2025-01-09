-- Model of Substitution Calculus
module SC+U+Pi+Id.QIIRT.Model where

open import Prelude
  hiding (_,_)
open import Data.Nat hiding (_⊔_)
open import SC+U+Pi+Id.QIIRT.Base
open import SC+U+Pi+Id.QIIRT.Properties

open import SC+U+Pi+Id.QIIRT.Model.Motives public
open import SC+U+Pi+Id.QIIRT.Model.Methods public

record Model {ℓ ℓ′} : Set (lsuc (ℓ ⊔ ℓ′)) where
  field
    Mot : Motive {ℓ} {ℓ′}
    Met : Method Mot
  
  open Motive Mot public
  open Method Met public
