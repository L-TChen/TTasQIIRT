-- translation between recursor of QIIT and recursor of QIIRT
open import Prelude

module SC+U+Pi+Id.Translation.Recursor.Translate where
import SC+U+Pi+Id.QIIT.Recursion as I
import SC+U+Pi+Id.QIIRT.Recursion as IR

module QIIT→QIIRT where
  open import SC+U+Pi+Id.Translation.Recursor.toQIIRT
  
  _<r : ∀{ℓ ℓ′} → I.Recursor {ℓ} {ℓ′} → IR.Recursor {ℓ} {ℓ′}
  rec <r = toQIIRT rec
