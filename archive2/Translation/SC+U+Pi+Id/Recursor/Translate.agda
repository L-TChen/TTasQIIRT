-- translation between recursor of QIIT and recursor of QIIRT
open import Prelude

module Translation.SC+U+Pi+Id.Recursor.Translate where
import Theory.SC+U+Pi+Id.QIIT.Recursion as I
import Theory.SC+U+Pi+Id.QIIRT.Recursion as IR

module QIIT→QIIRT where
  open import Translation.SC+U+Pi+Id.Recursor.toQIIRT
  
  _<r : ∀{ℓ ℓ′} → I.Recursor {ℓ} {ℓ′} → IR.Recursor {ℓ} {ℓ′}
  rec <r = toQIIRT rec
