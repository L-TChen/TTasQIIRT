open import Prelude

module Theory.SC+U+Pi+Id.QIIRT.Elimination where

open import Theory.SC+U+Pi+Id.QIIRT.Elimination.Motive
open import Theory.SC+U+Pi+Id.QIIRT.Elimination.Method

record Eliminator {ℓ ℓ′ : Level} : Set (lsuc (ℓ ⊔ ℓ′)) where
  field
    mot : Motive ℓ ℓ′
    met : Method mot

  open Motive mot public
  open Method met public
