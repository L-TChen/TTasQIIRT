-- translation of syntax between QIIRT and QIIT
module SC+U+Pi+Id.Translation.Syntax.Translate where
open import Prelude


record Syntax : Set₁ where
  field
    Ctx : Set
    Ty : Ctx → ℕ → Set
    Sub : Ctx → Ctx → Set
    Tm : {i : ℕ}(Γ : Ctx) → Ty Γ i → Set

record From_To_ (S₁ S₂ : Syntax) : Set₁ where
  open Syntax
  field
    _>c : S₁ .Ctx → S₂ .Ctx
    _>ty  : {i : ℕ}{Γ : S₁ .Ctx} → S₁ .Ty Γ i → S₂ .Ty (Γ >c) i
    _>s : {Γ Δ : S₁ .Ctx} → S₁ .Sub Γ Δ → S₂ .Sub (Γ >c) (Δ >c)
    _>tm : {Γ : S₁ .Ctx}{i : ℕ}{A : S₁ .Ty Γ i} → S₁ .Tm Γ A → S₂ .Tm (Γ >c) (A >ty)

import SC+U+Pi+Id.QIIRT.Base as RS
import SC+U+Pi+Id.QIIT.Syntax as QS

QIIRTSyn : Syntax
QIIRTSyn = record
  { Ctx = RS.Ctx
  ; Ty  = RS.Ty
  ; Sub = RS.Sub
  ; Tm  = RS.Tm
  }

QIITSyn : Syntax
QIITSyn = record
  { Ctx = QS.Ctx
  ; Ty  = QS.Ty
  ; Sub = QS.Sub
  ; Tm  = QS.Tm
  }

QIIRT→QIIT : From QIIRTSyn To QIITSyn
QIIRT→QIIT = record
  { _>c = ElimCtx
  ; _>ty = ElimTy
  ; _>s = ElimSub
  ; _>tm = ElimTm
  }
  where
    open import SC+U+Pi+Id.Translation.Syntax.toQIIT
      using (toQIIT)
    open import SC+U+Pi+Id.QIIRT.Elimination
    open elim toQIIT