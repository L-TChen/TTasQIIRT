-- translation of syntax between QIIRT and QIIT
module SC+U+Pi+Id.Translation.Syntax.Translate where
open import Prelude

record Syntax : Set₁ where
  field
    Ctx : Set
    Ty : Ctx → ℕ → Set
    Sub : Ctx → Ctx → Set
    Tm : {i : ℕ}(Γ : Ctx) → Ty Γ i → Set
    [_]ty_ : {Γ Δ : Ctx}{i : ℕ} → Sub Γ Δ → Ty Δ i → Ty Γ i
    [_]tm_ : {i : ℕ}{Γ Δ : Ctx}(σ : Sub Γ Δ){A : Ty Δ i} → Tm Δ A → Tm Γ ([ σ ]ty A)

record From_To_ (S₁ S₂ : Syntax) : Set₁ where
  open Syntax
  field
    _>c : S₁ .Ctx → S₂ .Ctx
    _>ty  : {i : ℕ}{Γ : S₁ .Ctx} → S₁ .Ty Γ i → S₂ .Ty (Γ >c) i
    _>s : {Γ Δ : S₁ .Ctx} → S₁ .Sub Γ Δ → S₂ .Sub (Γ >c) (Δ >c)
    _>tm : {Γ : S₁ .Ctx}{i : ℕ}{A : S₁ .Ty Γ i} → S₁ .Tm Γ A → S₂ .Tm (Γ >c) (A >ty)
    []>ty : {i : ℕ}{Γ Δ : S₁ .Ctx}(σ : S₁ .Sub Γ Δ)(A : S₁ .Ty Δ i)
          → S₂ .[_]ty_ (σ >s) (A >ty) ≡ S₁ .[_]ty_ σ A >ty
    []>tm : {i : ℕ}{Γ Δ : S₁ .Ctx}(σ : S₁ .Sub Γ Δ){A : S₁ .Ty Δ i}(t : S₁ .Tm Δ A)
          → tr (S₂ .Tm (Γ >c)) ([]>ty σ A) (S₂ .[_]tm_ (σ >s) (t >tm)) ≡ (S₁ .[_]tm_ σ t >tm)

import SC+U+Pi+Id.QIIRT.Base as RS
import SC+U+Pi+Id.QIIT.Syntax as QS

QIIRTSyn : Syntax
QIIRTSyn = record
  { Ctx = RS.Ctx
  ; Ty  = RS.Ty
  ; Sub = RS.Sub
  ; Tm  = RS.Tm
  ; [_]ty_ = RS.[_]_
  ; [_]tm_ = RS.[_]t_
  }

QIITSyn : Syntax
QIITSyn = record
  { Ctx = QS.Ctx
  ; Ty  = QS.Ty
  ; Sub = QS.Sub
  ; Tm  = QS.Tm
  ; [_]ty_ = QS.[_]_
  ; [_]tm_ = QS.[_]tm_
  }

QIIRT→QIIT : From QIIRTSyn To QIITSyn
QIIRT→QIIT = record
  { _>c = ElimCtx
  ; _>ty = ElimTy
  ; _>s = ElimSub
  ; _>tm = ElimTm
  ; []>ty = ElimTy[]
  ; []>tm = ElimTm[]
  }
  where
    open import SC+U+Pi+Id.Translation.Syntax.toQIIT
      using (toQIIT)
    open import SC+U+Pi+Id.QIIRT.Elimination
    open elim toQIIT