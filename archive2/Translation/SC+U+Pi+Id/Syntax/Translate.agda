-- translation of syntax between QIIRT and QIIT
open import Prelude

module Translation.SC+U+Pi+Id.Syntax.Translate where


module QIIRT→QIIT where
  open import Translation.SC+U+Pi+Id.Syntax.toQIIT
  open import Theory.SC+U+Pi+Id.QIIRT.Recursion

  _>c = recCtx toQIIT
  _>ty = recTy toQIIT
  _>s = recSub toQIIT
  _>tm = recTm toQIIT
  []>ty = recTy[] toQIIT
  []>tm = recTm[] toQIIT
--  ↑>Sub = recSub↑ toQIIT

module QIIT→QIIRT where
  open import Translation.SC+U+Pi+Id.Syntax.toQIIRT
  open import Theory.SC+U+Pi+Id.QIIT.Recursion
  _<c  = recCtx toQIIRT
  _<ty = recTy toQIIRT
  _<s  = recSub toQIIRT
  _<tm  = recTm toQIIRT
