-- translation of syntax between QIIRT and QIIT
open import Prelude

module SC+U+Pi+Id.Translation.Syntax.Translate where


module QIIRT→QIIT where
  open import SC+U+Pi+Id.Translation.Syntax.toQIIT
  open import SC+U+Pi+Id.QIIRT.Recursion

  _>c = recCtx toQIIT
  _>ty = recTy toQIIT
  _>s = recSub toQIIT
  _>tm = recTm toQIIT
  []>ty = recTy[] toQIIT
--  []>tm = recTm[] toQIIT
--  ↑>Sub = recSub↑ toQIIT

module QIIT→QIIRT where
  open import SC+U+Pi+Id.Translation.Syntax.toQIIRT
  open import SC+U+Pi+Id.QIIT.Recursion
  _<c  = recCtx toQIIRT
  _<ty = recTy toQIIRT
  _<s  = recSub toQIIRT
  _tm  = recTm toQIIRT
