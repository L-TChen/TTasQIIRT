-- translation of syntax between QIIRT and QIIT
open import Prelude

module SC+U+Pi+Id.Translation.Syntax.Translate where

open import SC+U+Pi+Id.Recursion.Rec

module QIIRT→QIIT where
  open import SC+U+Pi+Id.Translation.Syntax.toQIIT
    using (toQIIT)
  _>c = recCtxᴵᴿ toQIIT
  _>ty = recTyᴵᴿ toQIIT
  _>s = recSubᴵᴿ toQIIT
  _>tm = recTmᴵᴿ toQIIT
  []>ty = recTyᴵᴿ[] toQIIT
  []>tm = recTmᴵᴿ[] toQIIT
  ↑>Sub = recSubᴵᴿ↑ toQIIT

module QIIT→QIIRT where
  open import SC+U+Pi+Id.Translation.Syntax.toQIIRT
    using (toQIIRT)
  _<c = recCtxᴵ toQIIRT
  _<ty = recTyᴵ toQIIRT
  _<s = recSubᴵ toQIIRT
  _tm = recTmᴵ toQIIRT