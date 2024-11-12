module Prelude where

open import Data.Unit public
open import Data.Product public
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning) renaming (subst to tr) public
open ≡-Reasoning public