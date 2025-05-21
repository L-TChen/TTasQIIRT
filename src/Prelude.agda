module Prelude where

open import Cubical.Foundations.Prelude public
  hiding (Sub)
open import Cubical.Data.Sigma          public
  hiding (Sub)
open import Cubical.Data.Empty          public
open import Cubical.Data.Unit           public
open import Cubical.Data.Nat            public
  using (ℕ; zero; suc; _+_)
open import Cubical.Data.Bool           public
  using (Bool; true; false)
