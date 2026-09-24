------------------------------------------------------------------------
-- Local compatibility shim (build-support only, kept outside the project):
-- agda-stdlib 2.1 does not ship Data.Rational.Tactic.RingSolver, which
-- newer stdlib versions provide.  This reproduces it from the generic
-- Tactic.RingSolver over the rational commutative ring.
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Data.Rational.Tactic.RingSolver where

open import Agda.Builtin.Reflection using (Term; TC)

open import Algebra.Bundles using (CommutativeRing)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Rational.Base using (ℚ)
open import Data.Rational.Properties using (+-*-commutativeRing; _≟_)
open import Data.Unit.Base using (⊤)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)
open import Relation.Nullary.Decidable.Core using (yes; no)

import Tactic.RingSolver as Solver
import Tactic.RingSolver.Core.AlmostCommutativeRing as ACR

private
  open CommutativeRing +-*-commutativeRing using (0#)

  isZero : (x : ℚ) → Maybe (0# ≡ x)
  isZero x with 0# ≟ x
  ... | yes p = just p
  ... | no _ = nothing

ring : ACR.AlmostCommutativeRing 0ℓ 0ℓ
ring = ACR.fromCommutativeRing +-*-commutativeRing isZero

macro
  solve-∀ : Term → TC ⊤
  solve-∀ = Solver.solve-∀-macro (quote ring)

macro
  solve : Term → Term → TC ⊤
  solve n = Solver.solve-macro n (quote ring)
