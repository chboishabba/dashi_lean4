{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- Translation of a 1-periodic function by an *arbitrary* rational point.
--
-- `DASHI.Analysis.BishopPeriodicShift` proves exact invariance of the uniform
-- Riemann sum under a shift by a multiple of the mesh that does not leave the
-- unit cell (`t ≤ suc m`), and `DASHI.Analysis.BishopCircleInvariance`
-- upgrades this to invariance of the integral under such shifts.  For a Haar
-- integral one needs invariance under *every* rational shift, positive or
-- larger than the period.  This module removes the bound on `t`:
--
--   * `per-nat`               -- a 1-periodic function is `k`-periodic;
--   * `node-multiple`         -- `node m (Q · (m+1)) = Q`;
--   * `node-split`            -- Euclidean splitting of a node;
--   * `integral-nodeShift`    -- invariance of the integral under the shift
--                                by `node p t` for *every* natural `t`.
--
-- Postulate-free, over the constructed Bishop reals.
------------------------------------------------------------------------

module DASHI.Analysis.BishopCircleNodeShift where

open import Data.Nat as ℕ using (ℕ; zero; suc)
import Data.Nat.Properties as ℕP
open import Data.Nat.DivMod as ℕD using (_/_; _%_; m≡m%n+[m/n]*n; m%n<n)
open import Data.Integer as ℤ using (ℤ; +_)
import Data.Integer.Properties as ℤP
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong; subst)

open import Real
open import RealProperties
open import Sequence
open import DASHI.Analysis.BishopFiniteSumLemmas
open import DASHI.Analysis.BishopRiemannIntegral
open import DASHI.Analysis.BishopIntegralComparison
open import DASHI.Analysis.BishopPeriodicShift
open import DASHI.Analysis.BishopCircleInvariance

------------------------------------------------------------------------
-- Whole multiples of the mesh are integers.

node-multiple : ∀ m Q → node m (Q ℕ.* suc m) ≃ natToℝ Q
node-multiple m Q = ≃-trans (⋆-cong (ℚ.*≡* step)) (≃-symm (natToℝ-⋆ Q))
  where
  step : + (Q ℕ.* suc m) ℤ.* + 1 ≡ + Q ℤ.* + (suc m)
  step = trans (ℤP.*-identityʳ (+ (Q ℕ.* suc m))) (ℤP.pos-* Q (suc m))

node-split : ∀ m r Q → node m (r ℕ.+ Q ℕ.* suc m) ≃ node m r + natToℝ Q
node-split m r Q = ≃-trans (≃-symm (node-add m r (Q ℕ.* suc m)))
  (+-congʳ (node m r) (node-multiple m Q))

------------------------------------------------------------------------
-- A 1-periodic function is periodic with every natural period.

module _ (f : ℝ → ℝ) (mc : UniformModulus f) (per : ∀ x → f (x + 1ℝ) ≃ f x) where

  per-nat : ∀ k x → f (x + natToℝ k) ≃ f x
  per-nat zero x = uc-cong f mc (x + 0ℝ) x (+-identityʳ x)
  per-nat (suc k) x = ≃-trans reassoc (≃-trans (per (x + natToℝ k)) (per-nat k x))
    where
    reassoc : f (x + (natToℝ k + 1ℝ)) ≃ f ((x + natToℝ k) + 1ℝ)
    reassoc = uc-cong f mc (x + (natToℝ k + 1ℝ)) ((x + natToℝ k) + 1ℝ)
      (≃-symm (+-assoc x (natToℝ k) 1ℝ))

------------------------------------------------------------------------
-- Reducing an arbitrary node shift modulo the period.

  private
    shiftedModulus : ∀ (a : ℝ) → UniformModulus (λ x → f (x + a))
    shiftedModulus a = shiftModulus f mc a

  nodeShift-reduce : ∀ p t →
    let r = t % suc p
        Q = t / suc p
    in ∀ x → f (x + node p t) ≃ f (x + node p r)
  nodeShift-reduce p t x = ≃-trans congStep (per-nat Q (x + node p r))
    where
    r = t % suc p
    Q = t / suc p

    idx : t ≡ r ℕ.+ Q ℕ.* suc p
    idx = m≡m%n+[m/n]*n t (suc p)

    nodeEq : node p t ≃ node p r + natToℝ Q
    nodeEq = subst (λ z → node p z ≃ node p r + natToℝ Q) (sym idx)
      (node-split p r Q)

    congStep : f (x + node p t) ≃ f ((x + node p r) + natToℝ Q)
    congStep = uc-cong f mc (x + node p t) ((x + node p r) + natToℝ Q)
      (≃-trans (+-congʳ x nodeEq) (≃-symm (+-assoc x (node p r) (natToℝ Q))))

------------------------------------------------------------------------
-- Invariance of the integral under an arbitrary rational shift.

  integral-nodeShift : ∀ p t →
    integral (λ x → f (x + node p t)) (shiftedModulus (node p t)) ≃ integral f mc
  integral-nodeShift p t = ≃-trans reduce
    (integral-rationalShift f mc per p r r≤p)
    where
    r = t % suc p
    Q = t / suc p

    r≤p : r ℕ.≤ suc p
    r≤p = ℕP.<⇒≤ (m%n<n t (suc p))

    reduce : integral (λ x → f (x + node p t)) (shiftedModulus (node p t))
               ≃ integral (λ x → f (x + node p r)) (shiftedModulus (node p r))
    reduce = integral-cong (λ x → f (x + node p t)) (λ x → f (x + node p r))
      (shiftedModulus (node p t)) (shiftedModulus (node p r))
      (nodeShift-reduce p t)
