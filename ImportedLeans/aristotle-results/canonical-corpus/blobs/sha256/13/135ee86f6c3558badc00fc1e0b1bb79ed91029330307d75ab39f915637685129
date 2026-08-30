{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- Translation behaviour of the constructive Riemann sums.
--
-- Invariance of an integral under translation is the property that turns a
-- normalised positive functional into a *Haar* integral; it is exactly the
-- property that the Yang-Mills lane of this repository postulates rather than
-- proves (see `docs/ym/YangMillsClayObstructionReport.md`).
--
-- This module proves the combinatorial core of translation invariance on the
-- circle: for a 1-periodic uniformly continuous function, the uniform Riemann
-- sum on [0,1] is *exactly* invariant under a shift by any multiple of the
-- mesh of the partition.
--
-- Postulate-free, over the vendored Bishop constructive reals.
------------------------------------------------------------------------

module DASHI.Analysis.BishopPeriodicShift where

open import Data.Nat as ℕ using (ℕ; zero; suc)
import Data.Nat.Properties as ℕP
open import Data.Integer as ℤ using (ℤ; +_)
import Data.Integer.Properties as ℤP
open import Data.Integer.Solver as ℤSolver
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; 0ℚᵘ; 1ℚᵘ)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Real
open import RealProperties
open import Sequence
open import DASHI.Analysis.BishopFiniteSumLemmas
open import DASHI.Analysis.BishopRiemannIntegral

private
  open ℤSolver.+-*-Solver

  posMul : ∀ m n → + (m ℕ.* n) ≡ + m ℤ.* + n
  posMul m n = ℤP.pos-* m n

  addℤ : ∀ (I T N : ℤ) →
    (I ℤ.+ T) ℤ.* (N ℤ.* N) ≡ (I ℤ.* N ℤ.+ T ℤ.* N) ℤ.* N
  addℤ = solve 3 (λ I T N → (I :+ T) :* (N :* N) := (I :* N :+ T :* N) :* N) refl

  perℤ : ∀ (I N : ℤ) →
    (N ℤ.+ I) ℤ.* (N ℤ.* + 1) ≡ (I ℤ.* + 1 ℤ.+ + 1 ℤ.* N) ℤ.* N
  perℤ = solve 2
    (λ I N → (N :+ I) :* (N :* con (+ 1))
               := (I :* con (+ 1) :+ con (+ 1) :* N) :* N) refl

------------------------------------------------------------------------
-- Nodes add, and are 1-periodic.

node-add : ∀ m i t → node m i + node m t ≃ node m (i ℕ.+ t)
node-add m i t = ≃-symm
  (≃-trans (⋆-cong (ℚ.*≡* step))
           (⋆-distrib-+ (+ i ℚ./ suc m) (+ t ℚ./ suc m)))
  where
  n = suc m

  step : + (i ℕ.+ t) ℤ.* + (n ℕ.* n)
           ≡ (+ i ℤ.* + n ℤ.+ + t ℤ.* + n) ℤ.* + n
  step = trans (cong₂ (λ z w → z ℤ.* w) (ℤP.pos-+ i t) (posMul n n))
               (addℤ (+ i) (+ t) (+ n))

node-period : ∀ m i → node m (suc m ℕ.+ i) ≃ node m i + 1ℝ
node-period m i =
  ≃-trans (⋆-cong (ℚ.*≡* step))
          (⋆-distrib-+ (+ i ℚ./ suc m) 1ℚᵘ)
  where
  n = suc m

  step : + (n ℕ.+ i) ℤ.* + (n ℕ.* 1)
           ≡ (+ i ℤ.* + 1 ℤ.+ + 1 ℤ.* + n) ℤ.* + n
  step = trans (cong₂ (λ z w → z ℤ.* w) (ℤP.pos-+ n i) (posMul n 1))
               (perℤ (+ i) (+ n))

------------------------------------------------------------------------
-- A uniformly continuous function respects equality of reals.

module _ (f : ℝ → ℝ) (mc : UniformModulus f) where
  open UniformModulus mc

  uc-cong : ∀ x y → x ≃ y → f x ≃ f y
  uc-cong x y x≃y = ∣x-y∣≤k⁻¹⇒x≃y (f x) (f y) bound
    where
    zero-dist : ∀ (d : ℕ) → ∣ x - y ∣ ≤ (+ 1 ℚ./ suc d) ⋆
    zero-dist d = ≤-respˡ-≃
      (≃-symm (≃-trans (∣-∣-cong (≃-trans (+-congˡ (- y) x≃y) (+-inverseʳ y)))
                       (nonNegx⇒∣x∣≃x nonNeg0)))
      (0≤width d)

    bound : ∀ (k : ℕ) → .{{_ : ℕ.NonZero k}} → ∣ f x - f y ∣ ≤ (+ 1 ℚ./ k) ⋆
    bound (suc k-1) = δ-cont k-1 x y (zero-dist (δ k-1))

------------------------------------------------------------------------
-- Exact invariance of the Riemann sum under a shift by a multiple of the
-- mesh, for a 1-periodic function.

module _ (f : ℝ → ℝ) (mc : UniformModulus f)
         (per : ∀ x → f (x + 1ℝ) ≃ f x) where

  private
    F : ℕ → ℕ → ℝ
    F m i = f (node m i)

    F-period : ∀ m i → F m (suc m ℕ.+ i) ≃ F m i
    F-period m i =
      ≃-trans (uc-cong f mc (node m (suc m ℕ.+ i)) (node m i + 1ℝ)
                 (node-period m i))
              (per (node m i))

  periodicShiftSum : ∀ m t → t ℕ.≤ suc m →
    ∑₀ (λ i → F m (i ℕ.+ t)) (suc m) ≃ ∑₀ (F m) (suc m)
  periodicShiftSum m t t≤n = ≃-trans left (≃-symm right)
    where
    n = suc m
    u = n ℕ.∸ t

    u+t : u ℕ.+ t ≡ n
    u+t = ℕP.m∸n+n≡m t≤n

    t+u : t ℕ.+ u ≡ n
    t+u = trans (ℕP.+-comm t u) u+t

    -- the shifted sum, split at u
    splitL : ∑₀ (λ i → F m (i ℕ.+ t)) n
               ≃ ∑₀ (λ i → F m (i ℕ.+ t)) u
                 + ∑₀ (λ i → F m ((u ℕ.+ i) ℕ.+ t)) t
    splitL = subst (λ z → ∑₀ (λ i → F m (i ℕ.+ t)) z
                            ≃ ∑₀ (λ i → F m (i ℕ.+ t)) u
                              + ∑₀ (λ i → F m ((u ℕ.+ i) ℕ.+ t)) t)
                   u+t
                   (∑₀-shift-split (λ i → F m (i ℕ.+ t)) u t)

    wrap : ∀ i → F m ((u ℕ.+ i) ℕ.+ t) ≃ F m i
    wrap i = subst (λ z → F m z ≃ F m i) (sym idx) (F-period m i)
      where
      idx : (u ℕ.+ i) ℕ.+ t ≡ n ℕ.+ i
      idx = trans (ℕP.+-assoc u i t)
            (trans (cong (u ℕ.+_) (ℕP.+-comm i t))
            (trans (sym (ℕP.+-assoc u t i)) (cong (ℕ._+ i) u+t)))

    left : ∑₀ (λ i → F m (i ℕ.+ t)) n
             ≃ ∑₀ (λ i → F m (i ℕ.+ t)) u + ∑₀ (F m) t
    left = ≃-trans splitL
      (+-congʳ (∑₀ (λ i → F m (i ℕ.+ t)) u)
        (∑₀-congruent wrap t))

    splitR : ∑₀ (F m) n ≃ ∑₀ (F m) t + ∑₀ (λ i → F m (t ℕ.+ i)) u
    splitR = subst (λ z → ∑₀ (F m) z
                            ≃ ∑₀ (F m) t + ∑₀ (λ i → F m (t ℕ.+ i)) u)
                   t+u
                   (∑₀-shift-split (F m) t u)

    right : ∑₀ (F m) n ≃ ∑₀ (λ i → F m (i ℕ.+ t)) u + ∑₀ (F m) t
    right = ≃-trans splitR
      (≃-trans (+-congʳ (∑₀ (F m) t)
                 (∑₀-congruent
                   (λ i → ≃-reflexive₂ (cong (λ z → F m z) (ℕP.+-comm t i)))
                   u))
               (+-comm (∑₀ (F m) t) (∑₀ (λ i → F m (i ℕ.+ t)) u)))
      where
      ≃-reflexive₂ : ∀ {x y : ℝ} → x ≡ y → x ≃ y
      ≃-reflexive₂ refl = ≃-refl

  riemannSum-shift : ∀ m t → t ℕ.≤ suc m →
    riemannSum (λ x → f (x + node m t)) m ≃ riemannSum f m
  riemannSum-shift m t t≤n = *-congˡ
    (≃-trans
      (∑₀-congruent
        (λ i → uc-cong f mc (node m i + node m t) (node m (i ℕ.+ t))
                 (node-add m i t))
        (suc m))
      (periodicShiftSum m t t≤n))
