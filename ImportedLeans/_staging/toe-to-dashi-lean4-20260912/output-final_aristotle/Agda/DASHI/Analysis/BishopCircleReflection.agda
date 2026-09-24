{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- Inversion invariance (unimodularity) of the constructed circle integral.
--
-- `DASHI.Analysis.BishopCircleHaar` proves that the integral of a
-- 1-periodic uniformly continuous function is invariant under every real
-- translation.  A Haar integral on a compact group satisfies one further
-- symmetry that translation invariance does not give: invariance under the
-- group inversion,
--
--     ∫ f (x⁻¹) dx  =  ∫ f (x) dx,
--
-- which on the circle written additively is `∫ f (- x) = ∫ f x`.  This is
-- the statement that the measure is *unimodular*, and it is the second
-- non-translational change of variables available for the constructed
-- integral (the first being the shears of
-- `DASHI.Analysis.BishopTorusShear`).
--
-- The proof is finite combinatorics on the partition: the reflected nodes
-- are, modulo the period, the original nodes traversed backwards, so the
-- two Riemann sums agree exactly at every stage, and the two integrals are
-- then squeezed together by the explicit rate of
-- `DASHI.Analysis.BishopIntegralRate`.
--
-- Postulate-free, over the constructed Bishop reals.
------------------------------------------------------------------------

module DASHI.Analysis.BishopCircleReflection where

open import Data.Nat as ℕ using (ℕ; zero; suc; _∸_; s≤s; z≤n)
import Data.Nat.Properties as ℕP
open import Data.Integer as ℤ using (ℤ; +_)
open import Data.Integer.Solver as ℤSolver
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong; subst)

open import Real
open import RealProperties
open import ExtraProperties
open import Sequence
open import DASHI.Analysis.BishopFiniteSumLemmas
open import DASHI.Analysis.BishopRiemannIntegral
open import DASHI.Analysis.BishopPeriodicShift using (uc-cong; node-add; node-period)
open import DASHI.Analysis.BishopIntegralRate

------------------------------------------------------------------------
-- Finite sums: bounded congruence and reversal of the summation order.

∑₀-cong< : ∀ (u v : ℕ → ℝ) n → (∀ i → i ℕ.< n → u i ≃ v i) →
  ∑₀ u n ≃ ∑₀ v n
∑₀-cong< u v zero    h = ≃-refl
∑₀-cong< u v (suc n) h =
  +-cong (∑₀-cong< u v n (λ i i<n → h i (ℕP.≤-trans i<n (ℕP.n≤1+n n))))
         (h n ℕP.≤-refl)

minus-suc : ∀ n i → i ℕ.< n → n ∸ i ≡ suc (n ∸ suc i)
minus-suc (suc n) zero    _         = refl
minus-suc (suc n) (suc i) (s≤s i<n) = minus-suc n i i<n

∑₀-rev : ∀ (u : ℕ → ℝ) n → ∑₀ (λ i → u (n ∸ suc i)) n ≃ ∑₀ u n
∑₀-rev u zero    = ≃-refl
∑₀-rev u (suc n) = ≃-trans (+-cong inner last) (≃-symm split)
  where
  u′ : ℕ → ℝ
  u′ k = u (suc k)

  reindex : ∀ i → i ℕ.< n → u (n ∸ i) ≃ u′ (n ∸ suc i)
  reindex i i<n = subst (λ k → u (n ∸ i) ≃ u k) (minus-suc n i i<n) ≃-refl

  inner : ∑₀ (λ i → u (n ∸ i)) n ≃ ∑₀ u′ n
  inner = ≃-trans (∑₀-cong< (λ i → u (n ∸ i)) (λ i → u′ (n ∸ suc i)) n reindex)
                  (∑₀-rev u′ n)

  last : u (n ∸ n) ≃ u 0
  last = subst (λ k → u k ≃ u 0) (sym (ℕP.n∸n≡0 n)) ≃-refl

  split : ∑₀ u (suc n) ≃ ∑₀ u′ n + u 0
  split = ≃-trans (∑₀-shift-split u 1 n)
          (≃-trans (+-congˡ (∑₀ u′ n) (+-identityˡ (u 0)))
                   (+-comm (u 0) (∑₀ u′ n)))

------------------------------------------------------------------------
-- Nodes: the complementary node.

node-zero : ∀ m → node m 0 ≃ 0ℝ
node-zero m = ⋆-cong (ℚ.*≡* refl)

node-one : ∀ m → node m (suc m) ≃ 1ℝ
node-one m = ≃-trans nodeEnd
             (≃-trans (+-congˡ 1ℝ (node-zero m)) (+-identityˡ 1ℝ))
  where
  nodeEnd : node m (suc m) ≃ node m 0 + 1ℝ
  nodeEnd = subst (λ k → node m k ≃ node m 0 + 1ℝ) (ℕP.+-identityʳ (suc m))
                (node-period m 0)

node-complement : ∀ m i → i ℕ.≤ suc m → node m (suc m ∸ i) ≃ 1ℝ - node m i
node-complement m i i≤ = ≃-trans rearrange (+-congˡ (- node m i) whole)
  where
  open ℝ-Solver

  whole : node m i + node m (suc m ∸ i) ≃ 1ℝ
  whole = ≃-trans (≃-trans (node-add m i (suc m ∸ i))
                    (subst (λ k → node m k ≃ node m (suc m))
                           (sym (ℕP.m+[n∸m]≡n i≤)) ≃-refl))
                  (node-one m)

  rearrange : node m (suc m ∸ i)
                ≃ (node m i + node m (suc m ∸ i)) - node m i
  rearrange = ℝ-Solver.solve 2 (λ a b → b ⊜ (a ⊕ b) ⊖ a) ≃-refl
                (node m i) (node m (suc m ∸ i))

------------------------------------------------------------------------
-- Two auxiliary rational estimates.

private
  dbl : ℕ → ℕ
  dbl j = ℕ.pred (2 ℕ.* suc j)

  halves₂ : ∀ j →
    (+ 1 ℚ./ (2 ℕ.* suc j)) ⋆ + (+ 1 ℚ./ (2 ℕ.* suc j)) ⋆ ≤ (+ 1 ℚ./ suc j) ⋆
  halves₂ j = ≤-reflexive (≃-trans
    (≃-symm (⋆-distrib-+ (+ 1 ℚ./ (2 ℕ.* suc j)) (+ 1 ℚ./ (2 ℕ.* suc j))))
    (⋆-cong (ℚ.*≡* (solve 1 (λ z →
      (con (+ 1) :* (con (+ 2) :* z) :+ con (+ 1) :* (con (+ 2) :* z)) :* z
        := con (+ 1) :* (con (+ 2) :* z :* (con (+ 2) :* z)))
      refl (+ suc j)))))
    where open ℤSolver.+-*-Solver

------------------------------------------------------------------------
-- Reflection of a periodic uniformly continuous function.

reflectModulus : ∀ (f : ℝ → ℝ) → UniformModulus f → UniformModulus (λ x → f (- x))
reflectModulus f mc = record
  { δ      = UniformModulus.δ mc
  ; δ-cont = λ j x y hyp →
      UniformModulus.δ-cont mc j (- x) (- y) (≤-respˡ-≃ (negDist x y) hyp)
  }
  where
  negDist : ∀ x y → ∣ x - y ∣ ≃ ∣ (- x) - (- y) ∣
  negDist x y = ≃-symm (≃-trans (∣-∣-cong flip) ∣-x∣≃∣x∣)
    where
    open ℝ-Solver

    flip : (- x) - (- y) ≃ - (x - y)
    flip = ℝ-Solver.solve 2 (λ a b → (⊝ a) ⊖ (⊝ b) ⊜ ⊝ (a ⊖ b)) ≃-refl x y

module _ (f : ℝ → ℝ) (mc : UniformModulus f) (per : ∀ x → f (x + 1ℝ) ≃ f x) where

  private
    g : ℝ → ℝ
    g x = f (- x)

    mg : UniformModulus g
    mg = reflectModulus f mc

    -- the reflected node is, modulo the period, the complementary node
    reflectNode : ∀ m i → i ℕ.≤ suc m → f (- node m i) ≃ f (node m (suc m ∸ i))
    reflectNode m i i≤ = ≃-symm (≃-trans
      (uc-cong f mc (node m (suc m ∸ i)) ((- node m i) + 1ℝ) shape)
      (per (- node m i)))
      where
      open ℝ-Solver

      shape : node m (suc m ∸ i) ≃ (- node m i) + 1ℝ
      shape = ≃-trans (node-complement m i i≤)
        (ℝ-Solver.solve 2 (λ a b → a ⊖ b ⊜ (⊝ b) ⊕ a) ≃-refl 1ℝ (node m i))

    -- the wrapped endpoint contributes the same value as the origin
    endpoint : ∀ m → f (node m (suc m)) ≃ f (node m 0)
    endpoint m = ≃-trans
      (uc-cong f mc (node m (suc m)) (node m 0 + 1ℝ)
        (subst (λ k → node m k ≃ node m 0 + 1ℝ) (ℕP.+-identityʳ (suc m))
               (node-period m 0)))
      (per (node m 0))

    sumReflect : ∀ m → ∑₀ (λ i → f (- node m i)) (suc m)
                         ≃ ∑₀ (λ i → f (node m i)) (suc m)
    sumReflect m = ≃-trans stepA (≃-trans stepB (≃-symm stepE))
      where
      u : ℕ → ℝ
      u k = f (node m k)

      u′ : ℕ → ℝ
      u′ k = u (suc k)

      v : ℕ → ℝ
      v i = u (suc m ∸ i)

      stepA : ∑₀ (λ i → f (- node m i)) (suc m) ≃ ∑₀ v (suc m)
      stepA = ∑₀-cong< (λ i → f (- node m i)) v (suc m)
        (λ i i<n → reflectNode m i (ℕP.≤-trans (ℕP.n≤1+n i) i<n))

      stepC : ∑₀ (λ k → u (m ∸ k)) m ≃ ∑₀ u′ m
      stepC = ≃-trans
        (∑₀-cong< (λ k → u (m ∸ k)) (λ k → u′ (m ∸ suc k)) m
          (λ k k<m → subst (λ z → u (m ∸ k) ≃ u z) (minus-suc m k k<m) ≃-refl))
        (∑₀-rev u′ m)

      stepB : ∑₀ v (suc m) ≃ ∑₀ u 1 + ∑₀ u′ m
      stepB = ≃-trans (∑₀-shift-split v 1 m)
        (+-cong (+-congʳ 0ℝ (endpoint m)) stepC)

      stepE : ∑₀ u (suc m) ≃ ∑₀ u 1 + ∑₀ u′ m
      stepE = ∑₀-shift-split u 1 m

    riemannSum-reflect : ∀ m → riemannSum g m ≃ riemannSum f m
    riemannSum-reflect m = *-congˡ (sumReflect m)

  integral-reflect : integral (λ x → f (- x)) (reflectModulus f mc)
                       ≃ integral f mc
  integral-reflect = ∣x-y∣≤k⁻¹⇒x≃y (integral g mg) (integral f mc) main
    where
    main : ∀ (k : ℕ) → .{{_ : ℕ.NonZero k}} →
      ∣ integral g mg - integral f mc ∣ ≤ (+ 1 ℚ./ k) ⋆
    main (suc k₀) = ≤-trans (≤-reflexive (∣-∣-cong split))
      (≤-trans (∣x+y∣≤∣x∣+∣y∣ (integral g mg - S) (S - integral f mc))
      (≤-trans (+-mono-≤ boundG boundF) (halves₂ k₀)))
      where
      open ℝ-Solver

      m : ℕ
      m = UniformModulus.δ mc (dbl k₀)

      S : ℝ
      S = riemannSum g m

      split : integral g mg - integral f mc
                ≃ (integral g mg - S) + (S - integral f mc)
      split = ℝ-Solver.solve 3 (λ a b c → a ⊖ b ⊜ (a ⊖ c) ⊕ (c ⊖ b))
        ≃-refl (integral g mg) (integral f mc) S

      boundG : ∣ integral g mg - S ∣ ≤ (+ 1 ℚ./ (2 ℕ.* suc k₀)) ⋆
      boundG = integral-riemannSum-bound g mg (dbl k₀) m ℕP.≤-refl

      boundF : ∣ S - integral f mc ∣ ≤ (+ 1 ℚ./ (2 ℕ.* suc k₀)) ⋆
      boundF = ≤-respˡ-≃
        (≃-trans (∣x-y∣≃∣y-x∣ (integral f mc) (riemannSum f m))
                 (∣-∣-cong (+-congˡ (- integral f mc)
                             (≃-symm (riemannSum-reflect m)))))
        (integral-riemannSum-bound f mc (dbl k₀) m ℕP.≤-refl)
