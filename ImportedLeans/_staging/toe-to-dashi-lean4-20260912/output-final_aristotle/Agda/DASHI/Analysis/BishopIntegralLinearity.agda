{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- Scalar homogeneity of the constructive Riemann integral.
--
-- Together with `integral-add` (`DASHI.Analysis.BishopRiemannIntegralAdditivity`)
-- this makes the integral a genuine linear functional, which is what a Haar
-- specification demands.  The only real content is the modulus of uniform
-- continuity of `c · f`: it needs a bound on `∣c∣`, supplied by the canonical
-- bound `K` of the Bishop reals.
--
-- Postulate-free, over the constructed Bishop reals.
------------------------------------------------------------------------

module DASHI.Analysis.BishopIntegralLinearity where

open import Data.Nat as ℕ using (ℕ; zero; suc)
import Data.Nat.Properties as ℕP
open import Data.Integer as ℤ using (ℤ; +_)
import Data.Integer.Properties as ℤP
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong)

open import Real
open import RealProperties
open import Sequence
open import DASHI.Analysis.BishopFiniteSumLemmas
open import DASHI.Analysis.BishopRiemannIntegral
open import DASHI.Analysis.BishopIntegralComparison

------------------------------------------------------------------------
-- A modulus for a scalar multiple.

scaleModulusAux : ∀ (c : ℝ) (f : ℝ → ℝ) → UniformModulus f →
  (N-1 : ℕ) → ∣ c ∣ ≤ (+ suc N-1 ℚ./ 1) ⋆ →
  UniformModulus (λ x → c * f x)
scaleModulusAux c f mf N-1 cBound = record
  { δ      = λ j → δ (j ℕ.+ N-1 ℕ.* suc j)
  ; δ-cont = cont
  }
  where
  open UniformModulus mf

  ratEq : ∀ j →
    (+ suc N-1 ℚ./ 1) ℚ.* (+ 1 ℚ./ suc (j ℕ.+ N-1 ℕ.* suc j))
      ℚ.≃ (+ 1 ℚ./ suc j)
  ratEq j = ℚ.*≡* step
    where
    step : (+ suc N-1 ℤ.* + 1) ℤ.* + suc j
             ≡ + 1 ℤ.* + (1 ℕ.* suc (j ℕ.+ N-1 ℕ.* suc j))
    step = trans (cong (ℤ._* + suc j) (ℤP.*-identityʳ (+ suc N-1)))
           (trans (sym (ℤP.pos-* (suc N-1) (suc j)))
                  (sym (trans (ℤP.*-identityˡ (+ (1 ℕ.* suc (j ℕ.+ N-1 ℕ.* suc j))))
                              (cong +_ (ℕP.*-identityˡ (suc (j ℕ.+ N-1 ℕ.* suc j)))))))

  cont : ∀ (j : ℕ) (x y : ℝ) →
    ∣ x - y ∣ ≤ (+ 1 ℚ./ suc (δ (j ℕ.+ N-1 ℕ.* suc j))) ⋆ →
    ∣ c * f x - c * f y ∣ ≤ (+ 1 ℚ./ suc j) ⋆
  cont j x y hyp = ≤-respˡ-≃ (≃-symm split) (≤-respʳ-≃ collapse bound)
    where
    open ℝ-Solver

    j′ : ℕ
    j′ = j ℕ.+ N-1 ℕ.* suc j

    split : ∣ c * f x - c * f y ∣ ≃ ∣ c ∣ * ∣ f x - f y ∣
    split = ≃-trans
      (∣-∣-cong (ℝ-Solver.solve 3 (λ u v w → u ⊗ v ⊖ u ⊗ w ⊜ u ⊗ (v ⊖ w))
        ≃-refl c (f x) (f y)))
      (∣x*y∣≃∣x∣*∣y∣ c (f x - f y))

    bound : ∣ c ∣ * ∣ f x - f y ∣
              ≤ (+ suc N-1 ℚ./ 1) ⋆ * (+ 1 ℚ./ suc j′) ⋆
    bound = *-mono-≤ (nonNeg∣x∣ c) (nonNeg∣x∣ (f x - f y)) cBound
      (δ-cont j′ x y hyp)

    collapse : (+ suc N-1 ℚ./ 1) ⋆ * (+ 1 ℚ./ suc j′) ⋆ ≃ (+ 1 ℚ./ suc j) ⋆
    collapse = ≃-trans (≃-symm (⋆-distrib-* (+ suc N-1 ℚ./ 1) (+ 1 ℚ./ suc j′)))
      (⋆-cong (ratEq j))

scaleModulus : ∀ (c : ℝ) (f : ℝ → ℝ) → UniformModulus f →
  UniformModulus (λ x → c * f x)
scaleModulus c f mf =
  scaleModulusAux c f mf (ℕ.pred (K ∣ c ∣)) (x≤Kx ∣ c ∣)

------------------------------------------------------------------------
-- Homogeneity.

riemannSum-scale : ∀ (c : ℝ) (f : ℝ → ℝ) m →
  riemannSum (λ x → c * f x) m ≃ c * riemannSum f m
riemannSum-scale c f m = ≃-trans
  (*-congˡ (∑₀-scale c (λ i → f (node m i)) (suc m)))
  (ℝ-Solver.solve 3 (λ u v w → u ⊗ (v ⊗ w) ⊜ v ⊗ (u ⊗ w)) ≃-refl
    ((width m) ⋆) c (∑₀ (λ i → f (node m i)) (suc m)))
  where open ℝ-Solver

integral-scale : ∀ (c : ℝ) (f : ℝ → ℝ) (mf : UniformModulus f)
  (mcf : UniformModulus (λ x → c * f x)) →
  integral (λ x → c * f x) mcf ≃ c * integral f mf
integral-scale c f mf mcf = uniqueness-of-limits
  (riemannSum-converges (λ x → c * f x) mcf)
  (xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀ (λ k → ≃-symm (riemannSum-scale c f k)) scaled)
  where
  scaled : (λ k → c * riemannSum f k) isConvergent
  scaled = c * integral f mf ,
    xₙyₙ→x₀y₀ (c , xₙ≃c⇒xₙ→c (λ _ → ≃-refl))
              (integral f mf , riemannSum-converges f mf)

------------------------------------------------------------------------
-- Consequences: negation and differences.

integral-neg : ∀ (f : ℝ → ℝ) (mf : UniformModulus f)
  (mnf : UniformModulus (λ x → (- 1ℝ) * f x)) →
  integral (λ x → (- 1ℝ) * f x) mnf ≃ - integral f mf
integral-neg f mf mnf = ≃-trans (integral-scale (- 1ℝ) f mf mnf) minusOne
  where
  minusOne : (- 1ℝ) * integral f mf ≃ - integral f mf
  minusOne = ≃-trans (≃-symm (neg-distribˡ-* 1ℝ (integral f mf)))
    (-‿cong (*-identityˡ (integral f mf)))
