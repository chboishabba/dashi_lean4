{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- A quantitative rate for the constructive Riemann integral.
--
-- `riemannSum-converges` says that the uniform Riemann sums converge to the
-- integral, but with an unspecified rate.  For every later analytic use --
-- iterated integration and Fubini-type interchange in particular -- one needs
-- the *explicit* rate that the modulus of uniform continuity already
-- provides: once the partition is finer than the modulus, the Riemann sum is
-- within the corresponding tolerance of the integral, uniformly.
--
--    δ j ≤ m  ⟹  ∣ ∫f − riemannSum f m ∣ ≤ 1/(j+1).
--
-- Postulate-free, over the constructed Bishop reals.
------------------------------------------------------------------------

module DASHI.Analysis.BishopIntegralRate where

open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Integer as ℤ using (ℤ; +_)
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ)
open import Data.Product using (_,_; proj₁; proj₂)

open import Real
open import RealProperties
open import Sequence
open import DASHI.Analysis.BishopFiniteSumLemmas
open import DASHI.Analysis.BishopRiemannIntegral
open import DASHI.Analysis.BishopIntegralComparison
open import DASHI.Analysis.BishopCircleInvariance using (refine-mono)

module _ (f : ℝ → ℝ) (mf : UniformModulus f) (j m : ℕ)
         (fine : UniformModulus.δ mf j ℕ.≤ m) where

  private
    ε : ℝ
    ε = (+ 1 ℚ./ suc j) ⋆

    R : ℝ
    R = riemannSum f m

    approx : ℕ → ℝ
    approx q = riemannSum f (refine m q)

    approx→ : approx ConvergesTo integral f mf
    approx→ = xₙ⊆yₙ∧yₙ→y⇒xₙ→y
      (subseq* (refine m , (λ q → ≃-refl) , refine-mono m))
      (riemannSum-isConvergent f mf)

    diff : ℕ → ℝ
    diff q = approx q - R

    diff→ : diff ConvergesTo (integral f mf - R)
    diff→ = xₙ+yₙ→x₀+y₀ (integral f mf , approx→)
      (- R , xₙ≃c⇒xₙ→c (λ _ → ≃-refl))

    negdiff→ : (λ q → - diff q) ConvergesTo (- (integral f mf - R))
    negdiff→ = -xₙ→-x₀ (integral f mf - R , diff→)

    ε→ : (λ (_ : ℕ) → ε) ConvergesTo ε
    ε→ = xₙ≃c⇒xₙ→c (λ _ → ≃-refl)

    stepBound : ∀ q → ∣ diff q ∣ ≤ ε
    stepBound q = refinement-bound f mf j m q fine

    upper : integral f mf - R ≤ ε
    upper = xₙ≤yₙ⇒x₀≤y₀ diff→ ε→ (λ q → ≤-trans x≤∣x∣ (stepBound q))

    lower : - (integral f mf - R) ≤ ε
    lower = xₙ≤yₙ⇒x₀≤y₀ negdiff→ ε→
      (λ q → ≤-trans (≤-respʳ-≃ (≃-symm (∣x∣≃x⊔-x (diff q)))
                                (x≤y⊔x (- diff q) (diff q)))
                     (stepBound q))

  integral-riemannSum-bound : ∣ integral f mf - riemannSum f m ∣ ≤ (+ 1 ℚ./ suc j) ⋆
  integral-riemannSum-bound = ≤-respˡ-≃
    (≃-symm (∣x∣≃x⊔-x (integral f mf - R)))
    (x≤z∧y≤z⇒x⊔y≤z upper lower)
