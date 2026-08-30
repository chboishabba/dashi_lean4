{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- Order and comparison properties of the constructive Riemann integral.
--
-- `DASHI.Analysis.BishopRiemannIntegral` constructs the integral on [0,1]
-- over the vendored Bishop reals and proves the normalisation ∫1 = 1;
-- `DASHI.Analysis.BishopRiemannIntegralAdditivity` proves additivity.  The
-- Yang-Mills lane needs, on top of that, the *order* half of the Haar
-- specification and the analytic comparison estimate that lets one pass from
-- a uniform pointwise bound between two integrands to a bound between their
-- integrals; that estimate is what upgrades invariance under a dense set of
-- translations to invariance under every translation.
--
-- Proved here:
--   * `integral-cong`   -- pointwise equal integrands have equal integrals;
--   * `integral-mono`   -- monotonicity;
--   * `integral-nonNeg` -- positivity of the functional;
--   * `riemannSum-close`, `integral-close` -- the comparison estimate
--       (∀ x → ∣ f x - g x ∣ ≤ ε)  ⟹  ∣ ∫f - ∫g ∣ ≤ ε.
--
-- Postulate-free, over the constructed (not postulated) Bishop reals.
------------------------------------------------------------------------

module DASHI.Analysis.BishopIntegralComparison where

open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Integer as ℤ using (ℤ; +_)
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ)
open import Data.Product using (_,_; proj₁; proj₂)

open import Real
open import RealProperties
open import Sequence
open import DASHI.Analysis.BishopFiniteSumLemmas
open import DASHI.Analysis.BishopRiemannIntegral

------------------------------------------------------------------------
-- Pointwise congruence.

riemannSum-cong : ∀ (f g : ℝ → ℝ) → (∀ x → f x ≃ g x) →
  ∀ m → riemannSum f m ≃ riemannSum g m
riemannSum-cong f g f≃g m =
  *-congˡ (∑₀-congruent (λ i → f≃g (node m i)) (suc m))

integral-cong : ∀ (f g : ℝ → ℝ) (mf : UniformModulus f) (mg : UniformModulus g) →
  (∀ x → f x ≃ g x) → integral f mf ≃ integral g mg
integral-cong f g mf mg f≃g = uniqueness-of-limits
  (xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀ (λ n → riemannSum-cong f g f≃g n)
    (riemannSum-isConvergent f mf))
  (riemannSum-converges g mg)

------------------------------------------------------------------------
-- Monotonicity and positivity.

riemannSum-mono : ∀ (f g : ℝ → ℝ) → (∀ x → f x ≤ g x) →
  ∀ m → riemannSum f m ≤ riemannSum g m
riemannSum-mono f g f≤g m =
  *-monoˡ-≤-nonNeg (∑₀-mono-≤ (λ i → f≤g (node m i)) (suc m))
    (0≤x⇒nonNegx (0≤width m))

integral-mono : ∀ (f g : ℝ → ℝ) (mf : UniformModulus f) (mg : UniformModulus g) →
  (∀ x → f x ≤ g x) → integral f mf ≤ integral g mg
integral-mono f g mf mg f≤g = xₙ≤yₙ⇒x₀≤y₀
  (riemannSum-converges f mf) (riemannSum-converges g mg)
  (λ n → riemannSum-mono f g f≤g n)

integral-nonNeg : ∀ (f : ℝ → ℝ) (mf : UniformModulus f) →
  (∀ x → 0ℝ ≤ f x) → 0ℝ ≤ integral f mf
integral-nonNeg f mf 0≤f = ≤-respˡ-≃ (integral-const 0ℝ)
  (integral-mono (λ _ → 0ℝ) f (constModulus 0ℝ) mf 0≤f)

------------------------------------------------------------------------
-- The comparison estimate.

riemannSum-close : ∀ (f g : ℝ → ℝ) (ε : ℝ) → (∀ x → ∣ f x - g x ∣ ≤ ε) →
  ∀ m → ∣ riemannSum f m - riemannSum g m ∣ ≤ ε
riemannSum-close f g ε bound m =
  ≤-respˡ-≃ (∣-∣-cong (≃-symm main-eq)) (≤-respˡ-≃ (≃-symm absEq) final)
  where
  open ℝ-Solver

  n : ℕ
  n = suc m

  w : ℝ
  w = (width m) ⋆

  S : ℝ
  S = ∑₀ (λ i → f (node m i) - g (node m i)) n

  main-eq : riemannSum f m - riemannSum g m ≃ w * S
  main-eq = ≃-symm (≃-trans
    (*-congˡ (∑₀-sub (λ i → f (node m i)) (λ i → g (node m i)) n))
    (ℝ-Solver.solve 3 (λ a b c → a ⊗ (b ⊖ c) ⊜ a ⊗ b ⊖ a ⊗ c) ≃-refl
      w (∑₀ (λ i → f (node m i)) n) (∑₀ (λ i → g (node m i)) n)))

  absEq : ∣ w * S ∣ ≃ w * ∣ S ∣
  absEq = ≃-trans (∣x*y∣≃∣x∣*∣y∣ w S)
    (*-congʳ (nonNegx⇒∣x∣≃x (0≤x⇒nonNegx (0≤width m))))

  Sbound : ∣ S ∣ ≤ natToℝ n * ε
  Sbound = ≤-trans (∑₀-abs (λ i → f (node m i) - g (node m i)) n)
    (∑₀-const-bound (λ i → ∣ f (node m i) - g (node m i) ∣) ε
      (λ i → bound (node m i)) n)

  collapse : w * (natToℝ n * ε) ≃ ε
  collapse = ≃-trans (≃-symm (*-assoc w (natToℝ n) ε))
    (≃-trans (*-congʳ (width-unit m)) (*-identityˡ ε))

  final : w * ∣ S ∣ ≤ ε
  final = ≤-respʳ-≃ collapse
    (*-monoˡ-≤-nonNeg Sbound (0≤x⇒nonNegx (0≤width m)))

------------------------------------------------------------------------
-- ... and the same estimate for the integrals, by passing to the limit.

module _ (f g : ℝ → ℝ) (mf : UniformModulus f) (mg : UniformModulus g)
         (ε : ℝ) (bound : ∀ x → ∣ f x - g x ∣ ≤ ε) where

  private
    A B : ℝ
    A = integral f mf
    B = integral g mg

    diff : ℕ → ℝ
    diff k = riemannSum f k - riemannSum g k

    diff→ : diff ConvergesTo (A - B)
    diff→ = xₙ+yₙ→x₀+y₀ (A , riemannSum-converges f mf)
      (- B , -xₙ→-x₀ (B , riemannSum-converges g mg))

    negdiff→ : (λ k → - diff k) ConvergesTo (- (A - B))
    negdiff→ = -xₙ→-x₀ (A - B , diff→)

    ε→ : (λ (_ : ℕ) → ε) ConvergesTo ε
    ε→ = xₙ≃c⇒xₙ→c (λ _ → ≃-refl)

    upper : A - B ≤ ε
    upper = xₙ≤yₙ⇒x₀≤y₀ diff→ ε→
      (λ k → ≤-trans x≤∣x∣ (riemannSum-close f g ε bound k))

    lower : - (A - B) ≤ ε
    lower = xₙ≤yₙ⇒x₀≤y₀ negdiff→ ε→
      (λ k → ≤-trans (≤-respʳ-≃ (≃-symm (∣x∣≃x⊔-x (diff k)))
                                (x≤y⊔x (- diff k) (diff k)))
                     (riemannSum-close f g ε bound k))

  integral-close : ∣ A - B ∣ ≤ ε
  integral-close = ≤-respˡ-≃ (≃-symm (∣x∣≃x⊔-x (A - B)))
    (x≤z∧y≤z⇒x⊔y≤z upper lower)
