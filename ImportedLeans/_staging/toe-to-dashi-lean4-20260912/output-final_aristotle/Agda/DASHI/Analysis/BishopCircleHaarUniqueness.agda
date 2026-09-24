{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- Uniqueness of the Haar integral on the circle group.
--
-- `DASHI.Analysis.BishopCircleHaar` constructs a normalized, positive,
-- translation invariant functional `haar` on the 1-periodic uniformly
-- continuous functions.  Existence alone does not identify a measure: what
-- makes the construction *the* Haar integral is that it is the only such
-- functional.  This module proves that:
--
--     for every normalized, monotone, linear, translation invariant
--     functional `I` on periodic uniformly continuous functions,
--     and every such function `F`,        I F ≃ haar F.
--
-- The argument is the classical averaging one, made constructive.  For a
-- partition index `k` the average of the `k+1` translates of `F` by the
-- partition nodes is again an admissible integrand; the functional `I`
-- assigns it the value `I F`, because `I` is linear and invariant, while
-- *pointwise* that average is the Riemann sum of the translated function
-- and is therefore uniformly close to `haar F`.  Monotonicity turns the
-- uniform pointwise bound into a bound on `I`, and the two computations of
-- the same number are forced together.
--
-- Postulate-free, over the constructed Bishop reals.
------------------------------------------------------------------------

module DASHI.Analysis.BishopCircleHaarUniqueness where

open import Data.Nat as ℕ using (ℕ; zero; suc)
import Data.Nat.Properties as ℕP
open import Data.Integer as ℤ using (ℤ; +_)
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Real
open import RealProperties
open import Sequence
open import DASHI.Analysis.BishopFiniteSumLemmas
open import DASHI.Analysis.BishopRiemannIntegral
open import DASHI.Analysis.BishopIntegralComparison
open import DASHI.Analysis.BishopIntegralLinearity using (scaleModulus)
open import DASHI.Analysis.BishopIntegralRate
open import DASHI.Analysis.BishopPeriodicShift using (uc-cong)
open import DASHI.Analysis.BishopCircleInvariance using (shiftModulus)
open import DASHI.Analysis.BishopCircleHaar

open PeriodicUC

------------------------------------------------------------------------
-- Scalar multiples of periodic functions are periodic, so the integrands
-- form a vector space on which a linear functional can be required.

scalePeriodic : ℝ → PeriodicUC → PeriodicUC
scalePeriodic c F = record
  { fun = λ x → c * fun F x
  ; mod = scaleModulus c (fun F) (mod F)
  ; per = λ x → *-congˡ (per F x)
  }

------------------------------------------------------------------------
-- An abstract normalized invariant integral.

record HaarFunctional : Set where
  field
    I           : PeriodicUC → ℝ
    normalized  : I (constPeriodic 1ℝ) ≃ 1ℝ
    additive    : ∀ F G → I (addPeriodic F G) ≃ I F + I G
    homogeneous : ∀ c F → I (scalePeriodic c F) ≃ c * I F
    monotone    : ∀ F G → (∀ x → fun F x ≤ fun G x) → I F ≤ I G
    invariant   : ∀ F a → I (translate F a) ≃ I F

-- the constructed integral is one
haarFunctional : HaarFunctional
haarFunctional = record
  { I           = haar
  ; normalized  = haar-normalized
  ; additive    = haar-add
  ; homogeneous = λ c F → integral-scale c (fun F) (mod F)
                            (scaleModulus c (fun F) (mod F))
  ; monotone    = haar-mono
  ; invariant   = haar-invariant
  }
  where open import DASHI.Analysis.BishopIntegralLinearity using (integral-scale)

------------------------------------------------------------------------
-- Elementary consequences of the axioms.

module _ (J : HaarFunctional) where
  open HaarFunctional J

  I-cong : ∀ F G → (∀ x → fun F x ≃ fun G x) → I F ≃ I G
  I-cong F G h = ≤-antisym
    (monotone F G (λ x → ≤-reflexive (h x)))
    (monotone G F (λ x → ≤-reflexive (≃-symm (h x))))

  I-const : ∀ c → I (constPeriodic c) ≃ c
  I-const c = ≃-trans
    (I-cong (constPeriodic c) (scalePeriodic c (constPeriodic 1ℝ))
      (λ x → ≃-symm (*-identityʳ c)))
    (≃-trans (homogeneous c (constPeriodic 1ℝ))
             (≃-trans (*-congˡ normalized) (*-identityʳ c)))

  -- a uniform pointwise bound becomes a bound on the value of I
  private
    upperShift : ∀ {a b e : ℝ} → a - b ≤ e → a ≤ b + e
    upperShift {a} {b} {e} h = ≤-respʳ-≃ (+-comm e b) (≤-respˡ-≃ collapse
      (+-mono-≤ h (≤-refl {b})))
      where
      open ℝ-Solver

      collapse : (a - b) + b ≃ a
      collapse = ℝ-Solver.solve 2 (λ u v → (u ⊖ v) ⊕ v ⊜ u) ≃-refl a b

    downShift : ∀ {a b e : ℝ} → a ≤ b + e → a - e ≤ b
    downShift {a} {b} {e} h = ≤-respʳ-≃ collapse (+-mono-≤ h (≤-refl { - e}))
      where
      open ℝ-Solver

      collapse : (b + e) - e ≃ b
      collapse = ℝ-Solver.solve 2 (λ u v → (u ⊕ v) ⊖ v ⊜ u) ≃-refl b e

  I-close : ∀ (F : PeriodicUC) (c e : ℝ) →
    (∀ x → ∣ fun F x - c ∣ ≤ e) → ∣ I F - c ∣ ≤ e
  I-close F c e h = ≤-respˡ-≃ (≃-symm (∣x∣≃x⊔-x (I F - c)))
    (x≤z∧y≤z⇒x⊔y≤z upper lower)
    where
    open ℝ-Solver

    pointUpper : ∀ x → fun F x ≤ c + e
    pointUpper x = upperShift (≤-trans x≤∣x∣ (h x))

    pointLower : ∀ x → c - e ≤ fun F x
    pointLower x = downShift {c} {fun F x} {e} (upperShift {c} {fun F x} {e} near)
      where
      flip : c - fun F x ≃ - (fun F x - c)
      flip = ℝ-Solver.solve 2 (λ u v → v ⊖ u ⊜ ⊝ (u ⊖ v)) ≃-refl (fun F x) c

      near : c - fun F x ≤ e
      near = ≤-trans (≤-trans (≤-reflexive flip) x≤∣x∣)
                     (≤-respˡ-≃ (≃-symm ∣-x∣≃∣x∣) (h x))

    upper : I F - c ≤ e
    upper = downShift {I F} {e} {c}
      (≤-respʳ-≃ (+-comm c e)
        (≤-respʳ-≃ (I-const (c + e))
          (monotone F (constPeriodic (c + e)) pointUpper)))

    lower : - (I F - c) ≤ e
    lower = ≤-respˡ-≃ flip
      (downShift {c} {e} {I F} (upperShift {c} {e} {I F} base))
      where
      flip : c - I F ≃ - (I F - c)
      flip = ℝ-Solver.solve 2 (λ u v → v ⊖ u ⊜ ⊝ (u ⊖ v)) ≃-refl (I F) c

      base : c - e ≤ I F
      base = ≤-respˡ-≃ (I-const (c - e))
        (monotone (constPeriodic (c - e)) F pointLower)

------------------------------------------------------------------------
-- Averages of translates.

  sumTranslates : PeriodicUC → ℕ → ℕ → PeriodicUC
  sumTranslates F k zero    = constPeriodic 0ℝ
  sumTranslates F k (suc n) =
    addPeriodic (sumTranslates F k n) (translate F (node k n))

  fun-sumTranslates : ∀ F k n x →
    fun (sumTranslates F k n) x ≃ ∑₀ (λ i → fun F (x + node k i)) n
  fun-sumTranslates F k zero    x = ≃-refl
  fun-sumTranslates F k (suc n) x =
    +-congˡ (fun F (x + node k n)) (fun-sumTranslates F k n x)

  I-sumTranslates : ∀ F k n → I (sumTranslates F k n) ≃ natToℝ n * I F
  I-sumTranslates F k zero    = ≃-trans (I-const 0ℝ) (≃-symm (*-zeroˡ (I F)))
  I-sumTranslates F k (suc n) = ≃-trans
    (additive (sumTranslates F k n) (translate F (node k n)))
    (≃-trans (+-cong (I-sumTranslates F k n) (invariant F (node k n)))
    (≃-trans (+-congʳ (natToℝ n * I F) (≃-symm (*-identityˡ (I F))))
             (≃-symm (*-distribʳ-+ (I F) (natToℝ n) 1ℝ))))

  average : PeriodicUC → ℕ → PeriodicUC
  average F k = scalePeriodic ((width k) ⋆) (sumTranslates F k (suc k))

  I-average : ∀ F k → I (average F k) ≃ I F
  I-average F k = ≃-trans (homogeneous ((width k) ⋆) (sumTranslates F k (suc k)))
    (≃-trans (*-congˡ (I-sumTranslates F k (suc k)))
    (≃-trans (≃-symm (*-assoc ((width k) ⋆) (natToℝ (suc k)) (I F)))
    (≃-trans (*-congʳ (width-unit k)) (*-identityˡ (I F)))))

------------------------------------------------------------------------
-- Uniqueness.

  private
    preShiftModulus : ∀ (f : ℝ → ℝ) → UniformModulus f → (x : ℝ) →
      UniformModulus (λ y → f (x + y))
    preShiftModulus f m x = record
      { δ      = UniformModulus.δ m
      ; δ-cont = λ j y₁ y₂ hyp →
          UniformModulus.δ-cont m j (x + y₁) (x + y₂)
            (≤-respˡ-≃ (∣-∣-cong (≃-symm same)) hyp)
      }
      where
      open ℝ-Solver

      same : ∀ {y₁ y₂ : ℝ} → (x + y₁) - (x + y₂) ≃ y₁ - y₂
      same {y₁} {y₂} = ℝ-Solver.solve 3
        (λ u v w → (u ⊕ v) ⊖ (u ⊕ w) ⊜ v ⊖ w) ≃-refl x y₁ y₂

  haar-unique : ∀ (F : PeriodicUC) → I F ≃ haar F
  haar-unique F = ∣x-y∣≤k⁻¹⇒x≃y (I F) (haar F) main
    where
    f : ℝ → ℝ
    f = fun F

    m : UniformModulus f
    m = mod F

    main : ∀ (k : ℕ) → .{{_ : ℕ.NonZero k}} →
      ∣ I F - haar F ∣ ≤ (+ 1 ℚ./ k) ⋆
    main (suc j) = ≤-respˡ-≃ (∣-∣-cong (+-congˡ (- haar F) (I-average F N)))
      (I-close (average F N) (haar F) ((+ 1 ℚ./ suc j) ⋆) pointwise)
      where
      N : ℕ
      N = UniformModulus.δ m j

      pointwise : ∀ x →
        ∣ fun (average F N) x - haar F ∣ ≤ (+ 1 ℚ./ suc j) ⋆
      pointwise x =
        ≤-respˡ-≃ (∣-∣-cong (+-congˡ (- haar F) (≃-symm avgVal))) rsBound
        where
        g : ℝ → ℝ
        g y = f (x + y)

        mx : UniformModulus g
        mx = preShiftModulus f m x

        avgVal : fun (average F N) x ≃ riemannSum g N
        avgVal = *-congˡ (fun-sumTranslates F N (suc N) x)

        shifted : integral g mx ≃ haar F
        shifted = ≃-trans
          (integral-cong g (λ y → f (y + x)) mx (shiftModulus f m x)
            (λ y → uc-cong f m (x + y) (y + x) (+-comm x y)))
          (integral-realShift f m (per F) x)

        rsBound : ∣ riemannSum g N - haar F ∣ ≤ (+ 1 ℚ./ suc j) ⋆
        rsBound = ≤-respˡ-≃ (∣x-y∣≃∣y-x∣ (haar F) (riemannSum g N))
          (≤-respˡ-≃ (∣-∣-cong (+-congˡ (- riemannSum g N) shifted))
            (integral-riemannSum-bound g mx j N ℕP.≤-refl))


------------------------------------------------------------------------
-- Consequently any two normalized invariant integrals on the circle
-- agree: the Haar integral of U(1) is unique.

haarFunctional-unique : ∀ (J K : HaarFunctional) (F : PeriodicUC) →
  HaarFunctional.I J F ≃ HaarFunctional.I K F
haarFunctional-unique J K F =
  ≃-trans (haar-unique J F) (≃-symm (haar-unique K F))
