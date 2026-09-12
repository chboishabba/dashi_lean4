{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- Fubini's theorem for the constructive Riemann integral on the square.
--
-- For a function of two real variables with a joint modulus of uniform
-- continuity, the two iterated integrals over [0,1]^2 agree.  This is
-- item 3 of the "what is still missing" list in
-- `docs/ym/YangMillsClayObstructionReport.md`: an interchange theorem is
-- what makes iterated integration behave like a measure, and it is the step
-- on which every later change-of-variables argument rests.
--
-- The proof is the classical one, made quantitative by the explicit rate of
-- `DASHI.Analysis.BishopIntegralRate`: both iterated integrals are within
-- 2/(4k) of the *same* double Riemann sum, once the partition is finer than
-- the joint modulus, and the double sum is symmetric because finite sums
-- commute.
--
-- Postulate-free, over the constructed Bishop reals.
------------------------------------------------------------------------

module DASHI.Analysis.BishopFubini where

open import Data.Nat as ℕ using (ℕ; zero; suc)
import Data.Nat.Properties as ℕP
open import Data.Integer as ℤ using (ℤ; +_)
open import Data.Integer.Solver as ℤSolver
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Real
open import RealProperties
open import Sequence
open import DASHI.Analysis.BishopFiniteSumLemmas
open import DASHI.Analysis.BishopRiemannIntegral
open import DASHI.Analysis.BishopIntegralComparison
open import DASHI.Analysis.BishopIntegralRate

------------------------------------------------------------------------
-- Two small lemmas.

zeroDist : ∀ (x : ℝ) (d : ℕ) → ∣ x - x ∣ ≤ (+ 1 ℚ./ suc d) ⋆
zeroDist x d = ≤-respˡ-≃
  (≃-symm (≃-trans (∣-∣-cong (+-inverseʳ x)) (nonNegx⇒∣x∣≃x nonNeg0)))
  (0≤width d)

halves : ∀ (n : ℕ) →
  (+ 1 ℚ./ (2 ℕ.* suc n)) ⋆ + (+ 1 ℚ./ (2 ℕ.* suc n)) ⋆ ≤ (+ 1 ℚ./ suc n) ⋆
halves n = ≤-reflexive (≃-trans
  (≃-symm (⋆-distrib-+ (+ 1 ℚ./ (2 ℕ.* suc n)) (+ 1 ℚ./ (2 ℕ.* suc n))))
  (⋆-cong (ℚ.*≡* (solve 1 (λ z →
    (con (+ 1) :* (con (+ 2) :* z) :+ con (+ 1) :* (con (+ 2) :* z)) :* z
      := con (+ 1) :* (con (+ 2) :* z :* (con (+ 2) :* z)))
    refl (+ suc n)))))
  where open ℤSolver.+-*-Solver

------------------------------------------------------------------------
-- Finite double sums commute.

∑₀-zero : ∀ (n : ℕ) → ∑₀ (λ _ → 0ℝ) n ≃ 0ℝ
∑₀-zero n = ≃-trans (∑₀-const 0ℝ n) (*-zeroʳ (natToℝ n))

∑₀-swap : ∀ (h : ℕ → ℕ → ℝ) (n p : ℕ) →
  ∑₀ (λ i → ∑₀ (λ j → h i j) p) n ≃ ∑₀ (λ j → ∑₀ (λ i → h i j) n) p
∑₀-swap h zero p = ≃-symm (≃-trans (∑₀-congruent (λ j → ≃-refl) p) (∑₀-zero p))
∑₀-swap h (suc n) p = ≃-trans
  (+-congˡ (∑₀ (λ j → h n j) p) (∑₀-swap h n p))
  (≃-symm (∑₀-add (λ j → ∑₀ (λ i → h i j) n) (λ j → h n j) p))
  where
  ∑₀-add : ∀ (u v : ℕ → ℝ) (q : ℕ) → ∑₀ (λ j → u j + v j) q ≃ ∑₀ u q + ∑₀ v q
  ∑₀-add u v zero = ≃-symm (+-identityʳ 0ℝ)
  ∑₀-add u v (suc q) = ≃-trans (+-congˡ (u q + v q) (∑₀-add u v q))
    (ℝ-Solver.solve 4 (λ a b c d → (a ⊕ b) ⊕ (c ⊕ d) ⊜ (a ⊕ c) ⊕ (b ⊕ d))
      ≃-refl (∑₀ u q) (∑₀ v q) (u q) (v q))
    where open ℝ-Solver

------------------------------------------------------------------------
-- A joint modulus of uniform continuity in two variables.

record UniformModulus₂ (f : ℝ → ℝ → ℝ) : Set where
  field
    δ      : ℕ → ℕ
    δ-cont : ∀ (j : ℕ) (x₁ y₁ x₂ y₂ : ℝ) →
             ∣ x₁ - x₂ ∣ ≤ (+ 1 ℚ./ suc (δ j)) ⋆ →
             ∣ y₁ - y₂ ∣ ≤ (+ 1 ℚ./ suc (δ j)) ⋆ →
             ∣ f x₁ y₁ - f x₂ y₂ ∣ ≤ (+ 1 ℚ./ suc j) ⋆

module _ (f : ℝ → ℝ → ℝ) (mf : UniformModulus₂ f) where
  open UniformModulus₂ mf

  ------------------------------------------------------------------------
  -- Sections and partial integrals.

  rowMod : ∀ (y : ℝ) → UniformModulus (λ x → f x y)
  rowMod y = record
    { δ      = δ
    ; δ-cont = λ j x₁ x₂ hyp → δ-cont j x₁ y x₂ y hyp (zeroDist y (δ j))
    }

  colMod : ∀ (x : ℝ) → UniformModulus (λ y → f x y)
  colMod x = record
    { δ      = δ
    ; δ-cont = λ j y₁ y₂ hyp → δ-cont j x y₁ x y₂ (zeroDist x (δ j)) hyp
    }

  rowIntegral : ℝ → ℝ
  rowIntegral y = integral (λ x → f x y) (rowMod y)

  colIntegral : ℝ → ℝ
  colIntegral x = integral (λ y → f x y) (colMod x)

  rowIntMod : UniformModulus rowIntegral
  rowIntMod = record
    { δ      = δ
    ; δ-cont = λ j y₁ y₂ hyp → integral-close
        (λ x → f x y₁) (λ x → f x y₂) (rowMod y₁) (rowMod y₂)
        ((+ 1 ℚ./ suc j) ⋆)
        (λ x → δ-cont j x y₁ x y₂ (zeroDist x (δ j)) hyp)
    }

  colIntMod : UniformModulus colIntegral
  colIntMod = record
    { δ      = δ
    ; δ-cont = λ j x₁ x₂ hyp → integral-close
        (λ y → f x₁ y) (λ y → f x₂ y) (colMod x₁) (colMod x₂)
        ((+ 1 ℚ./ suc j) ⋆)
        (λ y → δ-cont j x₁ y x₂ y hyp (zeroDist y (δ j)))
    }

  ------------------------------------------------------------------------
  -- The two iterated integrals.

  iteratedXY : ℝ            -- ∫dy ∫dx f
  iteratedXY = integral rowIntegral rowIntMod

  iteratedYX : ℝ            -- ∫dx ∫dy f
  iteratedYX = integral colIntegral colIntMod

  ------------------------------------------------------------------------
  -- The double Riemann sums are symmetric.

  private
    doubleXY : ℕ → ℝ
    doubleXY m = riemannSum (λ y → riemannSum (λ x → f x y) m) m

    doubleYX : ℕ → ℝ
    doubleYX m = riemannSum (λ x → riemannSum (λ y → f x y) m) m

    double-symm : ∀ m → doubleXY m ≃ doubleYX m
    double-symm m = ≃-trans expandXY (≃-symm (≃-trans expandYX swapped))
      where
      w : ℝ
      w = (width m) ⋆

      N : ℕ
      N = suc m

      h : ℕ → ℕ → ℝ
      h i jj = f (node m i) (node m jj)

      expandXY : doubleXY m ≃ w * (w * ∑₀ (λ jj → ∑₀ (λ i → h i jj) N) N)
      expandXY = *-congˡ (∑₀-scale w (λ jj → ∑₀ (λ i → h i jj) N) N)

      expandYX : doubleYX m ≃ w * (w * ∑₀ (λ i → ∑₀ (λ jj → h i jj) N) N)
      expandYX = *-congˡ (∑₀-scale w (λ i → ∑₀ (λ jj → h i jj) N) N)

      swapped : w * (w * ∑₀ (λ i → ∑₀ (λ jj → h i jj) N) N)
                  ≃ w * (w * ∑₀ (λ jj → ∑₀ (λ i → h i jj) N) N)
      swapped = *-congˡ (*-congˡ (∑₀-swap h N N))

  ------------------------------------------------------------------------
  -- Each iterated integral is close to the double Riemann sum.

  private
    -- with m = δ j, both approximations hold at tolerance 1/(j+1)
    closeXY : ∀ j → ∣ iteratedXY - doubleXY (δ j) ∣
                      ≤ (+ 1 ℚ./ suc j) ⋆ + (+ 1 ℚ./ suc j) ⋆
    closeXY j = ≤-trans (≤-reflexive (∣-∣-cong split))
      (≤-trans (∣x+y∣≤∣x∣+∣y∣ (iteratedXY - middle) (middle - doubleXY (δ j)))
               (+-mono-≤ outer inner))
      where
      open ℝ-Solver

      m : ℕ
      m = δ j

      middle : ℝ
      middle = riemannSum rowIntegral m

      split : iteratedXY - doubleXY m
                ≃ (iteratedXY - middle) + (middle - doubleXY m)
      split = ℝ-Solver.solve 3 (λ a b c → a ⊖ b ⊜ (a ⊖ c) ⊕ (c ⊖ b))
        ≃-refl iteratedXY (doubleXY m) middle

      outer : ∣ iteratedXY - middle ∣ ≤ (+ 1 ℚ./ suc j) ⋆
      outer = integral-riemannSum-bound rowIntegral rowIntMod j m ℕP.≤-refl

      pointwise : ∀ y → ∣ rowIntegral y - riemannSum (λ x → f x y) m ∣
                          ≤ (+ 1 ℚ./ suc j) ⋆
      pointwise y = integral-riemannSum-bound (λ x → f x y) (rowMod y) j m
        ℕP.≤-refl

      inner : ∣ middle - doubleXY m ∣ ≤ (+ 1 ℚ./ suc j) ⋆
      inner = riemannSum-close rowIntegral
        (λ y → riemannSum (λ x → f x y) m) ((+ 1 ℚ./ suc j) ⋆) pointwise m

    closeYX : ∀ j → ∣ iteratedYX - doubleYX (δ j) ∣
                      ≤ (+ 1 ℚ./ suc j) ⋆ + (+ 1 ℚ./ suc j) ⋆
    closeYX j = ≤-trans (≤-reflexive (∣-∣-cong split))
      (≤-trans (∣x+y∣≤∣x∣+∣y∣ (iteratedYX - middle) (middle - doubleYX (δ j)))
               (+-mono-≤ outer inner))
      where
      open ℝ-Solver

      m : ℕ
      m = δ j

      middle : ℝ
      middle = riemannSum colIntegral m

      split : iteratedYX - doubleYX m
                ≃ (iteratedYX - middle) + (middle - doubleYX m)
      split = ℝ-Solver.solve 3 (λ a b c → a ⊖ b ⊜ (a ⊖ c) ⊕ (c ⊖ b))
        ≃-refl iteratedYX (doubleYX m) middle

      outer : ∣ iteratedYX - middle ∣ ≤ (+ 1 ℚ./ suc j) ⋆
      outer = integral-riemannSum-bound colIntegral colIntMod j m ℕP.≤-refl

      pointwise : ∀ x → ∣ colIntegral x - riemannSum (λ y → f x y) m ∣
                          ≤ (+ 1 ℚ./ suc j) ⋆
      pointwise x = integral-riemannSum-bound (λ y → f x y) (colMod x) j m
        ℕP.≤-refl

      inner : ∣ middle - doubleYX m ∣ ≤ (+ 1 ℚ./ suc j) ⋆
      inner = riemannSum-close colIntegral
        (λ x → riemannSum (λ y → f x y) m) ((+ 1 ℚ./ suc j) ⋆) pointwise m

  ------------------------------------------------------------------------
  -- Fubini.

  fubini : iteratedXY ≃ iteratedYX
  fubini = ∣x-y∣≤k⁻¹⇒x≃y iteratedXY iteratedYX main
    where
    main : ∀ (k : ℕ) → .{{_ : ℕ.NonZero k}} →
      ∣ iteratedXY - iteratedYX ∣ ≤ (+ 1 ℚ./ k) ⋆
    main (suc k₀) = ≤-trans (≤-reflexive (∣-∣-cong split))
      (≤-trans (∣x+y∣≤∣x∣+∣y∣ (iteratedXY - D) (D - iteratedYX))
      (≤-trans (+-mono-≤ left right) (halves k₀)))
      where
      open ℝ-Solver

      k K2 K4 j : ℕ
      k  = suc k₀
      K2 = 2 ℕ.* k
      K4 = 2 ℕ.* K2
      j  = ℕ.pred K4

      D : ℝ
      D = doubleXY (δ j)

      split : iteratedXY - iteratedYX ≃ (iteratedXY - D) + (D - iteratedYX)
      split = ℝ-Solver.solve 3 (λ a b c → a ⊖ b ⊜ (a ⊖ c) ⊕ (c ⊖ b))
        ≃-refl iteratedXY iteratedYX D

      left : ∣ iteratedXY - D ∣ ≤ (+ 1 ℚ./ K2) ⋆
      left = ≤-trans (closeXY j) (halves (ℕ.pred K2))

      symmD : D ≃ doubleYX (δ j)
      symmD = double-symm (δ j)

      chain : ∣ iteratedYX - doubleYX (δ j) ∣ ≃ ∣ D - iteratedYX ∣
      chain = ≃-trans
        (∣-∣-cong (+-congʳ iteratedYX (-‿cong (≃-symm symmD))))
        (∣x-y∣≃∣y-x∣ iteratedYX D)

      right : ∣ D - iteratedYX ∣ ≤ (+ 1 ℚ./ K2) ⋆
      right = ≤-respˡ-≃ chain (≤-trans (closeYX j) (halves (ℕ.pred K2)))
