{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- Additivity of the constructive Riemann integral on [0,1].
--
-- Together with `integral-const` this makes the integral a normalised
-- additive functional on the uniformly continuous functions: exactly the
-- shape that a normalised Haar integral on a compact group must have, minus
-- the invariance property (which is where the Yang-Mills lane is blocked; see
-- `docs/ym/YangMillsClayObstructionReport.md`).
--
-- Postulate-free, over the vendored Bishop constructive reals.
------------------------------------------------------------------------

module DASHI.Analysis.BishopRiemannIntegralAdditivity where

open import Data.Nat as ℕ using (ℕ; zero; suc; s≤s)
import Data.Nat.Properties as ℕP
open import Data.Integer as ℤ using (ℤ; +_)
open import Data.Integer.Solver as ℤSolver
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Real
open import RealProperties
open import ExtraProperties
open import Sequence
open import DASHI.Analysis.BishopFiniteSumLemmas
open import DASHI.Analysis.BishopRiemannIntegral

------------------------------------------------------------------------
-- Finite sums are additive.

∑₀-add : ∀ (f g : ℕ → ℝ) n → ∑₀ (λ i → f i + g i) n ≃ ∑₀ f n + ∑₀ g n
∑₀-add f g zero = ≃-symm (+-identityʳ 0ℝ)
∑₀-add f g (suc n) = ≃-trans (+-congˡ (f n + g n) (∑₀-add f g n))
  (solve 4 (λ a b c d → (a ⊕ b) ⊕ (c ⊕ d) ⊜ (a ⊕ c) ⊕ (b ⊕ d))
    ≃-refl (∑₀ f n) (∑₀ g n) (f n) (g n))
  where open ℝ-Solver

riemannSum-add : ∀ (f g : ℝ → ℝ) m →
  riemannSum (λ x → f x + g x) m ≃ riemannSum f m + riemannSum g m
riemannSum-add f g m =
  ≃-trans (*-congˡ (∑₀-add (λ i → f (node m i)) (λ i → g (node m i)) (suc m)))
          (*-distribˡ-+ ((width m) ⋆)
            (∑₀ (λ i → f (node m i)) (suc m))
            (∑₀ (λ i → g (node m i)) (suc m)))

------------------------------------------------------------------------
-- A modulus of uniform continuity for a sum of two functions.

private
  dbl : ℕ → ℕ
  dbl j = ℕ.pred (2 ℕ.* suc j)

sumModulus : ∀ (f g : ℝ → ℝ) →
  UniformModulus f → UniformModulus g → UniformModulus (λ x → f x + g x)
sumModulus f g mf mg = record { δ = δs ; δ-cont = cont }
  where
  open ℤSolver.+-*-Solver

  δf = UniformModulus.δ mf
  δg = UniformModulus.δ mg

  δs : ℕ → ℕ
  δs j = δf (dbl j) ℕ.⊔ δg (dbl j)

  halves : ∀ j →
    (+ 1 ℚ./ (2 ℕ.* suc j)) ⋆ + (+ 1 ℚ./ (2 ℕ.* suc j)) ⋆ ≤ (+ 1 ℚ./ suc j) ⋆
  halves j = ≤-reflexive (≃-trans
    (≃-symm (⋆-distrib-+ (+ 1 ℚ./ (2 ℕ.* suc j)) (+ 1 ℚ./ (2 ℕ.* suc j))))
    (⋆-cong (ℚ.*≡* (solve 1 (λ z →
      (con (+ 1) :* (con (+ 2) :* z) :+ con (+ 1) :* (con (+ 2) :* z)) :* z
        := con (+ 1) :* (con (+ 2) :* z :* (con (+ 2) :* z)))
      refl (+ suc j)))))

  cont : ∀ j x y → ∣ x - y ∣ ≤ (+ 1 ℚ./ suc (δs j)) ⋆ →
         ∣ (f x + g x) - (f y + g y) ∣ ≤ (+ 1 ℚ./ suc j) ⋆
  cont j x y hyp = ≤-trans t₁ (≤-trans t₂ (≤-trans t₃ (halves j)))
    where
    open ℝ-Solver

    hf : ∣ x - y ∣ ≤ (+ 1 ℚ./ suc (δf (dbl j))) ⋆
    hf = ≤-trans hyp (p≤q⇒p⋆≤q⋆ _ _
      (q≤r⇒+p/r≤+p/q 1 (suc (δf (dbl j))) (suc (δs j))
        (s≤s (ℕP.m≤m⊔n (δf (dbl j)) (δg (dbl j))))))

    hg : ∣ x - y ∣ ≤ (+ 1 ℚ./ suc (δg (dbl j))) ⋆
    hg = ≤-trans hyp (p≤q⇒p⋆≤q⋆ _ _
      (q≤r⇒+p/r≤+p/q 1 (suc (δg (dbl j))) (suc (δs j))
        (s≤s (ℕP.m≤n⊔m (δf (dbl j)) (δg (dbl j))))))

    t₁ : ∣ (f x + g x) - (f y + g y) ∣ ≤ ∣ (f x - f y) + (g x - g y) ∣
    t₁ = ≤-reflexive (∣-∣-cong (ℝ-Solver.solve 4
      (λ a b c d → (a ⊕ c) ⊖ (b ⊕ d) ⊜ (a ⊖ b) ⊕ (c ⊖ d))
      ≃-refl (f x) (f y) (g x) (g y)))

    t₂ : ∣ (f x - f y) + (g x - g y) ∣ ≤ ∣ f x - f y ∣ + ∣ g x - g y ∣
    t₂ = ∣x+y∣≤∣x∣+∣y∣ (f x - f y) (g x - g y)

    t₃ : ∣ f x - f y ∣ + ∣ g x - g y ∣
           ≤ (+ 1 ℚ./ (2 ℕ.* suc j)) ⋆ + (+ 1 ℚ./ (2 ℕ.* suc j)) ⋆
    t₃ = +-mono-≤ (UniformModulus.δ-cont mf (dbl j) x y hf)
                  (UniformModulus.δ-cont mg (dbl j) x y hg)

------------------------------------------------------------------------
-- The integral is additive.

integral-add : ∀ (f g : ℝ → ℝ) (mf : UniformModulus f) (mg : UniformModulus g) →
  integral (λ x → f x + g x) (sumModulus f g mf mg)
    ≃ integral f mf + integral g mg
integral-add f g mf mg = uniqueness-of-limits
  (riemannSum-converges (λ x → f x + g x) (sumModulus f g mf mg))
  conv
  where
  base : (λ m → riemannSum f m + riemannSum g m)
           ConvergesTo (integral f mf + integral g mg)
  base = xₙ+yₙ→x₀+y₀ (riemannSum-isConvergent f mf) (riemannSum-isConvergent g mg)

  conv : (λ m → riemannSum (λ x → f x + g x) m)
           ConvergesTo (integral f mf + integral g mg)
  conv = xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ n → ≃-symm (riemannSum-add f g n))
    (integral f mf + integral g mg , base)
