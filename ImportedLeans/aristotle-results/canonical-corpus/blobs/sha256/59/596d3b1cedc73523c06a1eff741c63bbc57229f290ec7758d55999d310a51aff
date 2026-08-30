{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- Invariance of the constructive integral under rational translations.
--
-- For a 1-periodic uniformly continuous function on the Bishop reals -- i.e.
-- a uniformly continuous function on the circle group R/Z -- the integral
-- built in `DASHI.Analysis.BishopRiemannIntegral` is invariant under
-- translation by every rational point t/(p+1) of the circle.  Together with
-- `integral-const` (normalisation) and `integral-add` (additivity) this is a
-- normalised, additive, rational-translation-invariant integral on a
-- nontrivial compact group, constructed rather than postulated.
--
-- What is still missing for a genuine Haar integral is invariance under
-- *arbitrary* real translations (a density/continuity argument) and, for the
-- Yang-Mills lane, the passage to SU(N); see
-- `docs/ym/YangMillsClayObstructionReport.md`.
--
-- Postulate-free, over the vendored Bishop constructive reals.
------------------------------------------------------------------------

module DASHI.Analysis.BishopCircleInvariance where

open import Data.Nat as ℕ using (ℕ; zero; suc)
import Data.Nat.Properties as ℕP
open import Data.Integer as ℤ using (ℤ; +_)
import Data.Integer.Properties as ℤP
open import Data.Integer.Solver as ℤSolver
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong; cong₂)

open import Real
open import RealProperties
open import Sequence
open import DASHI.Analysis.BishopFiniteSumLemmas
open import DASHI.Analysis.BishopRiemannIntegral
open import DASHI.Analysis.BishopPeriodicShift

private
  open ℤSolver.+-*-Solver

  scaleℤ : ∀ (T P R : ℤ) → T ℤ.* (P ℤ.* R) ≡ (T ℤ.* R) ℤ.* P
  scaleℤ = solve 3 (λ T P R → T :* (P :* R) := (T :* R) :* P) refl

------------------------------------------------------------------------
-- A node of a coarse partition is a node of every refinement of it.

node-scale : ∀ p t r → node p t ≃ node (refine p r) (t ℕ.* suc r)
node-scale p t r = ⋆-cong (ℚ.*≡* step)
  where
  step : + t ℤ.* + (suc p ℕ.* suc r) ≡ + (t ℕ.* suc r) ℤ.* + (suc p)
  step = trans (cong (+ t ℤ.*_) (ℤP.pos-* (suc p) (suc r)))
         (trans (scaleℤ (+ t) (+ suc p) (+ suc r))
                (cong (ℤ._* + suc p) (sym (ℤP.pos-* t (suc r)))))

------------------------------------------------------------------------
-- Refinements form a strictly increasing sequence of partitions.

refine-mono : ∀ p r → refine p r ℕ.< refine p (suc r)
refine-mono p r = ℕP.+-mono-<-≤ (ℕP.n<1+n r)
  (ℕP.*-monoʳ-≤ p (ℕP.n≤1+n (suc r)))

------------------------------------------------------------------------
-- Translating the argument does not change the modulus of continuity.

shift-diff : ∀ x y a → (x + a) - (y + a) ≃ x - y
shift-diff x y a = ℝ-Solver.solve 3 (λ u v w → (u ⊕ w) ⊖ (v ⊕ w) ⊜ u ⊖ v) ≃-refl x y a
  where open ℝ-Solver

shiftModulus : ∀ (f : ℝ → ℝ) → UniformModulus f → (a : ℝ) →
  UniformModulus (λ x → f (x + a))
shiftModulus f mc a = record
  { δ      = UniformModulus.δ mc
  ; δ-cont = λ j x y hyp →
      UniformModulus.δ-cont mc j (x + a) (y + a)
        (≤-respˡ-≃ (∣-∣-cong (≃-symm (shift-diff x y a))) hyp)
  }

------------------------------------------------------------------------
-- Rational-translation invariance.

module _ (f : ℝ → ℝ) (mc : UniformModulus f)
         (per : ∀ x → f (x + 1ℝ) ≃ f x) where

  rationalShiftSum : ∀ p t r → t ℕ.≤ suc p →
    riemannSum (λ x → f (x + node p t)) (refine p r)
      ≃ riemannSum f (refine p r)
  rationalShiftSum p t r t≤p = ≃-trans
    (*-congˡ (∑₀-congruent
      (λ i → uc-cong f mc (node (refine p r) i + node p t)
                          (node (refine p r) i + node (refine p r) (t ℕ.* suc r))
                          (+-congʳ (node (refine p r) i) (node-scale p t r)))
      (suc (refine p r))))
    (riemannSum-shift f mc per (refine p r) (t ℕ.* suc r)
      (ℕP.*-monoˡ-≤ (suc r) t≤p))

  integral-rationalShift : ∀ p t → t ℕ.≤ suc p →
    integral (λ x → f (x + node p t)) (shiftModulus f mc (node p t))
      ≃ integral f mc
  integral-rationalShift p t t≤p = uniqueness-of-limits conv subB
    where
    a : ℝ
    a = node p t

    A : (λ m → riemannSum (λ x → f (x + a)) m) isConvergent
    A = riemannSum-isConvergent (λ x → f (x + a)) (shiftModulus f mc a)

    B : (λ m → riemannSum f m) isConvergent
    B = riemannSum-isConvergent f mc

    subA : (λ r → riemannSum (λ x → f (x + a)) (refine p r)) ConvergesTo lim A
    subA = xₙ⊆yₙ∧yₙ→y⇒xₙ→y
      (subseq* (refine p , (λ r → ≃-refl) , refine-mono p)) A

    subB : (λ r → riemannSum f (refine p r)) ConvergesTo lim B
    subB = xₙ⊆yₙ∧yₙ→y⇒xₙ→y
      (subseq* (refine p , (λ r → ≃-refl) , refine-mono p)) B

    conv : (λ r → riemannSum f (refine p r)) ConvergesTo lim A
    conv = xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
      (λ r → rationalShiftSum p t r t≤p)
      (lim A , subA)
