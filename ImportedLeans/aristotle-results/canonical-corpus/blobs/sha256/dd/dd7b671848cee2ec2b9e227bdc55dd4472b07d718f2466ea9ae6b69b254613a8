{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- A constructed normalized invariant (Haar) integral on the circle group.
--
-- The Yang-Mills lane of this repository *postulates* the standard analytic
-- package for compact groups, whose central component is a normalized
-- invariant integral (`NormalizedHaarTheory` in
-- `DASHI/Physics/YangMills/CompactLieAnalyticPackage.agda`); no proved
-- inhabitant exists anywhere in the tree, and this is the base obstruction
-- recorded in `docs/ym/YangMillsClayObstructionReport.md`.
--
-- This module removes that obstruction for the simplest nontrivial compact
-- group, the circle R/Z, over the *constructed* Bishop reals:
--
--   * `integral-realShift` -- the constructive Riemann integral of a
--     1-periodic uniformly continuous function is invariant under
--     translation by an *arbitrary real* number, not merely a rational one;
--   * `haar` and the record `CircleHaar` -- the resulting functional,
--     together with proofs of normalisation, additivity, monotonicity,
--     positivity and full translation invariance, i.e. an inhabited Haar
--     specification for U(1).
--
-- The passage from rational to arbitrary real translations uses the Bishop
-- approximation `lemma-2-14` (every real is within 1/n of the rational
-- `seq x n`), the reduction of an arbitrary rational shift to a node shift
-- modulo the period (`DASHI.Analysis.BishopCircleNodeShift`), and the
-- comparison estimate for the integral
-- (`DASHI.Analysis.BishopIntegralComparison`).
--
-- Postulate-free; no receipt, no authority import, no opaque field.
------------------------------------------------------------------------

module DASHI.Analysis.BishopCircleHaar where

open import Data.Nat as ℕ using (ℕ; zero; suc)
import Data.Nat.Properties as ℕP
open import Data.Integer as ℤ using (ℤ; +_; -[1+_])
import Data.Integer.Properties as ℤP
open import Data.Integer.Solver as ℤSolver
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; mkℚᵘ; 0ℚᵘ)
import Data.Rational.Unnormalised.Properties as ℚP
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong; cong₂)

open import Real
open import RealProperties
open import Sequence
open import DASHI.Analysis.BishopFiniteSumLemmas
open import DASHI.Analysis.BishopRiemannIntegral
open import DASHI.Analysis.BishopRiemannIntegralAdditivity
open import DASHI.Analysis.BishopIntegralComparison
open import DASHI.Analysis.BishopPeriodicShift
open import DASHI.Analysis.BishopCircleInvariance
open import DASHI.Analysis.BishopCircleNodeShift

------------------------------------------------------------------------
-- Every rational is a node of some partition, up to a whole number of
-- periods.  (`t / (p+1) = q + K`, with `t`, `p`, `K` natural.)

record RatNode (q : ℚᵘ) : Set where
  field
    p t wind : ℕ
    nodeEq : node p t ≃ q ⋆ + natToℝ wind

private
  open ℤSolver.+-*-Solver

  negCase : ∀ (S D : ℤ) →
    (S ℤ.* D) ℤ.* (D ℤ.+ + 1)
      ≡ ((ℤ.- S) ℤ.* + 1 ℤ.+ S ℤ.* (D ℤ.+ + 1)) ℤ.* (D ℤ.+ + 1)
  negCase = solve 2
    (λ S D → (S :* D) :* (D :+ con (+ 1))
               := ((:- S) :* con (+ 1) :+ S :* (D :+ con (+ 1))) :* (D :+ con (+ 1)))
    refl

  -- (t / (p+1)) ⋆ ≃ q ⋆ + K, given the rational identity t/(p+1) = q + K/1.
  fromRatEq : ∀ (q : ℚᵘ) (p t w : ℕ) →
    (+ t ℚ./ suc p) ℚ.≃ q ℚ.+ (+ w ℚ./ 1) →
    node p t ≃ q ⋆ + natToℝ w
  fromRatEq q p t w ratEq = ≃-trans (⋆-cong ratEq)
    (≃-trans (⋆-distrib-+ q (+ w ℚ./ 1))
             (+-congʳ (q ⋆) (≃-symm (natToℝ-⋆ w))))

ratNode : ∀ q → RatNode q
ratNode (mkℚᵘ (+ n) d-1) = record
  { p = d-1 ; t = n ; wind = 0
  ; nodeEq = fromRatEq (mkℚᵘ (+ n) d-1) d-1 n 0
      (ℚP.≃-sym (ℚP.+-identityʳ (mkℚᵘ (+ n) d-1)))
  }
ratNode (mkℚᵘ (-[1+ n ]) d-1) = record
  { p = d-1 ; t = suc n ℕ.* d-1 ; wind = suc n
  ; nodeEq = fromRatEq (mkℚᵘ (-[1+ n ]) d-1) d-1 (suc n ℕ.* d-1) (suc n)
      (ℚ.*≡* step)
  }
  where
  S D : ℤ
  S = + suc n
  D = + d-1

  lhsNum : + (suc n ℕ.* d-1) ≡ S ℤ.* D
  lhsNum = ℤP.pos-* (suc n) d-1

  denom : + (suc d-1 ℕ.* 1) ≡ D ℤ.+ + 1
  denom = trans (cong +_ (ℕP.*-identityʳ (suc d-1)))
                (trans (cong +_ (ℕP.+-comm 1 d-1)) (ℤP.pos-+ d-1 1))

  denom′ : + suc d-1 ≡ D ℤ.+ + 1
  denom′ = trans (cong +_ (ℕP.+-comm 1 d-1)) (ℤP.pos-+ d-1 1)

  step : + (suc n ℕ.* d-1) ℤ.* + (suc d-1 ℕ.* 1)
           ≡ (-[1+ n ] ℤ.* + 1 ℤ.+ + suc n ℤ.* + suc d-1) ℤ.* + suc d-1
  step = trans (cong₂ ℤ._*_ lhsNum denom)
         (trans (negCase S D)
                (sym (cong₂ (λ u v → ((ℤ.- S) ℤ.* + 1 ℤ.+ S ℤ.* u) ℤ.* v)
                            denom′ denom′)))

------------------------------------------------------------------------
-- Invariance of the integral under an arbitrary real translation.

module _ (f : ℝ → ℝ) (mc : UniformModulus f) (per : ∀ x → f (x + 1ℝ) ≃ f x) where
  open UniformModulus mc

  private
    shifted : ∀ (a : ℝ) → UniformModulus (λ x → f (x + a))
    shifted a = shiftModulus f mc a

    -- (a + K) - node ≃ a - q, when node ≃ q + K.
    approxDiff : ∀ (a q n : ℝ) → (a + n) - (q + n) ≃ a - q
    approxDiff a q n = ℝ-Solver.solve 3
      (λ u v w → (u ⊕ w) ⊖ (v ⊕ w) ⊜ u ⊖ v) ≃-refl a q n
      where open ℝ-Solver

    argDiff : ∀ (x a n c : ℝ) → ((x + a) + c) - (x + n) ≃ (a + c) - n
    argDiff x a n c = ℝ-Solver.solve 4
      (λ u v w z → ((u ⊕ v) ⊕ z) ⊖ (u ⊕ w) ⊜ (v ⊕ z) ⊖ w) ≃-refl x a n c
      where open ℝ-Solver

  integral-realShift : ∀ (a : ℝ) →
    integral (λ x → f (x + a)) (shifted a) ≃ integral f mc
  integral-realShift a = ∣x-y∣≤k⁻¹⇒x≃y
    (integral (λ x → f (x + a)) (shifted a)) (integral f mc) main
    where
    main : ∀ (k : ℕ) → .{{_ : ℕ.NonZero k}} →
      ∣ integral (λ x → f (x + a)) (shifted a) - integral f mc ∣
        ≤ (+ 1 ℚ./ k) ⋆
    main (suc j) = ≤-respˡ-≃ (∣-∣-cong (+-congʳ _ (-‿cong nodeInt))) comparison
      where
      d : ℕ
      d = δ j

      q : ℚᵘ
      q = seq a (suc d)

      rn : RatNode q
      rn = ratNode q

      open RatNode rn

      -- the node is within 1/(δ j + 1) of a shifted by K periods
      close : ∣ (a + natToℝ wind) - node p t ∣ ≤ (+ 1 ℚ./ suc d) ⋆
      close = ≤-respˡ-≃
        (∣-∣-cong (≃-symm (≃-trans (+-congʳ (a + natToℝ wind) (-‿cong nodeEq))
                                   (approxDiff a (q ⋆) (natToℝ wind)))))
        (lemma-2-14 a (suc d))

      pointwise : ∀ x → ∣ f (x + a) - f (x + node p t) ∣ ≤ (+ 1 ℚ./ suc j) ⋆
      pointwise x = ≤-respˡ-≃ (∣-∣-cong (+-congˡ (- f (x + node p t)) shiftBack))
        (δ-cont j ((x + a) + natToℝ wind) (x + node p t) argClose)
        where
        shiftBack : f ((x + a) + natToℝ wind) ≃ f (x + a)
        shiftBack = per-nat f mc per wind (x + a)

        argClose : ∣ ((x + a) + natToℝ wind) - (x + node p t) ∣ ≤ (+ 1 ℚ./ suc d) ⋆
        argClose = ≤-respˡ-≃
          (∣-∣-cong (≃-symm (argDiff x a (node p t) (natToℝ wind)))) close

      comparison :
        ∣ integral (λ x → f (x + a)) (shifted a)
          - integral (λ x → f (x + node p t)) (shifted (node p t)) ∣
          ≤ (+ 1 ℚ./ suc j) ⋆
      comparison = integral-close (λ x → f (x + a)) (λ x → f (x + node p t))
        (shifted a) (shifted (node p t)) ((+ 1 ℚ./ suc j) ⋆) pointwise

      nodeInt : integral (λ x → f (x + node p t)) (shifted (node p t))
                  ≃ integral f mc
      nodeInt = integral-nodeShift f mc per p t

------------------------------------------------------------------------
-- The Haar package for the circle group.

record PeriodicUC : Set where
  field
    fun : ℝ → ℝ
    mod : UniformModulus fun
    per : ∀ x → fun (x + 1ℝ) ≃ fun x

open PeriodicUC

haar : PeriodicUC → ℝ
haar F = integral (fun F) (mod F)

-- the constant functions are periodic
constPeriodic : ℝ → PeriodicUC
constPeriodic c = record
  { fun = λ _ → c ; mod = constModulus c ; per = λ _ → ≃-refl }

-- translation acts on periodic functions
translate : PeriodicUC → ℝ → PeriodicUC
translate F a = record
  { fun = λ x → fun F (x + a)
  ; mod = shiftModulus (fun F) (mod F) a
  ; per = λ x → ≃-trans
      (uc-cong (fun F) (mod F) ((x + 1ℝ) + a) ((x + a) + 1ℝ) (swap x))
      (per F (x + a))
  }
  where
  swap : ∀ x → (x + 1ℝ) + a ≃ (x + a) + 1ℝ
  swap x = ℝ-Solver.solve 3 (λ u v w → (u ⊕ w) ⊕ v ⊜ (u ⊕ v) ⊕ w) ≃-refl x a 1ℝ
    where open ℝ-Solver

-- sums of periodic functions are periodic
addPeriodic : PeriodicUC → PeriodicUC → PeriodicUC
addPeriodic F G = record
  { fun = λ x → fun F x + fun G x
  ; mod = sumModulus (fun F) (fun G) (mod F) (mod G)
  ; per = λ x → +-cong (per F x) (per G x)
  }

------------------------------------------------------------------------
-- ... and its defining properties, all proved.

haar-normalized : haar (constPeriodic 1ℝ) ≃ 1ℝ
haar-normalized = integral-one

haar-const : ∀ c → haar (constPeriodic c) ≃ c
haar-const c = integral-const c

haar-add : ∀ F G → haar (addPeriodic F G) ≃ haar F + haar G
haar-add F G = integral-add (fun F) (fun G) (mod F) (mod G)

haar-mono : ∀ F G → (∀ x → fun F x ≤ fun G x) → haar F ≤ haar G
haar-mono F G h = integral-mono (fun F) (fun G) (mod F) (mod G) h

haar-nonNeg : ∀ F → (∀ x → 0ℝ ≤ fun F x) → 0ℝ ≤ haar F
haar-nonNeg F h = integral-nonNeg (fun F) (mod F) h

haar-invariant : ∀ F a → haar (translate F a) ≃ haar F
haar-invariant F a = integral-realShift (fun F) (mod F) (per F) a

------------------------------------------------------------------------
-- Packaged: a normalized, additive, monotone, translation invariant
-- functional on the uniformly continuous functions of the circle group,
-- with a proved inhabitant.

record CircleHaar : Set where
  field
    I           : PeriodicUC → ℝ
    normalized  : I (constPeriodic 1ℝ) ≃ 1ℝ
    additive    : ∀ F G → I (addPeriodic F G) ≃ I F + I G
    monotone    : ∀ F G → (∀ x → fun F x ≤ fun G x) → I F ≤ I G
    positive    : ∀ F → (∀ x → 0ℝ ≤ fun F x) → 0ℝ ≤ I F
    invariant   : ∀ F a → I (translate F a) ≃ I F

circleHaar : CircleHaar
circleHaar = record
  { I          = haar
  ; normalized = haar-normalized
  ; additive   = haar-add
  ; monotone   = haar-mono
  ; positive   = haar-nonNeg
  ; invariant  = haar-invariant
  }
