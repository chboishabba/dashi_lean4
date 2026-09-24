{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- Inversion invariance of the Haar integral of the n-torus.
--
-- `DASHI.Analysis.BishopCircleReflection` proves that the one-dimensional
-- integral of a periodic function is unchanged by `x ↦ - x`.  Here that
-- statement is lifted, coordinate by coordinate, to the iterated integral
-- of `DASHI.Analysis.BishopTorusHaar`:
--
--     ∫_{T^n} f (- v) dv = ∫_{T^n} f (v) dv,
--
-- i.e. the constructed torus measure is invariant under the inversion of
-- the group, which together with translation invariance is exactly
-- unimodularity of the measure.  For the lattice gauge measure built on
-- top of it this is the statement that reversing the orientation of every
-- link leaves every expectation value unchanged.
--
-- Postulate-free, over the constructed Bishop reals.
------------------------------------------------------------------------

module DASHI.Analysis.BishopTorusReflection where

open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Vec as Vec using (Vec; []; _∷_; lookup)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Integer as ℤ using (ℤ; +_)
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ)

open import Real
open import RealProperties
open import Sequence
open import DASHI.Analysis.BishopRiemannIntegral
open import DASHI.Analysis.BishopIntegralComparison
open import DASHI.Analysis.BishopPeriodicShift using (uc-cong)
open import DASHI.Analysis.BishopCircleReflection
  using (reflectModulus; integral-reflect)
open import DASHI.Analysis.BishopTorusHaar

------------------------------------------------------------------------
-- Coordinatewise negation.

negVec : ∀ {n} → Vec ℝ n → Vec ℝ n
negVec []      = []
negVec (x ∷ v) = (- x) ∷ negVec v

lookup-negVec : ∀ {n} (v : Vec ℝ n) (i : Fin n) →
  lookup (negVec v) i ≃ - lookup v i
lookup-negVec (x ∷ v) zero    = ≃-refl
lookup-negVec (x ∷ v) (suc i) = lookup-negVec v i

negVecModulus : ∀ {n} (f : Vec ℝ n → ℝ) → VecModulus f →
  VecModulus (λ v → f (negVec v))
negVecModulus f mf = record
  { δ      = VecModulus.δ mf
  ; δ-cont = λ j u v hyp →
      VecModulus.δ-cont mf j (negVec u) (negVec v)
        (λ i → ≤-respˡ-≃ (negDist i u v) (hyp i))
  }
  where
  flip : ∀ x y → (- x) - (- y) ≃ - (x - y)
  flip x y = ℝ-Solver.solve 2 (λ a b → (⊝ a) ⊖ (⊝ b) ⊜ ⊝ (a ⊖ b)) ≃-refl x y
    where open ℝ-Solver

  negDist : ∀ {n} (i : Fin n) (u v : Vec ℝ n) →
    ∣ lookup u i - lookup v i ∣ ≃ ∣ lookup (negVec u) i - lookup (negVec v) i ∣
  negDist i u v = ≃-symm (≃-trans
    (∣-∣-cong (≃-trans (+-cong (lookup-negVec u i)
                               (-‿cong (lookup-negVec v i)))
                       (flip (lookup u i) (lookup v i))))
    ∣-x∣≃∣x∣)

------------------------------------------------------------------------
-- Inversion invariance.

torus-reflect : ∀ {n} (f : Vec ℝ n → ℝ) (mf : VecModulus f) →
  VecPeriodic f →
  (mfn : VecModulus (λ v → f (negVec v))) →
  torusIntegral (λ v → f (negVec v)) mfn ≃ torusIntegral f mf
torus-reflect {zero}  f mf per mfn = ≃-refl
torus-reflect {suc n} f mf (perTail , perHead) mfn = ≃-trans step₁ step₂
  where
  G : ℝ → ℝ
  G x = torusIntegral (λ v → f (x ∷ v)) (consMod f mf x)

  mG : UniformModulus G
  mG = headMod f mf

  Gn : ℝ → ℝ
  Gn x = torusIntegral (λ v → f (negVec (x ∷ v)))
                       (consMod (λ v → f (negVec v)) mfn x)

  mGn : UniformModulus Gn
  mGn = headMod (λ v → f (negVec v)) mfn

  Gper : ∀ x → G (x + 1ℝ) ≃ G x
  Gper x = torusIntegral-cong (λ v → f ((x + 1ℝ) ∷ v)) (λ v → f (x ∷ v))
    (consMod f mf (x + 1ℝ)) (consMod f mf x) (λ v → perHead x v)

  inner : ∀ x → Gn x ≃ G (- x)
  inner x = torus-reflect (λ v → f ((- x) ∷ v)) (consMod f mf (- x))
    (perTail (- x)) (consMod (λ v → f (negVec v)) mfn x)

  step₁ : torusIntegral (λ v → f (negVec v)) mfn
            ≃ integral (λ x → G (- x)) (reflectModulus G mG)
  step₁ = uniqueness-of-limits
    (xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀ (λ k → riemannSum-cong Gn (λ x → G (- x)) inner k)
      (riemannSum-isConvergent Gn mGn))
    (riemannSum-converges (λ x → G (- x)) (reflectModulus G mG))

  step₂ : integral (λ x → G (- x)) (reflectModulus G mG) ≃ torusIntegral f mf
  step₂ = integral-reflect G mG Gper

torus-reflect-canonical : ∀ {n} (f : Vec ℝ n → ℝ) (mf : VecModulus f) →
  VecPeriodic f →
  torusIntegral (λ v → f (negVec v)) (negVecModulus f mf)
    ≃ torusIntegral f mf
torus-reflect-canonical f mf per =
  torus-reflect f mf per (negVecModulus f mf)

------------------------------------------------------------------------
-- The negated translate of a coordinatewise periodic function is again
-- coordinatewise periodic, so inversion acts on the space of integrands.

negVecPeriodic : ∀ {n} (f : Vec ℝ n → ℝ) (mf : VecModulus f) →
  VecPeriodic f → VecPeriodic (λ v → f (negVec v))
negVecPeriodic {zero}  f mf per = per
negVecPeriodic {suc n} f mf (perTail , perHead) = tailPer , headPer
  where
  tailPer : ∀ x → VecPeriodic (λ v → f ((- x) ∷ negVec v))
  tailPer x = negVecPeriodic (λ v → f ((- x) ∷ v)) (consMod f mf (- x))
                             (perTail (- x))

  headPer : ∀ x v → f ((- (x + 1ℝ)) ∷ negVec v) ≃ f ((- x) ∷ negVec v)
  headPer x v = ≃-trans
    (≃-symm (perHead (- (x + 1ℝ)) (negVec v)))
    (vec-cong f mf (((- (x + 1ℝ)) + 1ℝ) ∷ negVec v) ((- x) ∷ negVec v) atEach)
    where
    atEach : ∀ i → lookup (((- (x + 1ℝ)) + 1ℝ) ∷ negVec v) i
                     ≃ lookup ((- x) ∷ negVec v) i
    atEach zero    = ℝ-Solver.solve 2
      (λ a b → (⊝ (a ⊕ b)) ⊕ b ⊜ ⊝ a) ≃-refl x 1ℝ
      where open ℝ-Solver
    atEach (suc i) = ≃-refl
