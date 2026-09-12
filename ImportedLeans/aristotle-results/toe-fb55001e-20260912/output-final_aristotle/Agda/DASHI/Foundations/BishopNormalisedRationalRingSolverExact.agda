{-# OPTIONS --without-K --safe #-}

module DASHI.Foundations.BishopNormalisedRationalRingSolverExact where

------------------------------------------------------------------------
-- A RING SOLVER FOR BISHOP REALS WITH *NORMALISED* RATIONAL COEFFICIENTS.
--
-- PRIMARY SOURCE
--
-- Zachary Murray, "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, 2022.  arXiv:2205.08354.
--
-- WHY THIS MODULE EXISTS.
--
-- The vendored constructive-reals library exposes `RealProperties.ℝ-Solver`,
-- a non-reflective ring solver whose coefficient ring is the *unnormalised*
-- rationals `ℚᵘ`.  A call
--
--     solve n (λ … → lhs ⊜ rhs) ≃-refl args
--
-- discharges its side condition with `≃-refl`, which forces the two sides'
-- normal forms to be *definitionally* equal.  With `ℚᵘ` coefficients that is
-- a genuinely fragile requirement: `ℚᵘ` arithmetic never cancels, so a
-- coefficient obtained as, say, `2/1 * 1/6` is the syntactically distinct
-- value `2/6`, and an identity whose two sides fold the same rational out of
-- different products fails to close even though it is true.  This is exactly
-- what blocks the four Taylor-coefficient polynomial identities of
-- `BalabanP33BishopInverseDexpCoefficientExact` (and hence the whole
-- constructive sine/cosine cone above it) under Agda 2.6.4.3 / stdlib 2.1.
--
-- WHAT THIS MODULE DOES.
--
-- It rebuilds the same non-reflective solver over the *normalised* rationals
-- `ℚ`, embedding a coefficient by `p ↦ (toℚᵘ p) ⋆`.  The required ring
-- homomorphism is assembled from the standard library's `toℚᵘ` homomorphism
-- lemmas together with the library's `⋆`-distribution lemmas, so nothing is
-- assumed: `+`, `*` and negation are transported literally.  Because `ℚ`
-- arithmetic *does* reduce to a canonical (coprime, positive-denominator)
-- representative, equal coefficients now have equal representations, and
-- `≃-refl` closes the solver's side condition again.
--
-- No postulate, no hole, no receipt, no pragma beyond the options line.
-- Checked with `agda --safe`.
------------------------------------------------------------------------

open import Data.Bool.Base using (Bool; T)
open import Data.Vec.Base using (Vec)
open import Data.Empty using (⊥-elim)
open import Data.Maybe.Base using (nothing)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ)
import Data.Rational.Properties as ℚP
open import Relation.Nullary.Decidable using (does; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Algebra.Morphism
open import Tactic.RingSolver.Core.AlmostCommutativeRing
  using (AlmostCommutativeRing; fromCommutativeRing; _-Raw-AlmostCommutative⟶_)
open import Tactic.RingSolver.Core.Polynomial.Parameters
  using (RawCoeff; Homomorphism)

import Real as BishopReal
import RealProperties as BishopProperties

------------------------------------------------------------------------
-- 1.  The coefficient embedding
------------------------------------------------------------------------

-- A normalised rational, viewed as a Bishop real.
embedNormalised : ℚ → BishopReal.ℝ
embedNormalised p = (ℚ.toℚᵘ p) BishopReal.⋆

-- Zero detection is decidable *propositional* equality here, because ℚ is
-- canonical; over ℚᵘ the vendored solver has to use the equivalence relation.
isZeroNormalised : ℚ → Bool
isZeroNormalised p = does (p ℚP.≟ 0ℚ)

normalisedCoefficients : RawCoeff _ _
normalisedCoefficients = record
  { rawRing = ℚP.+-*-rawRing
  ; isZero  = isZeroNormalised
  }

realTargetRing : AlmostCommutativeRing _ _
realTargetRing =
  fromCommutativeRing BishopProperties.+-*-commutativeRing (λ _ → nothing)

------------------------------------------------------------------------
-- 2.  The ring morphism ℚ → ℝ
------------------------------------------------------------------------

normalisedMorphism :
  _-Raw-AlmostCommutative⟶_ ℚP.+-*-rawRing realTargetRing
normalisedMorphism = record
  { ⟦_⟧ = embedNormalised
  ; +-homo = λ p q →
      BishopProperties.≃-trans
        (BishopProperties.⋆-cong (ℚP.toℚᵘ-homo-+ p q))
        (BishopProperties.⋆-distrib-+ (ℚ.toℚᵘ p) (ℚ.toℚᵘ q))
  ; *-homo = λ p q →
      BishopProperties.≃-trans
        (BishopProperties.⋆-cong (ℚP.toℚᵘ-homo-* p q))
        (BishopProperties.⋆-distrib-* (ℚ.toℚᵘ p) (ℚ.toℚᵘ q))
  ; -‿homo = λ p →
      BishopProperties.≃-trans
        (BishopProperties.⋆-cong (ℚP.toℚᵘ-homo‿- p))
        (BishopProperties.⋆-distrib-neg (ℚ.toℚᵘ p))
  ; 0-homo = BishopProperties.≃-refl
  ; 1-homo = BishopProperties.≃-refl
  }

normalisedZeroChecker :
  ∀ p → T (isZeroNormalised p) →
  BishopReal._≃_ BishopReal.0ℝ (embedNormalised p)
normalisedZeroChecker p hyp with p ℚP.≟ 0ℚ
... | yes refl = BishopProperties.≃-refl
... | no  _    = ⊥-elim hyp

normalisedHomomorphism : Homomorphism _ _ _ _
normalisedHomomorphism = record
  { from          = normalisedCoefficients
  ; to            = realTargetRing
  ; morphism      = normalisedMorphism
  ; Zero-C⟶Zero-R = normalisedZeroChecker
  }

------------------------------------------------------------------------
-- 3.  The solver
------------------------------------------------------------------------

-- Exports `solve`, `_⊜_`, and the expression syntax `Κ`, `Ι`, `_⊕_`, `_⊗_`,
-- `⊝_`, `_⊛_`, exactly as `RealProperties.ℝ-Solver` does, but with `Κ`
-- taking a *normalised* rational.
open import NonReflective normalisedHomomorphism public
open import Tactic.RingSolver.Core.Expression public

-- The plain (unnormalised) evaluation of an expression tree, re-exported so
-- that callers can state what the solver's conclusion is.
open Eval (AlmostCommutativeRing.rawRing realTargetRing) embedNormalised public
  using (⟦_⟧)

------------------------------------------------------------------------
-- 4.  Discharging the side condition at the level of normal forms
------------------------------------------------------------------------

-- `solve` asks for a proof that the two sides have equivalent *normalised*
-- evaluations.  Passing `≃-refl` makes Agda compare two Bishop reals up to
-- conversion, which for a degree-seven polynomial means unfolding the whole
-- sequence-with-modulus semantics: it is astronomically slower than it needs
-- to be.  The normal forms are pieces of first-order data with normalised
-- rational coefficients, so their equality is a *decidable, cheap*
-- propositional equality, and it implies the required equivalence by
-- congruence.  This lemma performs that reduction once and for all.
open import Tactic.RingSolver.Core.Polynomial.Semantics normalisedHomomorphism
  renaming (⟦_⟧ to ⟦_⟧ₚ)

-- The two expression trees are taken *explicitly*: the conclusion mentions
-- them only under `⟦_⇓⟧`, which is not injective, so leaving them implicit
-- would force the conversion checker to guess them by unfolding the whole
-- real-number semantics.
normalFormSideCondition :
  ∀ {n} (lhs rhs : Expr ℚ n) → norm lhs ≡ norm rhs →
  ∀ (environment : Vec BishopReal.ℝ n) →
  BishopReal._≃_ (⟦ lhs ⇓⟧ environment) (⟦ rhs ⇓⟧ environment)
normalFormSideCondition lhs rhs normalFormsAgree environment =
  BishopProperties.≃-refl₂
    (cong (λ polynomial → ⟦ polynomial ⟧ₚ environment) normalFormsAgree)
