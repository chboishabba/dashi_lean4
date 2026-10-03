import Synthesis.MillenniumHodgeRelativeRulingEmbeddingsExact
import Synthesis.MillenniumHodgeCycleIsoPushforwardExact
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Fin.Basic

/-!
# Hodge max-cut: the actual P¹_Q scheme as Proj

This file fixes the scheme object used by the ruling-swap regression.  It is
not a synthetic projective line: it is Mathlib's literal `Proj` construction
applied to the ordinary total-degree grading on the two-variable polynomial
ring Q[X₀,X₁].

The first structure morphism is the canonical `Proj.toSpecZero`.  Its target is
the degree-zero ring of the grading; the next small plumbing theorem identifies
that ring with Q and composes the map with the corresponding `Spec` isomorphism.
After that, a rational section such as [1:0] can be constructed and fed directly
into `relativeRulingOne` / `relativeRulingTwo`.
-/

namespace Synthesis.Millennium.Hodge

open AlgebraicGeometry
open CategoryTheory

/-- Homogeneous coordinate ring of P¹_Q. -/
abbrev P1QCoordinateRing := MvPolynomial (Fin 2) ℚ

/-- Ordinary total-degree grading on Q[X₀,X₁]. -/
abbrev P1QGrading : ℕ → Submodule ℚ P1QCoordinateRing :=
  MvPolynomial.homogeneousSubmodule (Fin 2) ℚ

/-- Actual projective line over Q in the scheme category. -/
noncomputable abbrev P1QScheme : Scheme :=
  Proj P1QGrading

/-- Canonical structure morphism to the degree-zero base ring. -/
noncomputable def p1QToGradeZeroSpec :
    P1QScheme ⟶ Spec ↧(P1QGrading 0) :=
  Proj.toSpecZero P1QGrading

/-- The degree-zero homogeneous piece is literally the scalar submodule.  This
records the exact library theorem that reduces the remaining base-ring
identification to the standard constants ≃ Q equivalence. -/
theorem p1Q_gradeZero_eq_scalars :
    P1QGrading 0 = (1 : Submodule ℚ P1QCoordinateRing) := by
  exact MvPolynomial.homogeneousSubmodule_zero

/-- The actual self-product used by the ruling regression, already equipped
with Mathlib's genuine factor-swap isomorphism. -/
noncomputable abbrev P1QSelfProduct : Scheme :=
  Limits.pullback p1QToGradeZeroSpec p1QToGradeZeroSpec

noncomputable def p1QFactorSwap :
    P1QSelfProduct ≅ P1QSelfProduct :=
  relativeProductSwap p1QToGradeZeroSpec

@[simp, reassoc] theorem p1QFactorSwap_fst :
    p1QFactorSwap.hom ≫ Limits.pullback.fst
        p1QToGradeZeroSpec p1QToGradeZeroSpec =
      Limits.pullback.snd p1QToGradeZeroSpec p1QToGradeZeroSpec :=
  relativeProductSwap_fst p1QToGradeZeroSpec

@[simp, reassoc] theorem p1QFactorSwap_snd :
    p1QFactorSwap.hom ≫ Limits.pullback.snd
        p1QToGradeZeroSpec p1QToGradeZeroSpec =
      Limits.pullback.fst p1QToGradeZeroSpec p1QToGradeZeroSpec :=
  relativeProductSwap_snd p1QToGradeZeroSpec

/-!
MAX-CUT STATUS

PAID HERE (subject to exact-head kernel certification):
* the selected Hodge regression object is now a literal scheme-level Proj of
  Q[X₀,X₁] with its ordinary grading;
* the canonical projective structure morphism exists on that exact object;
* the actual relative self-product and factor-swap isomorphism are instantiated;
* the degree-zero/base-field seam is reduced to constants ≃ Q.

NEXT:
* package the ring equivalence `(P1QGrading 0) ≃+* Q` and obtain the displayed
  structure morphism P¹_Q -> Spec Q;
* construct an actual rational section [1:0] (preferably via
  `Proj.fromOfGlobalSections`);
* instantiate the two generic ruling embeddings and their genuine cycle
  pushforwards;
* use `actualCyclePushforward_iso_apply` to derive the swap eigencycle;
* then pay cycle-class/cohomology compatibility and leave the P¹ regression.
-/

end Synthesis.Millennium.Hodge
