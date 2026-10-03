import Synthesis.MillenniumHodgeP1QGeometryInstancesExact
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Topology.Irreducible

/-!
# Hodge max-cut: irreducibility of the literal Proj P¹_Q

No comparison with a separately-defined projective-space object is needed.
The underlying points of the selected `Proj` are relevant homogeneous prime
ideals.  Since `Q[X₀,X₁]` is a domain, the zero homogeneous ideal is prime.
It is relevant because the degree-one variable `X₀` lies in the irrelevant
ideal but is nonzero.  Hence the zero ideal defines a literal Proj point η.

The specialization order on `ProjectiveSpectrum` is ideal inclusion, so η is
below every point.  Equivalently every point lies in `closure {η}`.  Thus the
singleton η is dense and the selected literal Proj is irreducible.
-/

namespace Synthesis.Millennium.Hodge

open AlgebraicGeometry
open ProjectiveSpectrum
open MvPolynomial
open Set Topology

noncomputable section

/-- The homogeneous zero prime, viewed as an actual point of the selected
projective spectrum. -/
noncomputable def p1QZeroPrimePoint : ProjectiveSpectrum P1QGrading where
  asHomogeneousIdeal := ⊥
  isPrime := by
    change (⊥ : Ideal P1QCoordinateRing).IsPrime
    exact Ideal.isPrime_bot
  not_irrelevant_le := by
    intro hle
    have hxHom :
        (X (0 : Fin 2) : P1QCoordinateRing) ∈ P1QGrading 1 := by
      exact (MvPolynomial.mem_homogeneousSubmodule 1 _).2
        (MvPolynomial.isHomogeneous_X ℚ (0 : Fin 2))
    have hxIrr :
        (X (0 : Fin 2) : P1QCoordinateRing) ∈
          HomogeneousIdeal.irrelevant P1QGrading :=
      HomogeneousIdeal.mem_irrelevant_of_mem P1QGrading (by norm_num) hxHom
    have hxBot :
        (X (0 : Fin 2) : P1QCoordinateRing) ∈
          (⊥ : HomogeneousIdeal P1QGrading) :=
      hle hxIrr
    simpa using hxBot

/-- The zero-prime point specializes to every point of the selected Proj. -/
theorem p1QZeroPrimePoint_le_all
    (x : ProjectiveSpectrum P1QGrading) :
    p1QZeroPrimePoint ≤ x := by
  change (⊥ : HomogeneousIdeal P1QGrading) ≤ x.asHomogeneousIdeal
  exact bot_le

/-- Consequently its singleton is dense in the literal projective spectrum. -/
theorem p1QZeroPrimePoint_closure :
    closure ({p1QZeroPrimePoint} : Set (ProjectiveSpectrum P1QGrading)) =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact (ProjectiveSpectrum.le_iff_mem_closure p1QZeroPrimePoint x).mp
    (p1QZeroPrimePoint_le_all x)

/-- The exact selected `Proj Q[X₀,X₁]` is irreducible. -/
noncomputable instance p1QScheme_irreducibleSpace :
    IrreducibleSpace P1QScheme := by
  refine
    { toNonempty := ⟨p1QZeroPrimePoint⟩
    , isPreirreducible_univ := ?_ }
  rw [← p1QZeroPrimePoint_closure]
  exact IsPreirreducible.closure isPreirreducible_singleton

/-- With all standard geometry instances discharged, the genuine ruling-cycle
exchange theorem is now available without local hypotheses. -/
theorem p1QRulingCycleOne_swap_paid :
    actualCyclePushforward p1QFactorSwapOverQ.hom p1QRulingCycleOne =
      p1QRulingCycleTwo :=
  p1QRulingCycleOne_swap

/-- Converse exchange. -/
theorem p1QRulingCycleTwo_swap_paid :
    actualCyclePushforward p1QFactorSwapOverQ.hom p1QRulingCycleTwo =
      p1QRulingCycleOne :=
  p1QRulingCycleTwo_swap

/-- Complete genuine cycle-side regression on the actual selected
`P¹_Q × P¹_Q`. -/
theorem p1QRulingDifference_antiInvariant_paid :
    actualCyclePushforward p1QFactorSwapOverQ.hom
        (p1QRulingCycleOne - p1QRulingCycleTwo) =
      -(p1QRulingCycleOne - p1QRulingCycleTwo) :=
  p1QRulingDifference_antiInvariant

/-!
MAX-CUT STATUS

SUBJECT TO EXACT-HEAD LEAN CERTIFICATION, THE ENTIRE SELECTED CYCLE-SIDE
REGRESSION IS CLOSED ON GENUINE MATHLIB OBJECTS:

* literal `Proj Q[X₀,X₁]` is irreducible;
* both real ruling embeddings are quasi-compact closed immersions;
* `D₁=(i₁)_*[P¹]` and `D₂=(i₂)_*[P¹]` are actual `AlgebraicCycle`s;
* factor swap exchanges them;
* `D₁-D₂` is an actual (-1)-eigencycle.

The next boundary is not more cycle plumbing: it is a genuine cycle-class map
and proper-pushforward naturality in a real cohomology theory.
-/

end

end Synthesis.Millennium.Hodge
