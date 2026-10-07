import Integration.AlbertF4CompatibilityTerminal
import Integration.AlbertCubicRigidity
import Integration.AlbertTrialityCubicCompiler
import Integration.F4D4TrialityAlbertShape
import Integration.F4FiniteInvariantNonuniqueness
import Mathlib

/-!
# Reduced Albert/F4 terminal

The existing terminal asks each of the four folded generators to preserve the
entire transported Albert structure.  Two parts of that obligation are already
paid by the finite fold once the same coordinate identification matches the
actual unit and trace:

* every folded generator fixes `f4UnitCandidate`;
* every folded generator preserves `foldedZeroTrace`.

For a rank-three Albert algebra satisfying the classical cubic-rigidity theorem,
product preservation then follows from preservation of unit, trace and cubic.
Thus the terminal can be reduced to:

1. same-object unit identification;
2. same-object trace identification;
3. one global cubic-rigidity theorem;
4. cubic preservation for the four folded generators.

The D4/triality compiler separately reduces those cubic checks to octonion norm
and triality-form compatibility.  Finite W(F4) invariance alone cannot choose
the cubic: the exact character averages give 7 quadratic and 23 cubic invariant
dimensions on the 26-dimensional finite shadow.
-/

namespace Integration.AlbertF4ReducedTerminal

open Integration.AlbertScalarTraceless
open Integration.AlbertJordanAutomorphism
open Integration.AlbertStructureTransport
open Integration.AlbertCubicRigidity
open Integration.E6F4WeylFold
open Integration.F4MinusculeOnePlus26
open Integration.AlbertF4CompatibilityTerminal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]

/-- Strictly smaller compatibility object than `AlbertF4Compatibility`: product
preservation is derived globally from cubic rigidity rather than reproved for
four generators. -/
structure ReducedAlbertF4Compatibility
    (A : AlbertStructure J) [Module.Finite ℝ J]
    (hJ : Module.finrank ℝ J = 27) : Prop where
  coordinateEquiv : J ≃ₗ[ℝ] Integration.E6MinusculeWeightModule.MinusculeModule
  unitMatches :
    coordinateEquiv A.traceUnit.unit = f4UnitCandidate
  traceMatches :
    (transportTraceUnit A coordinateEquiv).trace = foldedZeroTrace
  cubicRigidity :
    CubicRigidity (transportAlbertStructure A coordinateEquiv)
  foldedGeneratorsPreserveCubic :
    ∀ g x,
      (transportAlbertStructure A coordinateEquiv).cubic
          (f4WeylLinearAction g x) =
        (transportAlbertStructure A coordinateEquiv).cubic x

private theorem reduced_unit_preserved
    (A : AlbertStructure J) [Module.Finite ℝ J]
    (hJ : Module.finrank ℝ J = 27)
    (C : ReducedAlbertF4Compatibility A hJ)
    (g : FoldGenerator) :
    f4WeylLinearAction g (transportTraceUnit A C.coordinateEquiv).unit =
      (transportTraceUnit A C.coordinateEquiv).unit := by
  rw [show (transportTraceUnit A C.coordinateEquiv).unit = f4UnitCandidate from C.unitMatches]
  exact folded_action_fixes_unit g

private theorem reduced_trace_preserved
    (A : AlbertStructure J) [Module.Finite ℝ J]
    (hJ : Module.finrank ℝ J = 27)
    (C : ReducedAlbertF4Compatibility A hJ)
    (g : FoldGenerator) :
    ∀ x,
      (transportTraceUnit A C.coordinateEquiv).trace (f4WeylLinearAction g x) =
        (transportTraceUnit A C.coordinateEquiv).trace x := by
  intro x
  rw [C.traceMatches]
  exact folded_action_preserves_trace g x

/-- Reduced compatibility compiles to the old full terminal. -/
noncomputable def toFullCompatibility
    (A : AlbertStructure J) [Module.Finite ℝ J]
    (hJ : Module.finrank ℝ J = 27)
    (C : ReducedAlbertF4Compatibility A hJ) :
    AlbertF4Compatibility A hJ where
  coordinateEquiv := C.coordinateEquiv
  unitMatches := C.unitMatches
  traceMatches := C.traceMatches
  foldedGeneratorsPreserveAlbert := by
    intro g
    let B := transportAlbertStructure A C.coordinateEquiv
    have hunit := reduced_unit_preserved A hJ C g
    have htrace := reduced_trace_preserved A hJ C g
    have hcubic := C.foldedGeneratorsPreserveCubic g
    refine ⟨hunit, ?_, htrace, hcubic⟩
    exact C.cubicRigidity.product_recovered
      (f4WeylLinearAction g) hunit htrace hcubic

/-- Therefore the reduced terminal already compiles each folded generator to a
Jordan automorphism. -/
noncomputable def foldedJordanAutomorphismOfReduced
    (A : AlbertStructure J) [Module.Finite ℝ J]
    (hJ : Module.finrank ℝ J = 27)
    (C : ReducedAlbertF4Compatibility A hJ)
    (g : FoldGenerator) :
    JordanAutomorphism (transportAlbertStructure A C.coordinateEquiv) :=
  foldedJordanAutomorphism A hJ (toFullCompatibility A hJ C) g

structure Boundary where
  unitPreservationReducedToPaidFiniteTheorem : Bool
  tracePreservationReducedToPaidFiniteTheorem : Bool
  productPreservationReducedToCubicRigidity : Bool
  fourGeneratorTerminalReducedToCubicChecks : Bool
  octonionTrialityCompilerAvailable : Bool
  finiteWeylInvarianceUniquenessRefuted : Bool
  actualCubicRigidityPaidHere : Bool
  actualFourCubicChecksPaidHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  unitPreservationReducedToPaidFiniteTheorem := true
  tracePreservationReducedToPaidFiniteTheorem := true
  productPreservationReducedToCubicRigidity := true
  fourGeneratorTerminalReducedToCubicChecks := true
  octonionTrialityCompilerAvailable := true
  finiteWeylInvarianceUniquenessRefuted := true
  actualCubicRigidityPaidHere := false
  actualFourCubicChecksPaidHere := false

end Integration.AlbertF4ReducedTerminal
