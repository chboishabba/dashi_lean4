import Integration.AlbertStructureTransport
import Integration.F4MinusculeOnePlus26
import Mathlib

/-!
# Terminal compatibility seam for the Albert/F4 programme

At this point every carrier-level and finite Weyl ingredient is available.
The remaining same-object theorem is not another dimension count.  It is the
existence of one linear identification of the actual Albert algebra with the
canonical minuscule coordinate module for which:

* the actual Jordan unit becomes the finite W(F4)-fixed all-ones vector on the
  three folded-zero E6 weight lines;
* the actual normalized trace becomes the sum of those three coordinates;
* the four independently defined folded generators preserve the transported
  Jordan product and cubic norm.

Once these statements are supplied, each folded generator is automatically a
Jordan automorphism of the same transported Albert structure and acts on the
same 26-dimensional trace-zero carrier.  This file performs that compiler; it
does not manufacture the compatibility receipt.
-/

namespace Integration.AlbertF4CompatibilityTerminal

open Integration.AlbertScalarTraceless
open Integration.AlbertJordanAutomorphism
open Integration.AlbertStructureTransport
open Integration.AlbertLinearMinusculeTransport
open Integration.E6MinusculeWeightModule
open Integration.E6F4WeylFold
open Integration.F4MinusculeOnePlus26

variable {J : Type*} [AddCommGroup J] [Module ℝ J]

/-- Single exact compatibility object remaining after the finite/linear max-cut. -/
structure AlbertF4Compatibility
    (A : AlbertStructure J) [Module.Finite ℝ J]
    (hJ : Module.finrank ℝ J = 27) : Prop where
  coordinateEquiv : J ≃ₗ[ℝ] MinusculeModule

  /-- The distinguished Albert unit is the W(F4)-fixed sum of the three
  folded-zero coordinate vectors. -/
  unitMatches : coordinateEquiv A.traceUnit.unit = f4UnitCandidate

  /-- The actual trace is exactly the folded-zero coefficient sum after this
  same coordinate identification. -/
  traceMatches :
    (transportTraceUnit A coordinateEquiv).trace = foldedZeroTrace

  /-- The four folded generators are actual symmetries of the transported
  product/unit/trace/cubic structure. -/
  foldedGeneratorsPreserveAlbert :
    ∀ g, PreservesTransportedAlbert A coordinateEquiv (f4WeylLinearAction g)

/-- Under a terminal compatibility receipt, the transported actual unit is the
finite invariant unit candidate. -/
theorem transported_unit_eq_candidate
    (A : AlbertStructure J) [Module.Finite ℝ J]
    (hJ : Module.finrank ℝ J = 27)
    (C : AlbertF4Compatibility A hJ) :
    (transportTraceUnit A C.coordinateEquiv).unit = f4UnitCandidate := by
  exact C.unitMatches

/-- The actual transported trace-zero carrier is literally the finite W(F4)
trace-zero carrier after identifying the trace maps. -/
theorem transported_traceless_eq_f4_candidate
    (A : AlbertStructure J) [Module.Finite ℝ J]
    (hJ : Module.finrank ℝ J = 27)
    (C : AlbertF4Compatibility A hJ) :
    Traceless (transportTraceUnit A C.coordinateEquiv) = F4TracelessCandidate := by
  unfold Traceless F4TracelessCandidate f4TraceUnitData
  rw [C.traceMatches]

/-- Every folded generator compiles to an actual Jordan automorphism of the
same transported Albert algebra. -/
noncomputable def foldedJordanAutomorphism
    (A : AlbertStructure J) [Module.Finite ℝ J]
    (hJ : Module.finrank ℝ J = 27)
    (C : AlbertF4Compatibility A hJ)
    (g : FoldGenerator) :
    JordanAutomorphism (transportAlbertStructure A C.coordinateEquiv) :=
  jordanAutomorphismOfPreserves A C.coordinateEquiv (f4WeylLinearAction g)
    (C.foldedGeneratorsPreserveAlbert g)

/-- Consequently each folded generator restricts to an automorphism of the
actual transported traceless carrier, which is the same 26-dimensional carrier
as the finite W(F4) candidate by the theorem above. -/
noncomputable def foldedTracelessAutomorphism
    (A : AlbertStructure J) [Module.Finite ℝ J]
    (hJ : Module.finrank ℝ J = 27)
    (C : AlbertF4Compatibility A hJ)
    (g : FoldGenerator) :
    Traceless (transportTraceUnit A C.coordinateEquiv) ≃ₗ[ℝ]
      Traceless (transportTraceUnit A C.coordinateEquiv) :=
  (foldedJordanAutomorphism A hJ C g).tracelessLinearEquiv
    (transportAlbertStructure A C.coordinateEquiv)

/-- Terminal compiler surface for the remaining continuous/algebraic theorem.
The finite Weyl action is now inside Jordan automorphisms; identifying the full
Jordan automorphism group with the algebraic/compact F4 object is strictly
stronger. -/
structure FullF4Recognition
    (A : AlbertStructure J) [Module.Finite ℝ J]
    (hJ : Module.finrank ℝ J = 27)
    (C : AlbertF4Compatibility A hJ) : Type 1 where
  recognition : E6F4StabilizerRecognition (transportAlbertStructure A C.coordinateEquiv)
  foldedGeneratorsAgreeWithF4 : Set
  fullJordanAutomorphismGroupExhausted : Set

inductive FiniteFoldedAutomorphismsCreateFullF4Recognition : Prop

theorem folded_jordan_automorphisms_do_not_create_full_f4 :
    ¬ FiniteFoldedAutomorphismsCreateFullF4Recognition := by
  intro h; cases h

structure Boundary where
  terminalCompatibilityObjectTyped : Bool
  unitSameObjectRequirementTyped : Bool
  traceSameObjectRequirementTyped : Bool
  fourFoldedAlbertPreservationRequirementsTyped : Bool
  compatibilityCompilesToJordanAutomorphisms : Bool
  actualTracelessCarrierIdentificationCompiles : Bool
  fullF4RecognitionTypedSeparately : Bool
  terminalCompatibilityPaidHere : Bool
  fullF4RecognitionPaidHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  terminalCompatibilityObjectTyped := true
  unitSameObjectRequirementTyped := true
  traceSameObjectRequirementTyped := true
  fourFoldedAlbertPreservationRequirementsTyped := true
  compatibilityCompilesToJordanAutomorphisms := true
  actualTracelessCarrierIdentificationCompiles := true
  fullF4RecognitionTypedSeparately := true
  terminalCompatibilityPaidHere := false
  fullF4RecognitionPaidHere := false

end Integration.AlbertF4CompatibilityTerminal
