import Mathlib
import Integration.OggSSPP2BanerjeeF4ZetaCoordinates
import Integration.OggSSPP2F4ActualPairingNormalization

/-!
# Concrete cubic phases attached to the actual E(F4) Heisenberg form

The normalized alternating form in
OggSSPP2F4ActualPairingNormalization is ZMod 3 valued.
This module realizes its phases in the ACTUAL F4 coefficient field:

  0 |-> 1,  1 |-> zeta,  -1 |-> zeta^2.

This construction is NOT the intrinsic geometric Weil pairing e3.
In particular, phase normalization does not evaluate an independently
defined Weil pairing at the geometric points P,Q.

Likewise the multiplicative cube roots here live in characteristic two;
they are NOT the complex cyclotomic phases of the VOA action. Comparing
their abstract cyclic groups requires a separate phase-group isomorphism,
not a characteristic-zero/characteristic-two field embedding.

Source orientation: the choice of zeta agrees with the concrete F4 root
selected in OggSSPP2BanerjeeF4ZetaCoordinates.
-/

namespace Integration.OggSSPP2F4ConcreteCubicPhase

namespace B := Integration.OggSSPP2BanerjeeF4UniversalDeformationSource
namespace Z := Integration.OggSSPP2BanerjeeF4ZetaCoordinates
namespace P := Integration.OggSSPP2F4ActualPairingNormalization
namespace E := Integration.OggSSPP2F4ActualEllipticGroup
namespace G := Integration.OggSSPP2F4ActualGroupGenerators
namespace A := Integration.OggSSPP2F4ActualGroupShearReflection

/-- The concrete cube root phase chosen on the actual field F4. -/
def phase (a : ZMod 3) : B.F4 :=
  if a = 0 then 1 else if a = 1 then Z.zeta else Z.zeta ^ 2

@[simp] theorem phase_zero : phase 0 = 1 := by
  simp [phase]

@[simp] theorem phase_one : phase 1 = Z.zeta := by
  simp [phase]

theorem phase_neg_one : phase (-1) = Z.zeta ^ 2 := by
  have hzero : (-1 : ZMod 3) ≠ 0 := by decide
  have hone : (-1 : ZMod 3) ≠ 1 := by decide
  simp [phase, hzero, hone]

/-- Every phase belongs to the actual multiplicative cubic root group. -/
theorem phase_cube (a : ZMod 3) : phase a ^ 3 = 1 := by
  fin_cases a
  · simp [phase]
  · simp [phase, Z.zeta_cube_is_one]
  · rw [show (2 : ZMod 3) = -1 from by decide, phase_neg_one]
    calc
      (Z.zeta ^ 2) ^ 3 = (Z.zeta ^ 3) ^ 2 := by ring
      _ = 1 := by rw [Z.zeta_cube_is_one]; ring

/-- Arithmetic Frobenius on the concrete cube roots agrees with phase inversion. -/
theorem phase_neg_frobenius (a : ZMod 3) :
    phase (-a) = (phase a) ^ 2 := by
  fin_cases a
  · simp [phase]
  · change phase (-1) = (phase 1) ^ 2
    rw [phase_neg_one, phase_one]
  · have hminus : -(2 : ZMod 3) = 1 := by decide
    rw [hminus, phase_one]
    change Z.zeta = (phase 2) ^ 2
    rw [show (2 : ZMod 3) = -1 from by decide, phase_neg_one]
    calc
      Z.zeta = Z.zeta ^ 4 := Z.zeta_fourth_is_zeta.symm
      _ = (Z.zeta ^ 2) ^ 2 := by ring

/-- Transport of the normalized reflection to field Frobenius on F4 phases. -/
theorem phase_frobenius (a : ZMod 3) :
    (phase a) ^ 2 = phase (-a) :=
  (phase_neg_frobenius a).symm

/-- The normalized alternating form gives a concrete F4-valued phase. -/
noncomputable def ellipticPhase (p q : E.ActualCurveGroup) : B.F4 :=
  phase (P.ellipticOmega p q)

theorem elliptic_phase_P_Q :
    ellipticPhase G.P G.Q = Z.zeta := by
  rw [ellipticPhase, P.ellipticOmega_P_Q, phase_one]

theorem elliptic_phase_Q_P :
    ellipticPhase G.Q G.P = Z.zeta ^ 2 := by
  rw [ellipticPhase, P.ellipticOmega_Q_P, phase_neg_one]

theorem elliptic_phase_alternating (p : E.ActualCurveGroup) :
    ellipticPhase p p = 1 := by
  simp [ellipticPhase, P.ellipticOmega_alternating]

theorem elliptic_phase_cubic (p q : E.ActualCurveGroup) :
    ellipticPhase p q ^ 3 = 1 :=
  phase_cube _

/-- Shear preserves the actual F4-valued normalized commutator phase. -/
theorem elliptic_phase_shear
    (p q : E.ActualCurveGroup) :
    ellipticPhase (A.actualShearModel p) (A.actualShearModel q) =
      ellipticPhase p q := by
  simp only [ellipticPhase, P.ellipticOmega_shearModel]

/--
At the normalized level, the Frobenius-model reflection negates the
ZMod 3 phase. The equality with FIELD Frobenius on concrete cubic roots
is an independent orientation check, not an intrinsic e3 construction.
-/
theorem elliptic_phase_frobenius_reflection
    (p q : E.ActualCurveGroup) :
    ellipticPhase (A.actualFrobeniusModel p)
      (A.actualFrobeniusModel q) =
      phase (-P.ellipticOmega p q) := by
  rw [ellipticPhase, P.ellipticOmega_frobeniusModel]

/--
The transported elliptic-group reflection is the actual coefficient-field
Frobenius on the normalized F4-valued phase.  This is NOT yet an equation
for an independently constructed intrinsic Weil pairing.
-/
theorem elliptic_phase_reflection_is_field_frobenius
    (p q : E.ActualCurveGroup) :
    ellipticPhase (A.actualFrobeniusModel p)
      (A.actualFrobeniusModel q) =
      (ellipticPhase p q) ^ 2 := by
  rw [elliptic_phase_frobenius_reflection]
  exact phase_neg_frobenius _

structure Boundary where
  concreteF4CubicRootPhaseSelected : Bool
  P_QPhaseIsConcreteZeta : Bool
  Q_PPhaseIsConcreteZetaSquared : Bool
  alternatingAndCubicRootProperties : Bool
  transportedShearPhasePreservation : Bool
  transportedFrobeniusPhaseSign : Bool
  fieldFrobeniusMatchesPhaseInversion : Bool
  complexCyclotomicFieldIdentifiedWithF4 : Bool
  intrinsicGeometricWeilPairingConstructed : Bool
  intrinsicWeilValueAtP_QComputed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  concreteF4CubicRootPhaseSelected := true
  P_QPhaseIsConcreteZeta := true
  Q_PPhaseIsConcreteZetaSquared := true
  alternatingAndCubicRootProperties := true
  transportedShearPhasePreservation := true
  transportedFrobeniusPhaseSign := true
  fieldFrobeniusMatchesPhaseInversion := true
  complexCyclotomicFieldIdentifiedWithF4 := false
  intrinsicGeometricWeilPairingConstructed := false
  intrinsicWeilValueAtP_QComputed := false

end Integration.OggSSPP2F4ConcreteCubicPhase
