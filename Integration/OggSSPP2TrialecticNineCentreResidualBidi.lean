import Mathlib
import Integration.DependentRecoverableProjection
import Integration.OggSSPP2BalancedTernaryPuncturedPlane
import Integration.OggSSPP2TrialecticNineObserverReconciliation

/-!
# p=2 target as PhaseNine + centre-only dependent residual

The shared two-trit observer has nine states.  The ten-state p=2 target differs
from it only by duplicating the centre.  Therefore the exact repair is a
dependent residual:

* at (0,0): two branches;
* at every noncentral phase state: PUnit.

This yields a full two-sided dependent codec of the ten-state target.
-/

namespace Integration.OggSSPP2TrialecticNineCentreResidualBidi

open Integration.DependentRecoverableProjection
open Integration.BalancedTernaryAntipodal369OrbitHierarchy
open Integration.OggSSPP2BalancedTernaryPuncturedPlane
open Integration.OggSSPP2TrialecticNineObserverReconciliation

inductive CentreBranchBit
  | lower
  | upper
  deriving DecidableEq, Repr, Fintype

def CentreResidual : PhaseNine → Type
  | (.zero,.zero) => CentreBranchBit
  | (.neg,.neg) => PUnit
  | (.neg,.zero) => PUnit
  | (.neg,.pos) => PUnit
  | (.zero,.neg) => PUnit
  | (.zero,.pos) => PUnit
  | (.pos,.neg) => PUnit
  | (.pos,.zero) => PUnit
  | (.pos,.pos) => PUnit

def projectToPhaseNine :
    DuplicatedCentreNineSheet → PhaseNine :=
  duplicatedCentreToPhaseNine

def centreResidualOf :
    (s : DuplicatedCentreNineSheet) →
      CentreResidual (projectToPhaseNine s)
  | .lowerCentre => .lower
  | .upperCentre => .upper
  | .puncturedPoint .negativeFirstAxis => PUnit.unit
  | .puncturedPoint .positiveFirstAxis => PUnit.unit
  | .puncturedPoint .negativeSecondAxis => PUnit.unit
  | .puncturedPoint .positiveSecondAxis => PUnit.unit
  | .puncturedPoint .negativeEqualDiagonal => PUnit.unit
  | .puncturedPoint .positiveEqualDiagonal => PUnit.unit
  | .puncturedPoint .negativeOppositeDiagonal => PUnit.unit
  | .puncturedPoint .positiveOppositeDiagonal => PUnit.unit

def reopenPhaseNine :
    (p : PhaseNine) → CentreResidual p → DuplicatedCentreNineSheet
  | (.zero,.zero), .lower => .lowerCentre
  | (.zero,.zero), .upper => .upperCentre
  | (.neg,.neg), _ => .puncturedPoint .negativeEqualDiagonal
  | (.neg,.zero), _ => .puncturedPoint .negativeFirstAxis
  | (.neg,.pos), _ => .puncturedPoint .negativeOppositeDiagonal
  | (.zero,.neg), _ => .puncturedPoint .negativeSecondAxis
  | (.zero,.pos), _ => .puncturedPoint .positiveSecondAxis
  | (.pos,.neg), _ => .puncturedPoint .positiveOppositeDiagonal
  | (.pos,.zero), _ => .puncturedPoint .positiveFirstAxis
  | (.pos,.pos), _ => .puncturedPoint .positiveEqualDiagonal

theorem reopen_phase_nine_exact
    (s : DuplicatedCentreNineSheet) :
    reopenPhaseNine (projectToPhaseNine s) (centreResidualOf s) = s := by
  cases s with
  | lowerCentre => rfl
  | upperCentre => rfl
  | puncturedPoint p => cases p <;> rfl

def centreResidualProjection :
    Projection DuplicatedCentreNineSheet PhaseNine where
  Residual := CentreResidual
  project := projectToPhaseNine
  residual := centreResidualOf
  reopen := reopenPhaseNine
  reopen_exact := reopen_phase_nine_exact

def encode :
    DuplicatedCentreNineSheet → Code centreResidualProjection :=
  Integration.DependentRecoverableProjection.encode centreResidualProjection

def decode :
    Code centreResidualProjection → DuplicatedCentreNineSheet :=
  Integration.DependentRecoverableProjection.decode centreResidualProjection

theorem decode_encode (s : DuplicatedCentreNineSheet) :
    decode (encode s) = s :=
  Integration.DependentRecoverableProjection.decode_encode
    centreResidualProjection s

theorem encode_decode (code : Code centreResidualProjection) :
    encode (decode code) = code := by
  rcases code with ⟨phase,residual⟩
  rcases phase with ⟨a,b⟩
  cases a <;> cases b <;> cases residual <;> rfl

def centreResidualSize : PhaseNine → Nat
  | (.zero,.zero) => 2
  | _ => 1

theorem centre_residual_has_two_branches :
    centreResidualSize (.zero,.zero) = 2 := rfl

theorem noncentral_residuals_are_unit
    (p : PhaseNine) (h : p ≠ (.zero,.zero)) :
    centreResidualSize p = 1 := by
  rcases p with ⟨a,b⟩
  cases a <;> cases b <;> simp_all [centreResidualSize]

theorem fine_state_count_is_ten :
    Fintype.card DuplicatedCentreNineSheet = 10 := by
  decide

theorem centre_branch_count_is_two :
    Fintype.card CentreBranchBit = 2 := by
  decide

structure Boundary where
  sharedPhaseNineSurfaceReused : Bool
  residualOnlyNontrivialAtCentre : Bool
  centreResidualHasTwoBranchesPaid : Bool
  noncentralResidualsAreUnit : Bool
  decodeEncodePaid : Bool
  encodeDecodePaid : Bool
  exactFineStateCountTen : Bool
  globalBinaryResidualRequired : Bool
  arithmeticMeaningClaimed : Bool
  monsterMeaningClaimed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  sharedPhaseNineSurfaceReused := true
  residualOnlyNontrivialAtCentre := true
  centreResidualHasTwoBranchesPaid := true
  noncentralResidualsAreUnit := true
  decodeEncodePaid := true
  encodeDecodePaid := true
  exactFineStateCountTen := true
  globalBinaryResidualRequired := false
  arithmeticMeaningClaimed := false
  monsterMeaningClaimed := false

end Integration.OggSSPP2TrialecticNineCentreResidualBidi
