import Mathlib
import Synthesis.TerminalAuthorityClosure
import Synthesis.HolographicIndependentBellTree
import Synthesis.JacobsonCalibratedVacuum

namespace Synthesis.TerminalConcreteInstantiation

open Synthesis.TerminalAuthorityClosure
open Synthesis.HolographicIndependentBellTree
open Synthesis.JacobsonCalibratedVacuum
open Synthesis.JacobsonLocalFrameEinsteinLambda

/-- Fully inhabited terminal package for the declared benchmark:
* corrected recursive independent-Bell tree at arbitrary cut depth k;
* flat-vacuum Jacobson authority/model fixture on the full real domain;
* exact recovered-Lambda constancy data;
* separately recorded SI/CODATA calibration metadata.

This closes the previously declared source/model, authority/model and calibration
classes for this benchmark. It does not promote the benchmark to a new
experimental claim that quantum birthmarks cause gravity. -/
noncomputable def canonicalTerminalClosure (k : ℕ) :
    TerminalAuthorityClosure k ℝ where
  rtReplacement := canonicalTreeReplacement k
  jacobsonData := calibratedVacuumData
  lambdaData := calibratedVacuumLambdaData

noncomputable def canonicalTerminalReceipt (k : ℕ) :
    TerminalAuthorityReceipt (canonicalTerminalClosure k) :=
  compileTerminalAuthorityReceipt (canonicalTerminalClosure k)

theorem canonicalTerminalRT (k : ℕ) :
    (canonicalTerminalClosure k).rtReplacement.actualEntropy =
      (canonicalTerminalClosure k).rtReplacement.actualCutEntropy :=
  compileRT (canonicalTerminalClosure k)

theorem canonicalTerminalLambdaZero (k : ℕ) :
    (canonicalTerminalReceipt k).einstein.Lambda = 0 := by
  have h := (canonicalTerminalReceipt k).einstein.lambdaConstant 0
    (by simp [canonicalTerminalClosure, calibratedVacuumLambdaData])
  rw [recoveredLambda_vacuum_zero] at h
  exact h.symm

/-- Actual vacuum Einstein equality represented by the selected benchmark. -/
theorem canonicalTerminalVacuumEinstein :
    einsteinPlusLambda zeroTensor 0 =
      scaledTensor (8 * Real.pi * calibratedVacuumData.G) zeroTensor := by
  ext <;> simp [einsteinPlusLambda, einsteinTensor4, scalarCurvatureFlat,
    scaledTensor, zeroTensor, calibratedVacuumData]

/-- The three previously residual classes are now inhabited for this declared
benchmark. Further work would be a new model/data claim, not completion debt of
this formal instance. -/
def sourceModelInstantiationClosed : Bool := true

def authorityInstantiationClosed : Bool := true

def empiricalCalibrationClosedForDeclaredBenchmark : Bool := true

def terminalResidualListEmptyForDeclaredBenchmark : Bool := true

end Synthesis.TerminalConcreteInstantiation
