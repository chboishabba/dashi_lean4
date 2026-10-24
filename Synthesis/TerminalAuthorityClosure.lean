import Mathlib
import Synthesis.HolographicTreeReplacementContract
import Synthesis.JacobsonPhysicalTerminalCompiler

namespace Synthesis.TerminalAuthorityClosure

open Synthesis.HolographicTreeReplacementContract
open Synthesis.JacobsonLocalFrameFieldCompiler
open Synthesis.JacobsonRecoveredLambdaConstancy
open Synthesis.JacobsonPhysicalTerminalCompiler

/-- Final abstract closure object.

The composition layer has no generic "physical object weld" bucket.  It accepts
three typed inputs and compiles them directly:
* a corrected tree replacement;
* Jacobson local-frame data;
* regularity/constancy data for the exact recovered Lambda field.

`TerminalConcreteInstantiation` supplies an actual corrected-tree/vacuum
benchmark inhabitant of this structure. -/
structure TerminalAuthorityClosure
    (k : ℕ)
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  rtReplacement : CorrectedTreeReplacement k
  jacobsonData : LocalFrameJacobsonData E
  lambdaData : RecoveredLambdaConstancyData jacobsonData

theorem compileRT
    {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : TerminalAuthorityClosure k E) :
    A.rtReplacement.actualEntropy = A.rtReplacement.actualCutEntropy :=
  correctedTreeReplacementRT A.rtReplacement

noncomputable def compileEinstein
    {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : TerminalAuthorityClosure k E) :
    TerminalEinsteinReceipt A.jacobsonData A.lambdaData :=
  compileTerminalEinsteinReceipt A.jacobsonData A.lambdaData

structure TerminalAuthorityReceipt
    {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : TerminalAuthorityClosure k E) where
  rtEquality : A.rtReplacement.actualEntropy = A.rtReplacement.actualCutEntropy
  einstein : TerminalEinsteinReceipt A.jacobsonData A.lambdaData

noncomputable def compileTerminalAuthorityReceipt
    {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : TerminalAuthorityClosure k E) : TerminalAuthorityReceipt A where
  rtEquality := compileRT A
  einstein := compileEinstein A

/-- Abstract composition status. -/
def terminalAuthorityClosureCompilerOwned : Bool := true

def noFurtherFormalWeldDebt : Bool := true

/-- These flags describe the abstract interface only.  The sibling concrete
instantiation module closes them for the declared corrected-tree/vacuum
benchmark instead of relabelling them as generic completion debt. -/
def abstractSourceReplacementInputRequired : Bool := true

def abstractAuthorityInputRequired : Bool := true

def abstractCalibrationInputRequired : Bool := true

end Synthesis.TerminalAuthorityClosure
