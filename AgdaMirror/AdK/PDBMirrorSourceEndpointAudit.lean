import Mathlib
import AgdaMirror.AdK.PDBMirrorCVProjection

/-!
# Audit receipt: literal mirror evaluation versus published approximate endpoints

Primary scientific reference:
Li, Liu, Ji 2015, Biophysical Journal 109(3):647–660,
DOI 10.1016/j.bpj.2015.06.059.

The paper states approximate crystal endpoint coordinates:
- 4AKE open: theta1 ~95 deg, theta2 ~61 deg, dLN ~38 A.
- 1AKE closed: theta1 ~68 deg, theta2 ~28 deg, dLN ~20 A.

A direct fixed-column evaluation of the observed YueHuLab/LieRMSD mirror objects,
using the same backbone residue definitions and the adopted Prohaska working
masses, produced the rounded diagnostics recorded below.

These numbers are an **external runtime diagnostic receipt**, not Lean kernel
theorems.  The exact transparent coordinate rows they summarize now live in
`PDBMirrorSelectedFixture` and are projected natively by
`PDBMirrorCVProjection`.

The receipt is deliberately fail-closed:
- published approximate values are not promoted to exact equalities;
- mirror evaluation is not scientific authority;
- the notable 1AKE theta1 mismatch and 4AKE dLN offset remain unresolved
  semantic/evaluator questions rather than being silently normalized away.
-/

namespace AgdaMirror.AdK.PDBMirrorSourceEndpointAudit

abbrev MilliDegree := Nat
abbrev MilliAngstrom := Nat

structure MirrorEndpointDiagnostic where
  pdbLabel : String
  chain : String
  mirrorGitBlobSha : String
  thetaOneMilliDegree : MilliDegree
  thetaTwoMilliDegree : MilliDegree
  dlnBackboneMilliAngstrom : MilliAngstrom
  dlnHeavyMilliAngstrom : MilliAngstrom
  runtimeObserved : Bool
  leanKernelRecomputed : Bool
  scientificAuthorityPromoted : Bool
  deriving DecidableEq, Repr

def fourAKEChainABackboneDiagnostic : MirrorEndpointDiagnostic :=
  { pdbLabel := "4AKE"
    chain := "A"
    mirrorGitBlobSha := "a6990f8befb52ca25ca0b65674e0861f53dd7ee5"
    thetaOneMilliDegree := 94763
    thetaTwoMilliDegree := 61520
    dlnBackboneMilliAngstrom := 36135
    dlnHeavyMilliAngstrom := 35877
    runtimeObserved := true
    leanKernelRecomputed := false
    scientificAuthorityPromoted := false }

def fourAKEChainBBackboneDiagnostic : MirrorEndpointDiagnostic :=
  { pdbLabel := "4AKE"
    chain := "B"
    mirrorGitBlobSha := "a6990f8befb52ca25ca0b65674e0861f53dd7ee5"
    thetaOneMilliDegree := 93103
    thetaTwoMilliDegree := 61068
    dlnBackboneMilliAngstrom := 35886
    dlnHeavyMilliAngstrom := 35676
    runtimeObserved := true
    leanKernelRecomputed := false
    scientificAuthorityPromoted := false }

def oneAKEChainABackboneDiagnostic : MirrorEndpointDiagnostic :=
  { pdbLabel := "1AKE"
    chain := "A"
    mirrorGitBlobSha := "407ebf46f707592958aaa34df06785d7880ca02a"
    thetaOneMilliDegree := 62807
    thetaTwoMilliDegree := 26992
    dlnBackboneMilliAngstrom := 19650
    dlnHeavyMilliAngstrom := 19607
    runtimeObserved := true
    leanKernelRecomputed := false
    scientificAuthorityPromoted := false }

def oneAKEChainBBackboneDiagnostic : MirrorEndpointDiagnostic :=
  { pdbLabel := "1AKE"
    chain := "B"
    mirrorGitBlobSha := "407ebf46f707592958aaa34df06785d7880ca02a"
    thetaOneMilliDegree := 62478
    thetaTwoMilliDegree := 27162
    dlnBackboneMilliAngstrom := 19675
    dlnHeavyMilliAngstrom := 19657
    runtimeObserved := true
    leanKernelRecomputed := false
    scientificAuthorityPromoted := false }

structure PublishedApproximateEndpoint where
  pdbLabel : String
  thetaOneDegree : Nat
  thetaTwoDegree : Nat
  dlnAngstrom : Nat
  sourceDOI : String
  approximate : Bool
  deriving DecidableEq, Repr

def fourAKEPublishedApproximate : PublishedApproximateEndpoint :=
  { pdbLabel := "4AKE"
    thetaOneDegree := 95
    thetaTwoDegree := 61
    dlnAngstrom := 38
    sourceDOI := "10.1016/j.bpj.2015.06.059"
    approximate := true }

def oneAKEPublishedApproximate : PublishedApproximateEndpoint :=
  { pdbLabel := "1AKE"
    thetaOneDegree := 68
    thetaTwoDegree := 28
    dlnAngstrom := 20
    sourceDOI := "10.1016/j.bpj.2015.06.059"
    approximate := true }

def sourceApproximationPromotedToExactEquality : Bool := false
def literalMirrorEvaluatorCreatesScientificAuthority : Bool := false

/-- Literal mirror evaluation gives ~62.8/~62.5 deg for 1AKE theta1 under the
current backbone-COM convention, versus the paper's quoted ~68 deg.  The cause
is not resolved by this receipt. -/
def closedThetaOneSemanticGapResolved : Bool := false

/-- Literal mirror evaluation gives ~36 A for 4AKE dLN under both explicit atom
policies, versus the paper's quoted ~38 A.  The cause is not resolved here. -/
def openDlnSemanticGapResolved : Bool := false

example : oneAKEPublishedApproximate.approximate = true := rfl
example : oneAKEChainABackboneDiagnostic.leanKernelRecomputed = false := rfl
example : fourAKEChainABackboneDiagnostic.scientificAuthorityPromoted = false := rfl

end AgdaMirror.AdK.PDBMirrorSourceEndpointAudit
