import Mathlib
import CondensedMatter.MajoranaParityQubitExact

/-!
# Dirac angular-mode scattering -> fermionic even-parity code: loss-source BIDI

This is a new small, exact **algebraic consumer** of the already-merged
`CondensedMatter.MajoranaParityQubitExact` carrier.

Source / attribution:
* two independent fermionic attenuation modes are a STANDARD second-quantized
  channel model (fermionic beam splitter + environmental loss modes);
* existing `CondensedMatter.MajoranaParityQubitExact` proves the
  four-Majorana **even-parity** logical basis |00>,|11>;
* Agda PR #1248 has a **different** two-angular-mode single-particle
  transmission channel, not a physical four-Majorana device;
* the theorem here distinguishes its mean single-particle success from
  success on an even-parity Fock code, and distinguishes a parity-only
  postselection from the strictly stronger **no-environment-loss** herald.

No theorem below asserts a physical Majorana device, a charged-fermion
4D Einstein solution, an actual spin-c spectral lift, a CPTP channel proof
in Lean, or faster-than-light signalling.
-/

namespace MMPQuantumChannel

/-- Real transmission / loss amplitudes of two independent fermionic modes,
with unit-norm one-particle beam-splitter columns. -/
structure IndependentFermionLoss where
  t1 : ℝ
  t2 : ℝ
  s1 : ℝ
  s2 : ℝ
  firstComplete : t1 ^ 2 + s1 ^ 2 = 1
  secondComplete : t2 ^ 2 + s2 ^ 2 = 1

/-- The success fraction for an unpolarized **single-particle mode qubit**.
This is NOT the success fraction for a two-fermion parity-encoded qubit. -/
def singleParticleSuccess (a : IndependentFermionLoss) : ℝ :=
  (a.t1 ^ 2 + a.t2 ^ 2) / 2

/-- The successful **zero-environment-loss** branch on the logical
occupation basis |00>, |11>: diagonal amplitudes (1, t1*t2). -/
def logicalNoLossAmplitude (a : IndependentFermionLoss)
    (logical : CondensedMatter.LogicalQubit) : ℝ :=
  match logical with
  | .logicalZero => 1
  | .logicalOne => a.t1 * a.t2

/-- A **double-loss** event |11> -> |00> produces an EVEN-PARITY
output but environmental excitations, and cannot be counted as no loss. -/
def logicalDoubleLossAmplitude (a : IndependentFermionLoss)
    (logical : CondensedMatter.LogicalQubit) : ℝ :=
  match logical with
  | .logicalZero => 0
  | .logicalOne => a.s1 * a.s2

theorem vacuum_no_loss (a : IndependentFermionLoss) :
    logicalNoLossAmplitude a .logicalZero = 1 := rfl

theorem occupied_no_loss (a : IndependentFermionLoss) :
    logicalNoLossAmplitude a .logicalOne = a.t1 * a.t2 := rfl

theorem vacuum_cannot_double_lose (a : IndependentFermionLoss) :
    logicalDoubleLossAmplitude a .logicalZero = 0 := rfl

theorem occupied_can_double_lose (a : IndependentFermionLoss) :
    logicalDoubleLossAmplitude a .logicalOne = a.s1 * a.s2 := rfl

/-- Mean success of strictly heralding no lost fermions, with maximally mixed
logical inputs on |00>,|11>. -/
def noLossHeraldProbability (a : IndependentFermionLoss) : ℝ :=
  (1 + (a.t1 * a.t2) ^ 2) / 2

/-- Mean success of testing ONLY output even parity (vacuum or both occupied).
It accepts no-loss and indistinguishable-on-output double-loss events. -/
def evenParityAcceptanceProbability (a : IndependentFermionLoss) : ℝ :=
  (1 + (a.t1 * a.t2) ^ 2 + (a.s1 * a.s2) ^ 2) / 2

/-- The exact false-acceptance correction to a parity-only success statistic. -/
theorem evenParity_eq_noLoss_add_doubleLoss (a : IndependentFermionLoss) :
    evenParityAcceptanceProbability a =
      noLossHeraldProbability a + (a.s1 * a.s2) ^ 2 / 2 := by
  unfold evenParityAcceptanceProbability noLossHeraldProbability
  ring

theorem noLoss_le_evenParity (a : IndependentFermionLoss) :
    noLossHeraldProbability a ≤ evenParityAcceptanceProbability a := by
  rw [evenParity_eq_noLoss_add_doubleLoss]
  have hs : 0 ≤ (a.s1 * a.s2) ^ 2 / 2 := by positivity
  linarith

/-- Full source-level probability decomposition for the initially occupied
two-mode Fock state |11>: no loss, two losses, loss of mode 1, loss of mode 2.
The premise comes from the independently normalized beam-splitter amplitudes. -/
theorem occupied_all_outcomes_sum_one (a : IndependentFermionLoss) :
    (a.t1 * a.t2) ^ 2 + (a.s1 * a.s2) ^ 2
      + (a.s1 * a.t2) ^ 2 + (a.t1 * a.s2) ^ 2 = 1 := by
  calc
    (a.t1 * a.t2) ^ 2 + (a.s1 * a.s2) ^ 2
      + (a.s1 * a.t2) ^ 2 + (a.t1 * a.s2) ^ 2
        = (a.t1 ^ 2 + a.s1 ^ 2) * (a.t2 ^ 2 + a.s2 ^ 2) := by ring
    _ = 1 := by rw [a.firstComplete, a.secondComplete]; norm_num

/-- Rewriting the parity acceptance probability using only single-particle
transmission and correlated double-transmission probabilities. -/
theorem evenParity_closed_formula (a : IndependentFermionLoss) :
    evenParityAcceptanceProbability a =
      1 - singleParticleSuccess a + (a.t1 * a.t2) ^ 2 := by
  have h1 : a.s1 ^ 2 = 1 - a.t1 ^ 2 := by
    linarith [a.firstComplete]
  have h2 : a.s2 ^ 2 = 1 - a.t2 ^ 2 := by
    linarith [a.secondComplete]
  unfold evenParityAcceptanceProbability singleParticleSuccess
  rw [show (a.s1 * a.s2) ^ 2 = a.s1 ^ 2 * a.s2 ^ 2 by ring]
  rw [h1, h2]
  ring

/-- Extreme counterexample: both particles are perfectly lost.
A single-particle qubit has zero transmission; output parity is always EVEN,
but strict no-environment-loss heralding succeeds only for input vacuum. -/
def completeLoss : IndependentFermionLoss where
  t1 := 0
  t2 := 0
  s1 := 1
  s2 := 1
  firstComplete := by norm_num
  secondComplete := by norm_num

theorem completeLoss_single_success_zero :
    singleParticleSuccess completeLoss = 0 := by
  norm_num [completeLoss, singleParticleSuccess]

theorem completeLoss_even_parity_always_accepted :
    evenParityAcceptanceProbability completeLoss = 1 := by
  norm_num [completeLoss, evenParityAcceptanceProbability]

theorem completeLoss_noLoss_only_vacuum :
    noLossHeraldProbability completeLoss = 1 / 2 := by
  norm_num [completeLoss, noLossHeraldProbability]

/-- Explicitly state the consumed and not-yet-consumed physical receipts. -/
structure SourceBoundary where
  mergedMajoranaEvenParityBasis : Bool := true
  exactIndependentBeamSplitterLossAccounting : Bool := true
  doubleLossParityFalseAcceptanceExhibited : Bool := true
  physicalFourDimensionalSpinCBundleLift : Bool := false
  actualMMPInOutFockModeAttachment : Bool := false
  globallyRenormalizedFermionState : Bool := false
  secondQuantizedFourDimensionalScattering : Bool := false
  arbitraryInputCPTPKrausFormalization : Bool := false
  realWormholeQuantumTeleportation : Bool := false
  deriving Repr

def canonicalSourceBoundary : SourceBoundary := {}

theorem globalDiracStateNotPaid :
    canonicalSourceBoundary.globallyRenormalizedFermionState = false := rfl

end MMPQuantumChannel
