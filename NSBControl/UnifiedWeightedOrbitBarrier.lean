import Mathlib.Tactic

/-!
Unified periodic NS conditional compiler.
All analytic and physical same-object assumptions are explicit.
This does not close the Clay Navier-Stokes problem.
-/

namespace NSBControl
namespace UnifiedWeightedOrbitBarrier

structure Slice where
  initialCritical : ℝ
  terminalCritical : ℝ
  dissipation : ℝ
  margin : ℝ
  integratedWeighted : ℝ
  Qinitial : ℝ
  Qterminal : ℝ
  bound : ℝ
  w2Defect : ℝ
  separatedResidual : ℝ
  comparableTouchedResidual : ℝ
  qQuotient : ℝ
  nestedFourHelicity : ℝ

def augmentedDefect (s : Slice) : ℝ :=
  (s.terminalCritical - 12 * s.Qterminal) -
    (s.initialCritical - 12 * s.Qinitial) +
    s.margin * s.dissipation -
    12 * s.integratedWeighted

/-- Do not silently equate the R742 W2 integrated defect with R781 orbit
    residuals. The second field is an explicit, unproved physical weld. -/
structure PhysicalOrbitWeld (s : Slice) : Prop where
  w2Defect_is_augmented : s.w2Defect = augmentedDefect s
  w2Defect_eq_orbitParts :
    s.w2Defect = s.separatedResidual + s.comparableTouchedResidual
  separated_is_R813 :
    s.separatedResidual = 2 * (9 * s.nestedFourHelicity - s.qQuotient)

def SignedOrbitPayment (s : Slice) : Prop :=
  2 * (9 * s.nestedFourHelicity - s.qQuotient) +
    s.comparableTouchedResidual ≤ 0

theorem orbitPayment_implies_W2
    (s : Slice) (h : PhysicalOrbitWeld s)
    (payment : SignedOrbitPayment s) :
    augmentedDefect s ≤ 0 := by
  dsimp [SignedOrbitPayment] at payment
  rw [← h.w2Defect_is_augmented, h.w2Defect_eq_orbitParts,
    h.separated_is_R813]
  exact payment

theorem weightedOrbitBarrier
    (s : Slice)
    (weld : PhysicalOrbitWeld s)
    (payment : SignedOrbitPayment s)
    (weightedPlusTerminal : s.integratedWeighted + s.Qterminal ≤ s.bound)
    (initialMixedMassNonnegative : 0 ≤ s.Qinitial) :
    s.terminalCritical + s.margin * s.dissipation
      ≤ s.initialCritical + 12 * s.bound := by
  have hw2 := orbitPayment_implies_W2 s weld payment
  unfold augmentedDefect at hw2
  linarith

/-- A single uniform margin floor is additional to a cutoff-wise positive
    margin; do not infer one from positivity alone. -/
theorem uniformMarginBarrier
    (s : Slice)
    (weld : PhysicalOrbitWeld s)
    (payment : SignedOrbitPayment s)
    (weightedPlusTerminal : s.integratedWeighted + s.Qterminal ≤ s.bound)
    (initialMixedMassNonnegative : 0 ≤ s.Qinitial)
    (dissipationNonnegative : 0 ≤ s.dissipation)
    (uniformMargin : ℝ)
    (marginFloor : uniformMargin ≤ s.margin) :
    s.terminalCritical + uniformMargin * s.dissipation
      ≤ s.initialCritical + 12 * s.bound := by
  have h := weightedOrbitBarrier s weld payment
    weightedPlusTerminal initialMixedMassNonnegative
  nlinarith

theorem exactSeparatedCancellation_iff (s : Slice)
    (weld : PhysicalOrbitWeld s) :
    s.separatedResidual = 0 ↔ s.qQuotient = 9 * s.nestedFourHelicity := by
  rw [weld.separated_is_R813]
  constructor <;> intro h <;> linarith

/-- With exact cubic/quintic scaling, universal equality at amplitudes one
    and two forces both terms to vanish. -/
theorem scaleFreeBalanceForcesBothZero
    (q n : ℝ)
    (balanceAtOne : q = 9 * n)
    (balanceAtTwo : (2 : ℝ)^3 * q = 9 * (2 : ℝ)^5 * n) :
    q = 0 ∧ n = 0 := by
  norm_num at balanceAtTwo
  constructor <;> linarith

end UnifiedWeightedOrbitBarrier
end NSBControl
