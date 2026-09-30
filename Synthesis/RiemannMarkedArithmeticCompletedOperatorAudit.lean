import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleBidiMarkedFourth
import Synthesis.RiemannQuarticSignedCosinePSDNoGo

/-!
# Same-witness marked Guinand–Weil source, and completion firewall

The *actual* primeProjectiveDefect of both short marked physical
detectors vanishes for t >= 200. A positive separately-defined
prime-angular jet cannot be substituted for their arithmetic source.

The literal Zeta23 cluster/off-ordinate/Gamma/pole decomposition,
together with the exact prime vanishing, is the completed source
identity for this marked test. It is not the canonical unmarked
signed fifth-RvM terminal inequality.
-/
noncomputable section
namespace Synthesis

def QuarticFourSignedPolePair.markedCompletedArithmeticResponse
    {t : ℝ} (W : QuarticFourSignedPolePair t) (A : ℝ) : ℝ :=
  W.bidiMarkedPrimeCombination A
    + W.bidiMarkedGammaCombination A
    + W.bidiMarkedPoleCombination A

theorem QuarticFourSignedPolePair.markedArithmetic_eq_gamma_add_pole
    {t A : ℝ} (ht : 200 ≤ t)
    (W : QuarticFourSignedPolePair t) :
    W.markedCompletedArithmeticResponse A
      = W.bidiMarkedGammaCombination A
        + W.bidiMarkedPoleCombination A := by
  simp [QuarticFourSignedPolePair.markedCompletedArithmeticResponse,
    W.bidiMarkedPrimeCombination_eq_zero ht A]

theorem QuarticFourSignedPolePair.markedCluster_eq_offOrd_add_arithmetic
    {t A : ℝ} (ht : 200 ≤ t)
    (W : QuarticFourSignedPolePair t) :
    W.bidiMarkedClusterCombination A
      =
    W.bidiMarkedOffOrdCombination A
      + W.markedCompletedArithmeticResponse A := by
  rw [W.bidiMarkedCluster_eq_offOrd_add_gamma_add_pole ht A]
  rw [W.markedArithmetic_eq_gamma_add_pole ht]
  ring

theorem QuarticFourSignedPolePair.markedPrime_not_positive
    {t A : ℝ} (ht : 200 ≤ t)
    (W : QuarticFourSignedPolePair t) :
    ¬ (0 < W.bidiMarkedPrimeCombination A) := by
  rw [W.bidiMarkedPrimeCombination_eq_zero ht A]
  exact lt_irrefl 0

theorem exists_selected_marked_arithmetic_pole_bias
    {t : ℝ} (ht : 200 ≤ t) :
    ∃ W : QuarticFourSignedPolePair t,
      7 * Real.pi^4 / 1600 ≤ W.targetStrength
      ∧ ∃ epsA : ℝ, 0 < epsA ∧
        ∀ A : ℝ, 0 < |A| → |A| < epsA →
          W.bidiMarkedOffOrdCombination A
            + W.markedCompletedArithmeticResponse A
              = W.bidiMarkedClusterCombination A
          ∧
          W.bidiMarkedOffOrdCombination A
            + W.bidiMarkedGammaCombination A
              < W.bidiMarkedClusterCombination A := by
  obtain ⟨W,hfloor,epsA,hepsA,hbias⟩ :=
    exists_quarticFourSignedPolePair_with_strength_floor_and_marked_channel_bias ht
  refine ⟨W,hfloor,epsA,hepsA,?_⟩
  intro A hA hsmall
  exact ⟨(W.markedCluster_eq_offOrd_add_arithmetic ht).symm,
    hbias A hA hsmall⟩

/-!
A PSD block is not available from a positive finite character trace
unless its positive diagonal is independently sourced and its
off-diagonal has an established same-object equality with the
selected completed zeta functional. The following elementary real
block theorem isolates the necessary Schur determinant payment.
-/
def RealTwoByTwoNonnegative
    (a d b : ℝ) : Prop :=
  ∀ x y : ℝ, 0 ≤ a*x^2 + 2*b*x*y + d*y^2

theorem realTwoByTwo_nonneg_diagonals
    {a d b : ℝ}
    (h : RealTwoByTwoNonnegative a d b) :
    0 ≤ a ∧ 0 ≤ d := by
  constructor
  · simpa [RealTwoByTwoNonnegative] using h 1 0
  · simpa [RealTwoByTwoNonnegative] using h 0 1

theorem realTwoByTwo_determinant_nonneg
    {a d b : ℝ}
    (h : RealTwoByTwoNonnegative a d b) :
    b^2 ≤ a*d := by
  obtain ⟨ha,hd⟩ := realTwoByTwo_nonneg_diagonals h
  by_cases hzero : a = 0
  · have htest := h (-(d+1)) b
    rw [hzero] at htest
    have hdb : 0 ≤ d * b^2 := mul_nonneg hd (sq_nonneg b)
    nlinarith [sq_nonneg b]
  · have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm hzero)
    have htest := h (-b/a) 1
    have hsq :
        a * (-b/a)^2 + 2*b*(-b/a) + d
          = d - b^2/a := by
      field_simp
      ring
    rw [hsq] at htest
    have hprod := mul_nonneg ha htest
    have hid : a*(d-b^2/a)=a*d-b^2 := by
      field_simp
      ring
    rw [hid] at hprod
    linarith

theorem realTwoByTwo_nonzero_offdiag_requires_positive_diagonals
    {a d b : ℝ}
    (h : RealTwoByTwoNonnegative a d b)
    (hb : b ≠ 0) :
    0 < a ∧ 0 < d ∧ b^2 ≤ a*d := by
  obtain ⟨ha,hd⟩ := realTwoByTwo_nonneg_diagonals h
  have hdet := realTwoByTwo_determinant_nonneg h
  have hb2 : 0 < b^2 := sq_pos_of_ne_zero hb
  refine ⟨?_, ?_,hdet⟩
  · by_contra hnot
    have hz : a = 0 := le_antisymm (le_of_not_gt hnot) ha
    rw [hz] at hdet
    nlinarith
  · by_contra hnot
    have hz : d = 0 := le_antisymm (le_of_not_gt hnot) hd
    rw [hz] at hdet
    nlinarith


/-!
## Removal of the marker does not restore a prime term

At A=0 the cosh marking is exactly the identity on each selected
physical detector. The prime defect is still identically zero. This
is stronger than a statement only about small nonzero markers.
-/

theorem quarticFourPhysicalDetector_primeProjectiveDefect_eq_zero
    {R lam mu t : ℝ}
    (hR : 0 < R)
    (hRone : R < 1)
    (ht : 200 ≤ t) :
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.primeProjectiveDefect
      (quarticFourPhysicalDetector R lam mu t) t (t/16)
      = 0 := by
  have h :=
    quarticFourBidiMarkedPhysicalDetector_primeProjectiveDefect_eq_zero
      (lam := lam) (mu := mu) hR hRone ht (A := 0)
  simpa [quarticFourBidiMarkedPhysicalDetector,
    quarticSignedPoleCoshMarkedDetector_zero] using h

theorem QuarticFourSignedPolePair.unmarkedSelectedPrimeHalf_eq_zero
    {t : ℝ} (ht : 200 ≤ t)
    (W : QuarticFourSignedPolePair t) :
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.primeProjectiveDefect
      (quarticFourPhysicalDetector W.R (1/2) W.muHalf t) t (t/16)
        = 0 :=
  quarticFourPhysicalDetector_primeProjectiveDefect_eq_zero
    W.Rpos W.RltOne ht

theorem QuarticFourSignedPolePair.unmarkedSelectedPrimeTwo_eq_zero
    {t : ℝ} (ht : 200 ≤ t)
    (W : QuarticFourSignedPolePair t) :
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.primeProjectiveDefect
      (quarticFourPhysicalDetector W.R (2/3) W.muTwo t) t (t/16)
        = 0 :=
  quarticFourPhysicalDetector_primeProjectiveDefect_eq_zero
    W.Rpos W.RltOne ht

/-- This is exactly the unmarked A=0 instance of the existing
same-witness two-window prime combination. -/
theorem QuarticFourSignedPolePair.unmarkedSelectedPrimeCombination_eq_zero
    {t : ℝ} (ht : 200 ≤ t)
    (W : QuarticFourSignedPolePair t) :
    W.bidiMarkedPrimeCombination 0 = 0 :=
  W.bidiMarkedPrimeCombination_eq_zero ht 0

end Synthesis
