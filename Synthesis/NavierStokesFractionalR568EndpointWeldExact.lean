import Mathlib
import Synthesis.MillenniumNSSignedSpectralResidualExact

/-!
# Physical R596 -> N2e -> R568, without inventing a nonlinear payment

Owner coordinates:
* R225/R388/R596/R597 coherent Cauchy Gram Q and coherent self-work H.
* Agda #1543 N2c and #1551 NSProofControl N2e/N2f signed fractional bridge.
* R568 original UNLIFTED signed, integrated nonzero-output forcing F.
* R652/R653 separate strict-margin signed packet lower bound.

Each scalar argument represents the actual same-cutoff, same-trajectory
functional already derived by the original Fourier owners. The hypotheses
below are the unverified original PHYSICAL real-FTC / fractional-Sobolev
estimates; this module does not construct them from arbitrary scalar functions.
The output k=0 sector is separate (the N2c/N2e reference assumes mean zero).
No global NSE, Galerkin all-cutoff estimate or Clay proof is asserted.
-/

namespace DASHI.NavierStokes.FractionalEndpoint

/-- Exact bidirectional R596 terminal trace reformulation of original R568 C1.
Q0, QT are the real R597-normalized nonnegative Gram values; HI is the
integrated H and FI is the original UNLIFTED forcing integral. -/
theorem original_R568_C1_iff_positive_trace
    (Q0 QT HI FI B : ℝ)
    (hR596 : 4 * FI = QT - Q0 + 2 * HI) :
    4 * FI ≤ B ↔ QT + 2 * HI ≤ B + Q0 := by
  rw [hR596]
  constructor <;> intro h <;> linarith

/-- Original R653 signed retained-surplus lower side, on the exact SAME
physical cutoff and trajectory as the R596 identity. No assumption that
rate-lifted R687 work has the same sign as unlifted FI. -/
theorem original_R653_C2_iff_positive_trace
    (Q0 QT HI FI surplus diagonal : ℝ)
    (hR596 : 4 * FI = QT - Q0 + 2 * HI) :
    2 * surplus + diagonal ≤ 4 * FI ↔
      2 * surplus + diagonal + Q0 ≤ QT + 2 * HI := by
  rw [hR596]
  constructor <;> intro h <;> linarith

/-- True source-preserving C1/C2 sandwich. The two endpoint inequalities
remain distinct: the upper never implies the positive retained C2 margin. -/
theorem original_C1_C2_source_sandwich
    (Q0 QT HI FI surplus diagonal ceiling : ℝ)
    (hR596 : 4 * FI = QT - Q0 + 2 * HI)
    (hC1 : 4 * FI ≤ ceiling)
    (hC2 : 2 * surplus + diagonal ≤ 4 * FI) :
    2 * surplus + diagonal + Q0 ≤ QT + 2 * HI ∧
      QT + 2 * HI ≤ ceiling + Q0 := by
  constructor
  · exact (original_R653_C2_iff_positive_trace
      Q0 QT HI FI surplus diagonal hR596).mp hC2
  · exact (original_R568_C1_iff_positive_trace
      Q0 QT HI FI ceiling hR596).mp hC1

/-- Physical fractional energy FTC in the N2e normalization.  In the
real Galerkin consumer ET²-E0² is the time integral of
2 E_a T_a - 4 ν E_a D_a, rather than an unrelated amplitude budget. -/
theorem n2e_energy_square_FTC
    (ν E0 ET ED signedTransfer : ℝ)
    (hν : ν ≠ 0)
    (hFTC : ET ^ 2 - E0 ^ 2 =
      2 * signedTransfer - 4 * ν * ED) :
    32 * ED =
      (8 / ν) * (E0 ^ 2 - ET ^ 2 + 2 * signedTransfer) := by
  field_simp [hν]
  nlinarith only [hFTC]

/-- The algebraic core of N2e, with its precise physical input slots.
For the Fourier application κ=8 K_a/ν, Qcap is the terminal HEAT
product estimate and Hcap is the physical mixed-product trace estimate.
Neither heat estimate is manufactured by the scalar theorem. -/
theorem n2e_signed_fractional_endpoint
    (ν κ E0 ET ED signedTransfer QT HI : ℝ)
    (hFTC : ET ^ 2 - E0 ^ 2 =
      2 * signedTransfer - 4 * ν * ED)
    (hHeatQ : QT ≤ κ * ET ^ 2)
    (hTraceH : 2 * HI ≤ 4 * ν * κ * ED) :
    QT + 2 * HI ≤
      κ * (E0 ^ 2 + 2 * signedTransfer) := by
  have hm := congrArg (fun x : ℝ => κ * x) hFTC
  nlinarith only [hHeatQ, hTraceH, hm]

/-- Actual direct P0-B producer implication: when a genuine uniform signed
bound on integral E_(1/4) T_(1/4) is eventually paid, the original
R596/R568 C1 follows with no Schur/M2 four-leaf detour. All appearances
of Q, H and F refer to ONE real-Galerkin trajectory and cutoff. -/
theorem original_R568_C1_of_fractional_signed_transfer
    (ν κ E0 ET ED signedTransfer transferCeiling
      Q0 QT HI FI : ℝ)
    (hκ : 0 ≤ κ)
    (hQ0 : 0 ≤ Q0)
    (hR596 : 4 * FI = QT - Q0 + 2 * HI)
    (hFTC : ET ^ 2 - E0 ^ 2 =
      2 * signedTransfer - 4 * ν * ED)
    (hHeatQ : QT ≤ κ * ET ^ 2)
    (hTraceH : 2 * HI ≤ 4 * ν * κ * ED)
    (hSignedUpper : signedTransfer ≤ transferCeiling) :
    4 * FI ≤ κ * (E0 ^ 2 + 2 * transferCeiling) := by
  have hn := n2e_signed_fractional_endpoint ν κ E0 ET ED
    signedTransfer QT HI hFTC hHeatQ hTraceH
  have ht : κ * (E0 ^ 2 + 2 * signedTransfer) ≤
      κ * (E0 ^ 2 + 2 * transferCeiling) :=
    mul_le_mul_of_nonneg_left (by linarith) hκ
  linarith only [hn, ht, hR596, hQ0]

/-- At a=0, zero energy transfer makes the N2c negative-order trace
uniform once the true heat and physical-energy inputs are supplied.
This does not promote it to unweighted original R568 (a=1/4). -/
theorem n2c_zero_transfer_budget
    (ν κ E0 ET ED QT HI : ℝ)
    (hFTC : ET ^ 2 - E0 ^ 2 = -4 * ν * ED)
    (hHeatQ : QT ≤ κ * ET ^ 2)
    (hTraceH : 2 * HI ≤ 4 * ν * κ * ED) :
    QT + 2 * HI ≤ κ * E0 ^ 2 := by
  have h := n2e_signed_fractional_endpoint ν κ E0 ET ED 0 QT HI
    (by linarith only [hFTC]) hHeatQ hTraceH
  nlinarith only [h]

/-- Retain the reverse direction: for fixed original initial Gram, an
unweighted R568 upper is equivalent to the terminal positive trace bound,
NOT to positivity of R541's Cauchy kernel or the rate-lifted R687 sign. -/
theorem c1_sufficient_and_necessary_given_R596
    (Q0 QT HI FI B : ℝ) (h : 4 * FI = QT - Q0 + 2 * HI) :
    (4 * FI ≤ B → QT + 2 * HI ≤ B + Q0) ∧
      (QT + 2 * HI ≤ B + Q0 → 4 * FI ≤ B) := by
  exact ⟨(original_R568_C1_iff_positive_trace Q0 QT HI FI B h).mp,
         (original_R568_C1_iff_positive_trace Q0 QT HI FI B h).mpr⟩

end DASHI.NavierStokes.FractionalEndpoint
