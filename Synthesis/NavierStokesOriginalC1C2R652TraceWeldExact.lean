import Mathlib
import Synthesis.NavierStokesFractionalR568EndpointWeldExact
import Synthesis.NavierStokesR726PhysicalRadicalSignCertificatesExact

/-!
# Original R652/R653 and positive coherent-heat endpoint: one signed trace

The original native Agda source already owns
  R652: 4 F_unlifted = 2 R406 + G_self + H_selfTangent.
The original R596 is a FINITE algebraic Gram/forcing normal form, not by
itself a real-time derivative theorem! The additional derivative of the
physical coherent Cauchy Gram and FTC on the original time carrier are
therefore explicit hypotheses named hRealTimeTrace here:
  4 F_unlifted = Q(T)-Q(0)+2 integral Hcoherent.
This is the N2e/physical-trace classical derivation recorded in Agda #1543,
not a direct citation to R596 as a complete real-time kernel theorem.

The exact combined identity pays all R652 representation algebra; the
physical time, phase and pressure, cutoff-uniform signed estimates are
distinct analytic obligations. No estimate is proved for arbitrary data.
-/

namespace DASHI.NavierStokes.OriginalJointTrace

/-- The existing R652 forcing/remainder plus a bona fide physical R596/N2e
real-time-FTC trace give ONE source, not two unrelated remainder objects. -/
theorem r652_original_joint_trace_identity
    (Q0 QT Hcoherent F R406 Gself Htangent : ℝ)
    (hRealTimeTrace : 4*F = QT-Q0+2*Hcoherent)
    (hR652 : 4*F = 2*R406+Gself+Htangent) :
    2*R406 = QT-Q0+2*Hcoherent-Gself-Htangent := by
  linarith only [hRealTimeTrace,hR652]

/-- One bidirectional source-weld for the proposed R645 strict
physical packet surplus, expressed directly on the existing coherent
positive trace. It does not assert that C2 can be paid. -/
theorem r653_original_C2_positive_trace_iff
    (Q0 QT Hcoherent F R406 Gself Htangent surplus : ℝ)
    (hRealTimeTrace : 4*F = QT-Q0+2*Hcoherent)
    (hR652 : 4*F = 2*R406+Gself+Htangent) :
    surplus ≤ R406 ↔
      2*surplus+Q0+Gself+Htangent ≤ QT+2*Hcoherent := by
  have hi := r652_original_joint_trace_identity
    Q0 QT Hcoherent F R406 Gself Htangent hRealTimeTrace hR652
  constructor <;> intro h <;> linarith only [h,hi]

/-- Full signed C1/C2 sandwich, using the REAL R568 forcing and
physical R406 on one selected cutoff/trajectory. C1 and C2 hypotheses
must be separately paid; the old R645 unrestricted C2 has a genuine
physical C=1 countercontrol, so this theorem is not a completion. -/
theorem r652_original_joint_sandwich
    (Q0 QT Hcoherent F R406 Gself Htangent surplus B : ℝ)
    (hRealTimeTrace : 4*F = QT-Q0+2*Hcoherent)
    (hR652 : 4*F = 2*R406+Gself+Htangent)
    (hC1 : 4*F ≤ B)
    (hC2 : surplus ≤ R406) :
    2*surplus+Q0+Gself+Htangent ≤ QT+2*Hcoherent ∧
      QT+2*Hcoherent ≤ B+Q0 := by
  constructor
  · exact (r653_original_C2_positive_trace_iff
      Q0 QT Hcoherent F R406 Gself Htangent surplus
      hRealTimeTrace hR652).mp hC2
  · linarith only [hRealTimeTrace,hC1]

/-- R723 + compensated R726 is not a separate guaranteed improvement:
when both carry their SAME source, their sum literally IS R406.
Separate upper estimates can be strictly harder than the one joint
signed bound. The actual new mathematical producer must exploit
cancellation, not sum two unrelated positive envelopes. -/
theorem r723_r726_compensated_sum_exact
    (r406 combined defect : ℝ)
    (hdef : defect = r406-combined) :
    combined+defect=r406 := by
  linarith only [hdef]

/-- No independent analytic gain from a split: a bound on the JOINT
signed sum is exactly an R406 bound. -/
theorem r723_r726_joint_budget_iff
    (r406 combined defect bound : ℝ)
    (hdef : defect = r406-combined) :
    combined+defect ≤ bound ↔ r406 ≤ bound := by
  rw [r723_r726_compensated_sum_exact _ _ _ hdef]

/-- The direct R568 C1 trace and (false as an unrestricted criterion)
R645 C2 are different sides of ONE coherent trace; no spectral,
zero-mode or rate homogeneity can be erased by order alone. -/
theorem c1_without_c2_has_no_retained_margin
    (B R S : ℝ) (hC1 : R ≤ B)
    (hC2not : S > R) :
    R ≤ B ∧ ¬ S ≤ R := by
  exact ⟨hC1, not_le_of_gt hC2not⟩

end DASHI.NavierStokes.OriginalJointTrace
