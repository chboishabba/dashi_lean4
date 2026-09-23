/-
# Non-vacuity of the Route `S` carrier

`RouteSData` is a record of hypotheses, so it is worth knowing that it can be
inhabited and that its output is sharp.  Reusing the projection Hamiltonian
`m·P_{Ω^⊥}` and its Dirac spectral measures from `BIDI/Witnesses.lean`, this
file exhibits Route-`S` data whose continuum covariance is the honest
correlation function `‖ψ‖² e^{-m k}` at integer Euclidean separations, and
checks that `routeS_massGapConclusion` then returns exactly the gap `m`.

This is an inhabitation check for the interface, not physical evidence for the
Yang–Mills gap: the carrier here is the projection Hamiltonian, not the
reconstructed Osterwalder–Schrader Hamiltonian of the Wilson theory.
-/
import Mathlib
import RequestProject.YangMills.BIDI.Witnesses
import RequestProject.YangMills.RouteS.Assembly

namespace RequestProject.YangMills.RouteS

open MeasureTheory Set
open RequestProject.YangMills.BIDI
open RequestProject.YangMills.VacuumSectorSpectralGap
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Route-`S` data for the projection Hamiltonian: the continuum covariance of
a vacuum-orthogonal state at Euclidean separation `k` is `‖ψ‖² e^{-mk}`. -/
noncomputable def routeSWitness (vac : E) {m : ℝ} (hm : 0 < m) :
    RouteSData (projHam vac m) vac m where
  spec := (clusteringWitness vac hm).toSpectralRepresentation
  covInf psi k := ((‖(psi : E)‖ ^ 2 * Real.exp (-(m * k)) : ℝ) : ℂ)
  clusterConst psi := ‖(psi : E)‖ ^ 2
  clusterConst_nonneg psi := by positivity
  alpha_pos := hm
  os_same_object psi _ k := by
    have hnorm : ‖((‖(psi : E)‖ ^ 2 * Real.exp (-(m * k)) : ℝ) : ℂ)‖
        = ‖(psi : E)‖ ^ 2 * Real.exp (-(m * k)) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hnorm]
    simp [clusteringWitness, diracSpectralMeasure, integral_smul_measure, smul_eq_mul,
      mul_comm]
  clustering psi k := by
    have hnorm : ‖((‖(psi : E)‖ ^ 2 * Real.exp (-(m * k)) : ℝ) : ℂ)‖
        = ‖(psi : E)‖ ^ 2 * Real.exp (-(m * k)) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hnorm]

omit [CompleteSpace E] in
/-- The witness delivers the gap `m` through Route `S`. -/
theorem routeSWitness_formGap (vac : E) {m : ℝ} (hm : 0 < m) :
    HasVacuumFormGap (projHam vac m) vac m :=
  (routeSWitness vac hm).vacuum_form_gap

/-- And the full mass-gap conclusion, for a unit vacuum. -/
theorem routeSWitness_massGapConclusion (vac : E) (hunit : ‖vac‖ = 1) {m : ℝ} (hm : 0 < m) :
    Clay.MassGapConclusion (projHam vac m) vac m :=
  routeS_massGapConclusion (routeSWitness vac hm) (by simp) hunit
    (by simpa using projHam_vac vac m) (isSelfAdjoint_projHam vac m)

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.RouteS

#print axioms routeSWitness_formGap
#print axioms routeSWitness_massGapConclusion

end Audit

end RequestProject.YangMills.RouteS
