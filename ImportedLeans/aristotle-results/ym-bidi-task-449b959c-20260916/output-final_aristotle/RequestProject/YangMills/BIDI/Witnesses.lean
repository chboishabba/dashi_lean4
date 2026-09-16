/-
# Non-vacuity of the BIDI carriers

None of the statements in this development is vacuous.  This file exhibits
inhabitants of the two carriers that carry hypotheses:

* `mixedLogDeriv_bilinear` — the source calculus computes: for the entire
  source-domain function `log Z(x,y) = a·x·y` the mixed derivative is `a`, so
  `mixedLogDeriv` is not identically zero and the waist estimate has content;
* `clusteringWitness` — in any complex Hilbert space with a unit vector `Ω` and
  any `m > 0`, the projection Hamiltonian `m·P_{Ω^⊥}` already in this library
  (`VacuumSectorSpectralGap.projHam`) carries a `ClusteringSpectralData` whose
  spectral measures are `‖ψ‖²·δ_m`: every vacuum-orthogonal state clusters at
  exactly the rate `m`.  Feeding it to `hasVacuumFormGap_of_clustering`
  reproduces the gap `m`, so the terminal half of the BIDI chain is inhabited
  and its output is sharp.
-/
import Mathlib
import RequestProject.YangMills.BIDI.ClusteringGap
import RequestProject.YangMills.BIDI.SourceCalculus

namespace RequestProject.YangMills.BIDI

open MeasureTheory Set Filter Topology
open RequestProject.YangMills.VacuumSectorSpectralGap
open scoped InnerProductSpace

/-- The source calculus computes on an entire two-source function. -/
theorem mixedLogDeriv_bilinear (a : ℂ) : mixedLogDeriv (fun x y => a * (x * y)) = a := by
  have hinner : ∀ x : ℂ, deriv (fun y => a * (x * y)) 0 = a * x := by
    intro x
    have hfun : (fun y : ℂ => a * (x * y)) = fun y => (a * x) * y := by
      funext y; ring
    rw [hfun, deriv_const_mul_field]
    simp
  simp only [mixedLogDeriv, hinner]
  rw [deriv_const_mul_field]
  simp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

noncomputable def diracSpectralMeasure {H : E →ₗ.[ℂ] E} (m : ℝ) (psi : H.domain) :
    Measure ℝ :=
  (ENNReal.ofReal (‖(psi : E)‖ ^ 2)) • Measure.dirac m

omit [CompleteSpace E] in
theorem diracSpectralMeasure_apply {H : E →ₗ.[ℂ] E} (m : ℝ) (psi : H.domain)
    (s : Set ℝ) (hs : MeasurableSet s) :
    diracSpectralMeasure (H := H) m psi s
      = ENNReal.ofReal (‖(psi : E)‖ ^ 2) * Measure.dirac m s := by
  simp [diracSpectralMeasure, Measure.smul_apply, smul_eq_mul, hs]

noncomputable def clusteringWitness (vac : E) {m : ℝ} (hm : 0 < m) :
    ClusteringSpectralData (projHam vac m) vac m where
  spectralMeasure psi := diracSpectralMeasure (H := projHam vac m) m psi
  isFinite psi _ := by
    refine ⟨?_⟩
    rw [diracSpectralMeasure_apply (H := projHam vac m) m psi univ MeasurableSet.univ]
    simp
  carried psi _ := by
    rw [diracSpectralMeasure_apply (H := projHam vac m) m psi _ measurableSet_Iio]
    have : m ∉ Iio (0:ℝ) := by simp [not_lt, le_of_lt hm]
    simp [Measure.dirac_apply' _ measurableSet_Iio, this]
  total_mass psi _ := by
    rw [diracSpectralMeasure_apply (H := projHam vac m) m psi univ MeasurableSet.univ]
    simp
  mean_energy psi horth := by
    have hop : projHam vac m psi = (m : ℂ) • (psi : E) :=
      projHam_apply_of_orthogonal psi horth
    rw [hop, UnboundedFormGapResolvent.re_inner_smul_self]
    simp [diracSpectralMeasure, integral_smul_measure, smul_eq_mul, mul_comm]
  integrable_energy psi _ := by
    refine Integrable.smul_measure ?_ (by simp)
    exact integrable_dirac (f := fun x : ℝ => x) enorm_lt_top
  no_zero_mode psi _ := by
    rw [diracSpectralMeasure_apply (H := projHam vac m) m psi _ (measurableSet_singleton 0)]
    have : m ∉ ({0} : Set ℝ) := by
      simp only [mem_singleton_iff]
      exact ne_of_gt hm
    simp [this]
  clusterConst psi := ‖(psi : E)‖ ^ 2
  clustering psi _ t _ := by
    simp [diracSpectralMeasure, integral_smul_measure, smul_eq_mul, mul_comm]

omit [CompleteSpace E] in
theorem clusteringWitness_formGap (vac : E) {m : ℝ} (hm : 0 < m) :
    HasVacuumFormGap (projHam vac m) vac m :=
  hasVacuumFormGap_of_clustering (clusteringWitness vac hm)

end RequestProject.YangMills.BIDI
