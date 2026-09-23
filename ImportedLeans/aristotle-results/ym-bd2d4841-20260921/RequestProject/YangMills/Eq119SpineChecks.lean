/-
# Non-vacuity and axiom audit for the Eq. (119) spine and the terminal quotient

The spine theorems are conditional on a stored-bond budget; this file shows the
hypotheses are simultaneously satisfiable by an explicit rational unit
quaternion, so nothing above is vacuous, and audits the axioms of the headline
theorems.
-/
import Mathlib
import RequestProject.YangMills.Eq119RelativeLogSpine
import RequestProject.YangMills.PhysicalNullQuotient
import RequestProject.YangMills.PhysicalTimeEvolutionGenerator

namespace RequestProject.YangMills.Eq119SpineChecks

open NormedSpace
open RequestProject.YangMills.SU2QuaternionOperatorNorm
open RequestProject.YangMills.RelativeHolonomyDefect
open RequestProject.YangMills.Eq119RelativeLogSpine

/-- An explicit rational unit quaternion inside the stored-bond budget:
`(m² - n², 2mn, 0, 0)/(m² + n²)` with `m = 5000`, `n = 1`. -/
noncomputable def witnessBond : Quaternion ℝ :=
  ⟨24999999 / 25000001, 10000 / 25000001, 0, 0⟩

theorem witnessBond_isUnit : IsUnitQuaternion witnessBond := by
  unfold IsUnitQuaternion witnessBond
  norm_num

theorem witnessBond_defect : l1defect witnessBond ≤ 1 / 2048 := by
  unfold l1defect witnessBond
  rw [show (24999999 / 25000001 : ℝ) - 1 = -(2 / 25000001) by norm_num]
  rw [abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2 / 25000001),
    abs_of_nonneg (by norm_num : (0:ℝ) ≤ 10000 / 25000001)]
  norm_num

/-- A full-length canonical word of stored bonds. -/
noncomputable def witnessWord : List (Bool × Quaternion ℝ) :=
  List.replicate 74 (true, witnessBond)

theorem witnessWord_isUnit : ∀ b ∈ witnessWord, IsUnitQuaternion b.2 := by
  intro b hb
  rw [witnessWord, List.mem_replicate] at hb
  rw [hb.2]
  exact witnessBond_isUnit

theorem witnessWord_defect : ∀ b ∈ witnessWord, l1defect b.2 ≤ 1 / 2048 := by
  intro b hb
  rw [witnessWord, List.mem_replicate] at hb
  rw [hb.2]
  exact witnessBond_defect

/-- The spine is non-vacuous: its hypotheses hold for a genuine
`74`-link word, and the conclusion produces an actual logarithm. -/
theorem witness_spine :
    ∃ Y : Quaternion ℝ, Y.re = 0 ∧ ‖Y‖ ≤ Real.arccos (1 - 37 / 1024) ∧
      exp (su2 Y) = holonomy (witnessWord ++ reverseWord []) := by
  refine relative_log_spine_quantitative witnessWord [] ?_ ?_ ?_
  · simp [witnessWord]
  · intro b hb
    simp only [reverseWord, List.map_nil, List.reverse_nil, List.append_nil] at hb
    exact witnessWord_isUnit b hb
  · intro b hb
    simp only [reverseWord, List.map_nil, List.reverse_nil, List.append_nil] at hb
    exact witnessWord_defect b hb

/-! ## Axiom audits -/

#print axioms RequestProject.YangMills.SU2QuaternionOperatorNorm.su2_norm
#print axioms RequestProject.YangMills.SU2QuaternionOperatorNorm.su2_defect_le_l1
#print axioms RequestProject.YangMills.RelativeHolonomyDefect.holonomy_relative
#print axioms RequestProject.YangMills.RelativeHolonomyDefect.relative_holonomy_defect_lt_inv24
#print axioms RequestProject.YangMills.SU2PrincipalChart.exp_qlog
#print axioms RequestProject.YangMills.SU2PrincipalChart.principal_chart_of_defect_lt_one
#print axioms RequestProject.YangMills.Eq119RelativeLogSpine.relative_log_spine
#print axioms RequestProject.YangMills.Eq119RelativeLogSpine.relative_log_spine_quantitative
#print axioms RequestProject.YangMills.PhysicalNullQuotient.nullRel_of_forall_inner_eq
#print axioms RequestProject.YangMills.PhysicalNullQuotient.descend_congr_of_forall_inner_eq
#print axioms RequestProject.YangMills.PhysicalTimeEvolutionGenerator.hamiltonian_eq_of_unitary_group_eq
#print axioms RequestProject.YangMills.Eq119SpineChecks.witness_spine

end RequestProject.YangMills.Eq119SpineChecks
