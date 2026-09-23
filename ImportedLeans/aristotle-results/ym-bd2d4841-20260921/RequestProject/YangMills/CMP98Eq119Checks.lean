/-
# Non-vacuity checks and witnesses for the Eq. (119) layer

Every hypothesis package used in `CMP98Eq119Transport`, `CMP98Eq119GCalculus`
and `CMP98Eq119Assembly` is inhabited here, so none of those theorems is
vacuously true:

* `eq119Contour_endpoint_witness` — with the canonical legs and the canonical
  coarse bond, the `28561` averaging contours really all join the same two
  centres, on a torus (`26⁴`) strictly larger than one block.
* `centres_distinct_witness`, `embedOffset_injective_witness` — that geometry
  is non-degenerate: the two block centres are distinct sites and the `13⁴`
  block offsets embed injectively, so the block is a proper sub-box.
* `adOp_quaternion_ne_zero` — the commutator operator is genuinely non-zero on
  a noncommutative algebra (the real quaternions), so the `ad`-calculus layer
  is not about a trivial operator.
* `isUnit_balabanG_quarter_quaternion` — a concrete small-field point at which
  the trivialisation `g(ad Y)` is invertible.

The final section audits the axioms of the headline results.
-/
import RequestProject.YangMills.CMP98Eq119PhysicalLog

namespace YangMills.CMP98Eq119

open Quaternion

/-! ## 1. The canonical geometry is non-degenerate -/

/-- With the canonical legs and the canonical coarse bond, all `13⁴ = 28561`
averaging contours join the same two centres — on a torus (`N = 26`) strictly
larger than one block, so this is not the degenerate case. -/
theorem eq119Contour_endpoint_witness (μ : Fin 4) (p : BlockOffset) :
    walk (0 : PSite 4 26) (eq119Contour legWord (coarseBond μ true) p)
      = nextCentre (0 : PSite 4 26) μ true := by
  refine eq119Contour_endpoint (cPlus := nextCentre (0 : PSite 4 26) μ true) ?_ ?_ p
  · intro q
    simpa using walk_legWord (0 : PSite 4 26) q
  · exact walk_coarseBond _ _ _

/-- The two block centres of that witness really are distinct sites. -/
theorem centres_distinct_witness (μ : Fin 4) :
    nextCentre (0 : PSite 4 26) μ true ≠ (0 : PSite 4 26) :=
  nextCentre_ne (by norm_num) _ _

/-- The `13⁴` block offsets embed injectively into the `26⁴` torus, so the
block is a genuine proper sub-box. -/
theorem embedOffset_injective_witness :
    Function.Injective (embedOffset (N := 26)) :=
  embedOffset_injective (by norm_num)

/-! ## 2. The `ad`-calculus is non-trivial -/

/-- The quaternion unit `i`. -/
noncomputable def qi : Quaternion ℝ := ⟨0, 1, 0, 0⟩

/-- The quaternion unit `j`. -/
noncomputable def qj : Quaternion ℝ := ⟨0, 0, 1, 0⟩

theorem adOp_quaternion_ne_zero : adOp qi qj ≠ 0 := by
  rw [adOp_apply]
  intro h
  have h2 := congrArg QuaternionAlgebra.imK h
  simp [qi, qj] at h2

theorem norm_qi : ‖qi‖ = 1 := by
  have h1 : Quaternion.normSq qi = 1 := by simp [qi, Quaternion.normSq_def']
  have h2 := Quaternion.normSq_eq_norm_mul_self qi
  rw [h1] at h2
  nlinarith [norm_nonneg qi]

/-- A concrete small-field point: at `Y = ¼ i` the trivialisation `g(ad Y)` is
invertible. -/
theorem isUnit_balabanG_quarter_quaternion :
    IsUnit (balabanG (adOp ((1 / 4 : ℝ) • qi))) := by
  refine (exists_inverse_of_norm_lt ?_).1
  rw [norm_smul, norm_qi, mul_one, Real.norm_eq_abs]
  have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  linarith

/-! ## 3. The physical-log package is inhabited -/

section Flat

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem expLog_one : expLog (1 : A) = 0 := by
  simpa [expLog] using (hasStrictFDerivAt_exp_zero_real (A := A)).localInverse_apply_image

omit [NormedAlgebra ℝ A] [CompleteSpace A] in
theorem hol_flat {N : ℕ} (x : PSite 4 N) (w : List (Step 4)) :
    hol (fun _ _ => (1 : Aˣ)) x w = 1 := by
  induction w generalizing x with
  | nil => rfl
  | cons s ss ih => simp [hol, ih]

omit [NormedAlgebra ℝ A] [CompleteSpace A] in
theorem relativeHolonomy_flat {N : ℕ} (x : PSite 4 N) (gamma coarse : List (Step 4)) :
    relativeHolonomy (fun _ _ => (1 : Aˣ)) x gamma coarse = 1 := by
  simp [relativeHolonomy, hol_flat]

/-- The two smallness hypotheses of `eq119_data_from_lattice` are satisfiable:
the flat link field meets both, for every positive radius. -/
theorem flat_link_smallness {N : ℕ} {ε : ℝ} (hε : 0 < ε) (cMinus : PSite 4 N)
    (gamma : BlockOffset → List (Step 4)) (coarse : List (Step 4)) :
    (∀ p, ‖relativeHolonomy (fun _ _ => (1 : Aˣ)) cMinus (gamma p) coarse - 1‖ < ε)
      ∧ (∀ p, ‖physicalLog (fun _ _ => (1 : Aˣ)) cMinus (gamma p) coarse‖
          < Real.log 2 / 2) := by
  constructor
  · intro p
    simpa [relativeHolonomy_flat] using hε
  · intro p
    have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    simp only [physicalLog, relativeHolonomy_flat, expLog_one, norm_zero]
    linarith

end Flat

/-! ## 4. Axiom audit -/

#print axioms rzero_append
#print axioms rzero_revWord
#print axioms crossing_of_centres
#print axioms balabanG_neg
#print axioms balabanJ_transport
#print axioms isUnit_balabanG_of_norm_lt_log_two
#print axioms expAd_apply
#print axioms balabanG_adOp_neg_apply
#print axioms eq119Contour_endpoint
#print axioms eq119_of_plus_convention
#print axioms exists_inverse_of_norm_lt
#print axioms walk_legWord
#print axioms walk_coarseBond
#print axioms nextCentre_ne
#print axioms embedOffset_injective
#print axioms eq119Contour_endpoint_witness
#print axioms adOp_quaternion_ne_zero
#print axioms isUnit_balabanG_quarter_quaternion
#print axioms exists_exp_physicalLog
#print axioms eq119_data_from_lattice
#print axioms flat_link_smallness

end YangMills.CMP98Eq119
