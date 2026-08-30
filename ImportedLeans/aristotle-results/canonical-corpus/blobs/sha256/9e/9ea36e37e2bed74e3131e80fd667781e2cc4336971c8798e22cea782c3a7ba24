/-
# Boundary tests for the positive-volume patch compiler

Two adversarial checks that the hypotheses of `PositivePatchEnclosure` are
load-bearing rather than decorative.

* `complementSign_load_bearing` : an explicit integrand with a patch of positive
  measure on which it is at least `1`, whose integral over the ambient set is
  nevertheless `−9 < 0`.  So the complement sign hypothesis of
  `setIntegral_ge_patch` cannot be dropped: a positive patch alone proves
  nothing.
* `nullPatch_gives_nothing` : the measure-zero patch case, restated on the
  momentum cell — a single momentum contributes lower bound `0`.
-/
import RequestProject.YangMills.PositivePatchEnclosure

namespace YangMills

open MeasureTheory Set

private noncomputable def stepIntegrand (x : ℝ) : ℝ := if x ≤ 1 then 1 else -10

private theorem stepIntegrand_integrable : IntegrableOn stepIntegrand (Icc (0 : ℝ) 2) := by
  have hfin : volume (Icc (0 : ℝ) 2) ≠ ⊤ := by simp
  apply Integrable.mono' (g := fun _ : ℝ => (10 : ℝ)) (integrableOn_const (hs := hfin))
  · exact (measurable_const.piecewise measurableSet_Iic
      measurable_const).aestronglyMeasurable
  · filter_upwards with x
    by_cases h : x ≤ 1 <;> simp [stepIntegrand, h]

private theorem stepIntegrand_integral : ∫ x in Icc (0 : ℝ) 2, stepIntegrand x = -9 := by
  have hsplit := MeasureTheory.integral_inter_add_diff (μ := volume) (f := stepIntegrand)
    (s := Icc (0 : ℝ) 2) (t := Iic 1) measurableSet_Iic stepIntegrand_integrable
  have h1 : Icc (0 : ℝ) 2 ∩ Iic 1 = Icc 0 1 := by
    ext x
    simp only [mem_inter_iff, mem_Icc, mem_Iic]
    constructor
    · rintro ⟨⟨ha, _⟩, hb⟩; exact ⟨ha, hb⟩
    · rintro ⟨ha, hb⟩; exact ⟨⟨ha, by linarith⟩, hb⟩
  have h2 : Icc (0 : ℝ) 2 \ Iic 1 = Ioc 1 2 := by
    ext x
    simp only [mem_diff, mem_Icc, mem_Iic, mem_Ioc, not_le]
    constructor
    · rintro ⟨⟨_, hb⟩, hc⟩; exact ⟨hc, hb⟩
    · rintro ⟨ha, hb⟩; exact ⟨⟨by linarith, hb⟩, ha⟩
  rw [h1, h2] at hsplit
  have hA : ∫ x in Icc (0 : ℝ) 1, stepIntegrand x = 1 := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc (g := fun _ => (1 : ℝ))
      (fun x hx => by simp [stepIntegrand, hx.2])]
    simp
  have hB : ∫ x in Ioc (1 : ℝ) 2, stepIntegrand x = -10 := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (g := fun _ => (-10 : ℝ))
      (fun x hx => by simp [stepIntegrand, not_le.2 hx.1])]
    simp
    norm_num
  rw [hA, hB] at hsplit
  linarith

/-- **The complement sign is load-bearing.**  A patch of measure `1` on which
the integrand is at least `1` coexists with an ambient integral of `−9`. -/
theorem complementSign_load_bearing :
    ∃ (f : ℝ → ℝ) (Omega P : Set ℝ),
      MeasurableSet P ∧ P ⊆ Omega ∧ IntegrableOn f Omega ∧
      (∀ x ∈ P, (1 : ℝ) ≤ f x) ∧ 0 < (volume P).toReal ∧
      (∫ x in Omega, f x) < 0 := by
  refine ⟨stepIntegrand, Icc 0 2, Icc 0 1, measurableSet_Icc,
    Icc_subset_Icc le_rfl (by norm_num), stepIntegrand_integrable,
    fun x hx => by simp [stepIntegrand, hx.2], ?_, ?_⟩
  · rw [Real.volume_Icc]
    norm_num
  · rw [stepIntegrand_integral]
    norm_num

/-- **A single momentum buys nothing.**  On the momentum cell, the lower
contribution of a one-point patch is at most `0`, however large the integrand
is there. -/
theorem nullPatch_gives_nothing (q : Fin 4 → ℝ) (c : ℝ) {err : ℝ} (herr : 0 ≤ err) :
    lowerContribution volume ({q} : Set (Fin 4 → ℝ)) c err ≤ 0 :=
  nullPatch_lowerContribution_nonpos (by simp) herr

end YangMills
