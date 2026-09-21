import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Fourth-order punctured sign compiler

This is the calculus layer needed by the moment-cancelled RH test.

If f, f1, f2, f3, f4 form a genuine derivative chain,

  f'   = f1,
  f1'  = f2,
  f2'  = f3,
  f3'  = f4,

the first four values through f3 vanish at zero, and f4(0)<0 with f4
continuous, then f is strictly negative on a sufficiently small right punctured
neighbourhood of zero.

The proof deliberately uses only local continuity plus the mean-value
monotonicity compiler, not an informal Taylor expansion.  Thus a future
projective test only needs to provide its exact fourth derivative and moment
identities.
-/

noncomputable section

open Set Topology

namespace Synthesis

theorem exists_neg_right_of_fourth_deriv_neg
    {f f1 f2 f3 f4 : ℝ → ℝ}
    (h01 : ∀ x : ℝ, HasDerivAt f (f1 x) x)
    (h12 : ∀ x : ℝ, HasDerivAt f1 (f2 x) x)
    (h23 : ∀ x : ℝ, HasDerivAt f2 (f3 x) x)
    (h34 : ∀ x : ℝ, HasDerivAt f3 (f4 x) x)
    (h4cont : Continuous f4)
    (hf0 : f 0 = 0)
    (hf10 : f1 0 = 0)
    (hf20 : f2 0 = 0)
    (hf30 : f3 0 = 0)
    (hf40 : f4 0 < 0) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ x : ℝ, 0 < x → x < eps → f x < 0 := by
  have hopen : IsOpen {x : ℝ | f4 x < 0} :=
    isOpen_lt h4cont continuous_const
  have hmem : (0 : ℝ) ∈ {x : ℝ | f4 x < 0} := hf40
  obtain ⟨eps, heps, hball⟩ :=
    (Metric.isOpen_iff.1 hopen) 0 hmem

  have hf4neg : ∀ x : ℝ, |x| < eps → f4 x < 0 := by
    intro x hx
    apply hball
    simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hx

  have hf3cont : Continuous f3 :=
    continuous_of_forall_continuousAt fun x => (h34 x).continuousAt
  have hf2cont : Continuous f2 :=
    continuous_of_forall_continuousAt fun x => (h23 x).continuousAt
  have hf1cont : Continuous f1 :=
    continuous_of_forall_continuousAt fun x => (h12 x).continuousAt
  have hfcont : Continuous f :=
    continuous_of_forall_continuousAt fun x => (h01 x).continuousAt

  have hanti3 : StrictAntiOn f3 (Icc (0 : ℝ) eps) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 eps)
      hf3cont.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    rw [(h34 x).deriv]
    apply hf4neg x
    rw [abs_of_pos hx.1]
    exact hx.2

  have hf3neg :
      ∀ x : ℝ, 0 < x → x < eps → f3 x < 0 := by
    intro x hx0 hxe
    have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) eps := ⟨le_rfl, heps.le⟩
    have hxmem : x ∈ Icc (0 : ℝ) eps := ⟨hx0.le, hxe.le⟩
    have h := hanti3 h0mem hxmem hx0
    rw [hf30] at h
    exact h

  have hanti2 : StrictAntiOn f2 (Icc (0 : ℝ) eps) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 eps)
      hf2cont.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    rw [(h23 x).deriv]
    exact hf3neg x hx.1 hx.2

  have hf2neg :
      ∀ x : ℝ, 0 < x → x < eps → f2 x < 0 := by
    intro x hx0 hxe
    have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) eps := ⟨le_rfl, heps.le⟩
    have hxmem : x ∈ Icc (0 : ℝ) eps := ⟨hx0.le, hxe.le⟩
    have h := hanti2 h0mem hxmem hx0
    rw [hf20] at h
    exact h

  have hanti1 : StrictAntiOn f1 (Icc (0 : ℝ) eps) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 eps)
      hf1cont.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    rw [(h12 x).deriv]
    exact hf2neg x hx.1 hx.2

  have hf1neg :
      ∀ x : ℝ, 0 < x → x < eps → f1 x < 0 := by
    intro x hx0 hxe
    have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) eps := ⟨le_rfl, heps.le⟩
    have hxmem : x ∈ Icc (0 : ℝ) eps := ⟨hx0.le, hxe.le⟩
    have h := hanti1 h0mem hxmem hx0
    rw [hf10] at h
    exact h

  have hantif : StrictAntiOn f (Icc (0 : ℝ) eps) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 eps)
      hfcont.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    rw [(h01 x).deriv]
    exact hf1neg x hx.1 hx.2

  refine ⟨eps, heps, ?_⟩
  intro x hx0 hxe
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) eps := ⟨le_rfl, heps.le⟩
  have hxmem : x ∈ Icc (0 : ℝ) eps := ⟨hx0.le, hxe.le⟩
  have h := hantif h0mem hxmem hx0
  rw [hf0] at h
  exact h

end Synthesis
