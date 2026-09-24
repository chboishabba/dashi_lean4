import Synthesis.RiemannProjectiveQuarticBaseLocalSign

/-!
# Derivative sign band for the quartic projective base kernel

The fourth-order local-sign proof contains a stronger intermediate fact than
Phi_Q(q)<0.

Under J2=0 and J4<0, the derivative chain gives, for sufficiently small q>0,

  Phi_Q'(q) < 0.

Since Phi_Q is even, Phi_Q' is odd, hence

  q < 0 small  ->  Phi_Q'(q) > 0.

Equivalently,

  0 < |q| < eps  ->  q * Phi_Q'(q) < 0.

This is the local signed-correlation geometry required by the Abel consumer for
the quartic escape.  It is the exact opposite orientation from the canonical
positive-lobe kernel.
-/

noncomputable section

open MeasureTheory Set Topology
open scoped Real

namespace Synthesis

theorem compactCosineD1_neg_right_of_quartic_escape
    {g : ℝ → ℝ} {r : ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (hJ2 : projectiveBracketSecondMoment g r = 0)
    (hJ4 : projectiveBracketFourthMoment g r < 0) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ q : ℝ, 0 < q -> q < eps ->
        compactCosineD1
          (genericProjectivePhysicalProfile g r) q < 0 := by
  let P : ℝ → ℝ := genericProjectivePhysicalProfile g r
  have hP : Continuous P :=
    genericProjectivePhysicalProfile_continuous hg r
  have hPc : HasCompactSupport P :=
    genericProjectivePhysicalProfile_compact hgc r

  have h1zero : compactCosineD1 P 0 = 0 :=
    compactCosineD1_zero P
  have h2zero : compactCosineD2 P 0 = 0 := by
    simpa [P] using
      genericProjectiveBaseKernel_secondDeriv_zero
        (g:=g) (r:=r) hJ2
  have h3zero : compactCosineD3 P 0 = 0 :=
    compactCosineD3_zero P
  have h4zero : compactCosineD4 P 0 < 0 := by
    rw [show compactCosineD4 P 0
        = 4 * projectiveBracketFourthMoment g r by
          simpa [P] using
            genericProjectiveBaseKernel_fourthDeriv_zero
              (g:=g) (r:=r)]
    nlinarith

  have h4cont := compactCosineD4_continuous hP hPc
  have hopen : IsOpen {q : ℝ | compactCosineD4 P q < 0} :=
    isOpen_lt h4cont continuous_const
  have hmem : (0:ℝ) ∈ {q : ℝ | compactCosineD4 P q < 0} := h4zero
  obtain ⟨eps, heps, hball⟩ :=
    (Metric.isOpen_iff.1 hopen) 0 hmem

  have h4neg :
      ∀ q : ℝ, |q| < eps -> compactCosineD4 P q < 0 := by
    intro q hq
    apply hball
    simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hq

  have h3cont : Continuous (compactCosineD3 P) :=
    continuous_of_forall_continuousAt fun q =>
      (compactCosineD3_deriv hP hPc q).continuousAt
  have h2cont : Continuous (compactCosineD2 P) :=
    continuous_of_forall_continuousAt fun q =>
      (compactCosineD2_deriv hP hPc q).continuousAt
  have h1cont : Continuous (compactCosineD1 P) :=
    continuous_of_forall_continuousAt fun q =>
      (compactCosineD1_deriv hP hPc q).continuousAt

  have hanti3 :
      StrictAntiOn (compactCosineD3 P) (Set.Icc 0 eps) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 eps)
      h3cont.continuousOn
    intro q hq
    rw [interior_Icc] at hq
    rw [(compactCosineD3_deriv hP hPc q).deriv]
    apply h4neg q
    rw [abs_of_pos hq.1]
    exact hq.2

  have h3neg :
      ∀ q : ℝ, 0 < q -> q < eps ->
        compactCosineD3 P q < 0 := by
    intro q hq0 hqe
    have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) eps := ⟨le_rfl, heps.le⟩
    have hq : q ∈ Set.Icc (0:ℝ) eps := ⟨hq0.le,hqe.le⟩
    have h := hanti3 h0 hq hq0
    rw [h3zero] at h
    exact h

  have hanti2 :
      StrictAntiOn (compactCosineD2 P) (Set.Icc 0 eps) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 eps)
      h2cont.continuousOn
    intro q hq
    rw [interior_Icc] at hq
    rw [(compactCosineD2_deriv hP hPc q).deriv]
    exact h3neg q hq.1 hq.2

  have h2neg :
      ∀ q : ℝ, 0 < q -> q < eps ->
        compactCosineD2 P q < 0 := by
    intro q hq0 hqe
    have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) eps := ⟨le_rfl, heps.le⟩
    have hq : q ∈ Set.Icc (0:ℝ) eps := ⟨hq0.le,hqe.le⟩
    have h := hanti2 h0 hq hq0
    rw [h2zero] at h
    exact h

  have hanti1 :
      StrictAntiOn (compactCosineD1 P) (Set.Icc 0 eps) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 eps)
      h1cont.continuousOn
    intro q hq
    rw [interior_Icc] at hq
    rw [(compactCosineD1_deriv hP hPc q).deriv]
    exact h2neg q hq.1 hq.2

  refine ⟨eps, heps, ?_⟩
  intro q hq0 hqe
  have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) eps := ⟨le_rfl, heps.le⟩
  have hq : q ∈ Set.Icc (0:ℝ) eps := ⟨hq0.le,hqe.le⟩
  have h := hanti1 h0 hq hq0
  rw [h1zero] at h
  exact h

theorem compactCosineD1_odd
    (P : ℝ → ℝ) (q : ℝ) :
    compactCosineD1 P (-q) = - compactCosineD1 P q := by
  unfold compactCosineD1
  rw [← integral_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    simp [Real.sin_neg]
    ring

theorem exists_genericProjectiveBaseKernel_deriv_radial_neg
    {g : ℝ → ℝ} {r : ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (hJ2 : projectiveBracketSecondMoment g r = 0)
    (hJ4 : projectiveBracketFourthMoment g r < 0) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ q : ℝ, 0 < |q| -> |q| < eps ->
        q *
          compactCosineD1
            (genericProjectivePhysicalProfile g r) q < 0 := by
  obtain ⟨eps,heps,hright⟩ :=
    compactCosineD1_neg_right_of_quartic_escape
      hg hgc hJ2 hJ4
  refine ⟨eps,heps,?_⟩
  intro q hq0 hqe
  by_cases hq : 0 <= q
  · have hqpos : 0 < q := by
      rw [abs_of_nonneg hq] at hq0
      exact hq0
    have habs : |q| = q := abs_of_pos hqpos
    have hd := hright q hqpos (by simpa [habs] using hqe)
    exact mul_neg_of_pos_of_neg hqpos hd
  · have hqneg : q < 0 := lt_of_not_ge hq
    have habs : |q| = -q := abs_of_neg hqneg
    have hdneg :=
      hright (-q) (by linarith) (by simpa [habs] using hqe)
    have hdpos :
        0 <
        compactCosineD1
          (genericProjectivePhysicalProfile g r) q := by
      rw [← neg_neg q, compactCosineD1_odd] at hdneg
      linarith
    exact mul_neg_of_neg_of_pos hqneg hdpos

end Synthesis
