import Synthesis.RiemannProjectiveQuarticBaseSignedBand

/-!
# Uniform negative subwindow inside the quartic base lobe

The punctured quartic sign theorem is pointwise.  For counting arguments we need
a quantitative window on which the kernel is bounded away from zero.

Fix a quartic witness W and one of its negative bands B.  Choose the interior
point q0 = eps/2.  The kernel is strictly negative there.  Continuity then gives
an open neighbourhood on which it remains below half that negative value.

Thus there are q0, delta, eta > 0 with delta < q0 such that

  |q-q0| < delta  ->  Phi_Q(q) <= -eta.

After physical scaling r=t/16 this becomes an ordinate interval of width
2 delta r = delta t/8 on which every zero contributes a uniformly negative
q-only base amount (up to multiplicity and the exact r^-2 normalization).

This is the quantitative local producer needed to turn the quartic signed lobe
into a macroscopic negative zero-count contribution.
-/

noncomputable section

open MeasureTheory Set
open scoped Real Topology

namespace Synthesis

structure QuarticBaseUniformNegativeWindow (W : QuarticHighWitness) where
  q0 : ℝ
  delta : ℝ
  eta : ℝ
  q0Pos : 0 < q0
  deltaPos : 0 < delta
  deltaLtQ0 : delta < q0
  etaPos : 0 < eta
  upper :
    ∀ q : ℝ, |q-q0| < delta ->
      genericProjectiveBaseKernel
        (quarticThreeWindowProfile W.R W.lam) 1 q <= -eta

theorem exists_quarticBaseUniformNegativeWindow
    (W : QuarticHighWitness)
    (B : QuarticBaseBand W) :
    ∃ U : QuarticBaseUniformNegativeWindow W, True := by
  let G : ℝ → ℝ := quarticThreeWindowProfile W.R W.lam
  let f : ℝ → ℝ := fun q => genericProjectiveBaseKernel G 1 q
  let q0 : ℝ := B.eps / 2

  have hq0 : 0 < q0 := by
    dsimp [q0]
    linarith [B.epsPos]
  have hq0eps : q0 < B.eps := by
    dsimp [q0]
    linarith [B.epsPos]
  have hq0abs : |q0| = q0 := abs_of_pos hq0
  have hf0neg : f q0 < 0 := by
    dsimp [f]
    exact B.neg q0 (by simpa [hq0abs] using hq0)
      (by simpa [hq0abs] using hq0eps)

  let eta : ℝ := -(f q0) / 2
  have heta : 0 < eta := by
    dsimp [eta]
    linarith

  have hG : Continuous G := by
    dsimp [G]
    exact quarticThreeWindowProfile_continuous W.Rpos
  have hGc : HasCompactSupport G := by
    dsimp [G]
    exact quarticThreeWindowProfile_compact W.Rpos
  have hP :
      Continuous (genericProjectivePhysicalProfile G 1) :=
    genericProjectivePhysicalProfile_continuous hG 1
  have hPc :
      HasCompactSupport (genericProjectivePhysicalProfile G 1) :=
    genericProjectivePhysicalProfile_compact hGc 1
  have hf : Continuous f := by
    apply continuous_of_forall_continuousAt
    intro q
    dsimp [f, genericProjectiveBaseKernel]
    exact
      (compactCosineTransform_hasDerivAt hP hPc q).continuousAt

  have hopen : IsOpen {q : ℝ | f q < -eta} :=
    isOpen_lt hf continuous_const
  have hmem : q0 ∈ {q : ℝ | f q < -eta} := by
    dsimp [eta]
    linarith
  obtain ⟨e, he, hball⟩ :=
    (Metric.isOpen_iff.1 hopen) q0 hmem

  let delta : ℝ := min e q0 / 2
  have hmin : 0 < min e q0 := lt_min he hq0
  have hdelta : 0 < delta := by
    dsimp [delta]
    linarith
  have hdeltaLtQ0 : delta < q0 := by
    dsimp [delta]
    have hle := min_le_right e q0
    linarith [hq0]
  have hdeltaLtE : delta < e := by
    dsimp [delta]
    have hle := min_le_left e q0
    linarith [he]

  refine ⟨{
    q0 := q0
    delta := delta
    eta := eta
    q0Pos := hq0
    deltaPos := hdelta
    deltaLtQ0 := hdeltaLtQ0
    etaPos := heta
    upper := ?_
  }, trivial⟩
  intro q hq
  have hdist : dist q q0 < e := by
    rw [Real.dist_eq]
    have habs : |q - q0| < e := hq.trans hdeltaLtE
    simpa [abs_sub_comm] using habs
  have hqin : q ∈ Metric.ball q0 e := by
    simpa [Metric.mem_ball] using hdist
  exact (hball hqin).le

end Synthesis
