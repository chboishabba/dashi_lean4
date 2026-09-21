import Synthesis.RiemannProjectiveQuarticThreeWindow

/-!
# Uniform localization of the smooth three-window family

For a continuous even weight w, define the atomic three-radius pairing

  w(0) - w(pi/3) + lambda w(pi/2).

The normalized smooth three-window pairing converges to this uniformly for

  lambda in [1/2,3/4].

Uniformity is elementary: the three individual normalized bump pairings do not
depend on lambda, and |lambda| <= 3/4 on the parameter interval.  This is the
robustness input needed to transport the atomic J2 sign change and the uniform
negative J4 margin to sufficiently narrow smooth windows.
-/

noncomputable section

open Set
open scoped Real

namespace Synthesis

def quarticAtomicPairingAt
    (lam : ℝ) (w : ℝ → ℝ) : ℝ :=
  w 0 - w (Real.pi/3) + lam * w (Real.pi/2)

theorem exists_radius_quarticThreeWindowPairing_close_atomic
    {w : ℝ → ℝ}
    (hw : Continuous w)
    (heven : ∀ u, w (-u) = w u)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ R lam : ℝ,
        0 < R -> R < delta ->
        lam ∈ Set.Icc (1/2 : ℝ) (3/4 : ℝ) ->
        |quarticThreeWindowPairing R lam w
          - quarticAtomicPairingAt lam w| ≤ eps := by
  let eta : ℝ := eps / 3
  have heta : 0 < eta := by
    dsimp [eta]
    linarith
  obtain ⟨d0, hd0, h0⟩ :=
    exists_radius_normalizedSymBumpPairing_close
      (c := 0) hw heven heta
  obtain ⟨d1, hd1, h1⟩ :=
    exists_radius_normalizedSymBumpPairing_close
      (c := Real.pi/3) hw heven heta
  obtain ⟨d2, hd2, h2⟩ :=
    exists_radius_normalizedSymBumpPairing_close
      (c := Real.pi/2) hw heven heta
  let delta : ℝ := min d0 (min d1 d2)
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min hd0 (lt_min hd1 hd2)
  refine ⟨delta, hdelta, ?_⟩
  intro R lam hR hRd hlam
  have hRd0 : R < d0 := hRd.trans_le (min_le_left d0 (min d1 d2))
  have hRd12 : R < min d1 d2 :=
    hRd.trans_le (min_le_right d0 (min d1 d2))
  have hRd1 : R < d1 := hRd12.trans_le (min_le_left d1 d2)
  have hRd2 : R < d2 := hRd12.trans_le (min_le_right d1 d2)
  have he0 := h0 R hR hRd0
  have he1 := h1 R hR hRd1
  have he2 := h2 R hR hRd2
  have hlam0 : 0 ≤ lam := by linarith [hlam.1]
  have hlamAbs : |lam| ≤ 3/4 := by
    rw [abs_of_nonneg hlam0]
    exact hlam.2

  let e0 := normalizedSymBumpPairing 0 R w - w 0
  let e1 := normalizedSymBumpPairing (Real.pi/3) R w - w (Real.pi/3)
  let e2 := normalizedSymBumpPairing (Real.pi/2) R w - w (Real.pi/2)
  have he0' : |e0| ≤ eta := by simpa [e0] using he0
  have he1' : |e1| ≤ eta := by simpa [e1] using he1
  have he2' : |e2| ≤ eta := by simpa [e2] using he2
  have htri :
      |e0 - e1 + lam*e2|
        ≤ |e0| + |e1| + |lam|*|e2| := by
    calc
      |e0 - e1 + lam*e2|
        ≤ |e0 - e1| + |lam*e2| := abs_add _ _
      _ ≤ (|e0| + |e1|) + |lam|*|e2| := by
        gcongr
        · exact abs_sub e0 e1
        · rw [abs_mul]
  have hbound :
      |e0 - e1 + lam*e2| ≤ eps := by
    calc
      |e0 - e1 + lam*e2|
        ≤ |e0| + |e1| + |lam|*|e2| := htri
      _ ≤ eta + eta + (3/4 : ℝ)*eta := by
        gcongr
      _ ≤ eps := by
        dsimp [eta]
        linarith

  unfold quarticThreeWindowPairing quarticAtomicPairingAt
  have hid :
      normalizedSymBumpPairing 0 R w
        - normalizedSymBumpPairing (Real.pi/3) R w
        + lam * normalizedSymBumpPairing (Real.pi/2) R w
        - (w 0 - w (Real.pi/3) + lam*w (Real.pi/2))
        =
      e0 - e1 + lam*e2 := by
    dsimp [e0,e1,e2]
    ring
  rw [hid]
  exact hbound

end Synthesis
