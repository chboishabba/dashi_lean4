import Synthesis.RiemannProjectiveQuarticFourWindow
import Synthesis.RiemannProjectiveQuarticThreeWindowLocalization

/-!
# Uniform localization of the smooth four-window family

For a continuous even weight w, the normalized smooth pairing

  <G_{R,lambda,mu},w>

converges uniformly to the atomic four-point pairing

  w(0)-w(pi/3)+lambda w(pi/2)+mu w(pi)

on the compact coefficient rectangle

  lambda in [1/2,2/3],  |mu| <= 1/10.

The coefficient absolute sum is < 3, so choosing each bump-localization error
at eps/3 suffices.  This is the robustness layer needed to lift the free atomic
J2-null manifold to actual C² compact profiles.
-/

noncomputable section

open Set
open scoped Real

namespace Synthesis

def quarticFourAtomicPairingAt
    (lam mu : ℝ) (w : ℝ -> ℝ) : ℝ :=
  w 0 - w (Real.pi/3)
    + lam * w (Real.pi/2)
    + mu * w Real.pi

theorem quarticFourAtomicPairing_momentWeight
    (lam mu : ℝ) (k : ℕ) (s : ℝ) :
    quarticFourAtomicPairingAt lam mu
      (quarticMomentWeight k s)
      =
    quarticFourAtomicMomentRespAt lam mu k s := by
  unfold quarticFourAtomicPairingAt quarticMomentWeight
    quarticFourAtomicMomentRespAt
  ring

theorem quarticFourWindowPairing_momentWeight
    (R lam mu : ℝ) (k : ℕ) (s : ℝ) :
    quarticFourWindowPairing R lam mu
      (quarticMomentWeight k s)
      =
    quarticFourWindowMomentResp R lam mu k s := by
  rfl

theorem exists_radius_quarticFourWindowPairing_close_atomic
    {w : ℝ -> ℝ}
    (hw : Continuous w)
    (heven : ∀ u, w (-u) = w u)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ R lam mu : ℝ,
        0 < R -> R < delta ->
        lam ∈ Set.Icc (1/2 : ℝ) (2/3 : ℝ) ->
        |mu| <= 1/10 ->
        |quarticFourWindowPairing R lam mu w
          - quarticFourAtomicPairingAt lam mu w| <= eps := by
  let eta : ℝ := eps / 3
  have heta : 0 < eta := by
    dsimp [eta]
    linarith
  obtain ⟨d0,hd0,h0⟩ :=
    exists_radius_normalizedSymBumpPairing_close
      (c:=0) hw heven heta
  obtain ⟨d1,hd1,h1⟩ :=
    exists_radius_normalizedSymBumpPairing_close
      (c:=Real.pi/3) hw heven heta
  obtain ⟨d2,hd2,h2⟩ :=
    exists_radius_normalizedSymBumpPairing_close
      (c:=Real.pi/2) hw heven heta
  obtain ⟨d3,hd3,h3⟩ :=
    exists_radius_normalizedSymBumpPairing_close
      (c:=Real.pi) hw heven heta
  let delta := min d0 (min d1 (min d2 d3))
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min hd0 (lt_min hd1 (lt_min hd2 hd3))
  refine ⟨delta,hdelta,?_⟩
  intro R lam mu hR hRd hlam hmu
  have hRd0 : R < d0 :=
    hRd.trans_le (min_le_left _ _)
  have hrest1 : R < min d1 (min d2 d3) :=
    hRd.trans_le (min_le_right _ _)
  have hRd1 : R < d1 :=
    hrest1.trans_le (min_le_left _ _)
  have hrest2 : R < min d2 d3 :=
    hrest1.trans_le (min_le_right _ _)
  have hRd2 : R < d2 :=
    hrest2.trans_le (min_le_left _ _)
  have hRd3 : R < d3 :=
    hrest2.trans_le (min_le_right _ _)

  have he0 := h0 R hR hRd0
  have he1 := h1 R hR hRd1
  have he2 := h2 R hR hRd2
  have he3 := h3 R hR hRd3

  let e0 := normalizedSymBumpPairing 0 R w - w 0
  let e1 :=
    normalizedSymBumpPairing (Real.pi/3) R w
      - w (Real.pi/3)
  let e2 :=
    normalizedSymBumpPairing (Real.pi/2) R w
      - w (Real.pi/2)
  let e3 :=
    normalizedSymBumpPairing Real.pi R w
      - w Real.pi

  have he0' : |e0| <= eta := by simpa [e0] using he0
  have he1' : |e1| <= eta := by simpa [e1] using he1
  have he2' : |e2| <= eta := by simpa [e2] using he2
  have he3' : |e3| <= eta := by simpa [e3] using he3
  have hlam0 : 0 <= lam := by linarith [hlam.1]
  have hlamAbs : |lam| <= 2/3 := by
    rw [abs_of_nonneg hlam0]
    exact hlam.2

  have htri :
      |e0-e1+lam*e2+mu*e3|
        <=
      |e0|+|e1|+|lam|*|e2|+|mu|*|e3| := by
    calc
      |e0-e1+lam*e2+mu*e3|
        <= |e0-e1+lam*e2| + |mu*e3| := abs_add _ _
      _ <= (|e0-e1|+|lam*e2|) + |mu|*|e3| := by
        gcongr
        · exact abs_add _ _
        · rw [abs_mul]
      _ <= (|e0|+|e1|)+|lam|*|e2|+|mu|*|e3| := by
        gcongr
        exact abs_sub _ _

  have hbound :
      |e0-e1+lam*e2+mu*e3| <= eps := by
    calc
      |e0-e1+lam*e2+mu*e3|
        <= |e0|+|e1|+|lam|*|e2|+|mu|*|e3| := htri
      _ <= eta+eta+(2/3:ℝ)*eta+(1/10:ℝ)*eta := by
        gcongr
      _ <= eps := by
        dsimp [eta]
        nlinarith

  unfold quarticFourWindowPairing quarticFourAtomicPairingAt
  have hid :
      normalizedSymBumpPairing 0 R w
        - normalizedSymBumpPairing (Real.pi/3) R w
        + lam*normalizedSymBumpPairing (Real.pi/2) R w
        + mu*normalizedSymBumpPairing Real.pi R w
        - (w 0-w (Real.pi/3)+lam*w (Real.pi/2)+mu*w Real.pi)
      =
      e0-e1+lam*e2+mu*e3 := by
    dsimp [e0,e1,e2,e3]
    ring
  rw [hid]
  exact hbound

end Synthesis
