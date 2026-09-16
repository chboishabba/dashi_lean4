/-
# Row A1a — the shell bound as a genuine Lebesgue integral over the Brillouin cell

The earlier development carried the cell integral as an *abstract positive linear
functional* (an interface: monotone, additive, homogeneous, with an assumed value
on constants and an assumed near/far split).  Here the functional is replaced by
the actual Lebesgue integral of the four-dimensional Brillouin cell
`[0,1/2]^4 ⊂ (Fin 4 → ℝ)` with respect to `volume`, so the split, the
monotonicity and the two box measures are *theorems*, not hypotheses:

* `volume` of the near box `[0,r]^4` is `r^4`;
* `volume` of the far shell `[0,1/2]^4 \ [0,r]^4` is `1/16 − r^4`;
* the cell integral is the sum of the two region integrals.

The main theorem `shell_lower_bound` turns two *pointwise* region bounds on the
orbit density into one lower bound for the cell integral, and
`shellBudget_at_two_fifths` evaluates the resulting budget at the working radius
`r = 2/5` with the near/far constants proved in `NearFarRegions.lean`.
-/
import RequestProject.YangMills.NearFarRegions

namespace YangMills

open MeasureTheory

/-! ## 1. The boxes and their measures -/

/-- The axis-aligned box `[a,b]^4` inside `Fin 4 → ℝ`. -/
def cellBox (a b : ℝ) : Set (Fin 4 → ℝ) := Set.univ.pi fun _ => Set.Icc a b

/-- The positive-orthant Brillouin cell `[0,1/2]^4`.  All of the analysis below
is carried out on this cell; the (standard) reduction of the full-zone integral
to this cell by hypercubic symmetry is *not* proved here and is not used. -/
def brillouinCell : Set (Fin 4 → ℝ) := cellBox 0 (1 / 2)

/-- The near box of radius `r`, `[0,r]^4`. -/
def nearCellBox (r : ℝ) : Set (Fin 4 → ℝ) := cellBox 0 r

/-- The far shell at radius `r`. -/
def farCellShell (r : ℝ) : Set (Fin 4 → ℝ) := brillouinCell \ nearCellBox r

lemma measurableSet_cellBox (a b : ℝ) : MeasurableSet (cellBox a b) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

lemma volume_cellBox_toReal {r : ℝ} (hr : 0 ≤ r) :
    (volume (cellBox 0 r)).toReal = r ^ 4 := by
  rw [cellBox, MeasureTheory.volume_pi_pi]
  simp [Real.volume_Icc, ← ENNReal.ofReal_pow hr]
  positivity

lemma volume_cellBox_ne_top (r : ℝ) : volume (cellBox 0 r) ≠ ⊤ := by
  rw [cellBox, MeasureTheory.volume_pi_pi]; simp [Real.volume_Icc]

/-- The Brillouin cell has measure `1/16`. -/
theorem volume_brillouinCell : (volume brillouinCell).toReal = 1 / 16 := by
  rw [brillouinCell, volume_cellBox_toReal (by norm_num : (0:ℝ) ≤ 1/2)]
  norm_num

lemma nearCellBox_subset {r : ℝ} (h : r ≤ 1 / 2) : nearCellBox r ⊆ brillouinCell := by
  intro p hp i _
  exact ⟨(hp i (Set.mem_univ i)).1, le_trans (hp i (Set.mem_univ i)).2 h⟩

lemma volume_nearCellBox_toReal {r : ℝ} (hr : 0 ≤ r) :
    (volume (nearCellBox r)).toReal = r ^ 4 := volume_cellBox_toReal hr

lemma volume_nearCellBox_ne_top (r : ℝ) : volume (nearCellBox r) ≠ ⊤ :=
  volume_cellBox_ne_top r

lemma volume_brillouinCell_ne_top : volume brillouinCell ≠ ⊤ :=
  volume_cellBox_ne_top (1 / 2)

/-- The far shell measure is `1/16 − r^4`. -/
theorem volume_farCellShell {r : ℝ} (h0 : 0 ≤ r) (h : r ≤ 1 / 2) :
    (volume (farCellShell r)).toReal = 1 / 16 - r ^ 4 := by
  have hsub := nearCellBox_subset h
  rw [farCellShell,
    measure_diff hsub (measurableSet_cellBox 0 r).nullMeasurableSet
      (volume_nearCellBox_ne_top r),
    ENNReal.toReal_sub_of_le (measure_mono hsub) volume_brillouinCell_ne_top,
    volume_nearCellBox_toReal h0, volume_brillouinCell]

/-! ## 2. The shell bound -/

/-- **Cell shell bound.**  A pointwise lower bound `−bn` on the near box and
`−bf` on the far shell integrate to a lower bound for the cell integral of the
orbit density, with the two exact box measures `r^4` and `1/16 − r^4`.

No abstract functional, no assumed additivity: this is the Lebesgue integral. -/
theorem shell_lower_bound {r bn bf : ℝ} (h0 : 0 ≤ r) (h : r ≤ 1 / 2)
    {d : (Fin 4 → ℝ) → ℝ} (hint : IntegrableOn d brillouinCell volume)
    (hnear : ∀ p ∈ nearCellBox r, -bn ≤ d p)
    (hfar : ∀ p ∈ farCellShell r, -bf ≤ d p) :
    -(r ^ 4 * bn + (1 / 16 - r ^ 4) * bf) ≤ ∫ p in brillouinCell, d p := by
  have hsub : nearCellBox r ⊆ brillouinCell := nearCellBox_subset h
  have hmeasN : MeasurableSet (nearCellBox r) := measurableSet_cellBox 0 r
  have hmeasC : MeasurableSet brillouinCell := measurableSet_cellBox 0 (1/2)
  have hmeasF : MeasurableSet (farCellShell r) := hmeasC.diff hmeasN
  have hunion : nearCellBox r ∪ farCellShell r = brillouinCell :=
    Set.union_diff_cancel hsub
  have hdisj : Disjoint (nearCellBox r) (farCellShell r) := Set.disjoint_sdiff_right
  have hintN : IntegrableOn d (nearCellBox r) volume := hint.mono_set hsub
  have hintF : IntegrableOn d (farCellShell r) volume := hint.mono_set Set.diff_subset
  have hNtop : volume (nearCellBox r) ≠ ⊤ := volume_cellBox_ne_top r
  have hFtop : volume (farCellShell r) ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_cellBox_ne_top (1/2)) (measure_mono Set.diff_subset)
  have hsplit : ∫ p in brillouinCell, d p
      = (∫ p in nearCellBox r, d p) + ∫ p in farCellShell r, d p := by
    conv_lhs => rw [← hunion]
    rw [setIntegral_union hdisj hmeasF hintN hintF]
  have hNbound : -(r ^ 4 * bn) ≤ ∫ p in nearCellBox r, d p := by
    have hc : IntegrableOn (fun _ : Fin 4 → ℝ => -bn) (nearCellBox r) volume :=
      integrableOn_const (hs := hNtop)
    have hmono := setIntegral_mono_on hc hintN hmeasN hnear
    rw [setIntegral_const] at hmono
    have hval : (volume.real (nearCellBox r)) • (-bn) = -(r ^ 4 * bn) := by
      rw [smul_eq_mul, MeasureTheory.measureReal_def, volume_nearCellBox_toReal h0]
      ring
    linarith [hmono, hval.le, hval.ge]
  have hFbound : -((1 / 16 - r ^ 4) * bf) ≤ ∫ p in farCellShell r, d p := by
    have hc : IntegrableOn (fun _ : Fin 4 → ℝ => -bf) (farCellShell r) volume :=
      integrableOn_const (hs := hFtop)
    have hmono := setIntegral_mono_on hc hintF hmeasF hfar
    rw [setIntegral_const] at hmono
    have hval : (volume.real (farCellShell r)) • (-bf) = -((1 / 16 - r ^ 4) * bf) := by
      rw [smul_eq_mul, MeasureTheory.measureReal_def, volume_farCellShell h0 h]
      ring
    linarith [hmono, hval.le, hval.ge]
  linarith [hsplit.le, hsplit.ge, hNbound, hFbound]

/-! ## 3. The budget at the working radius `r = 2/5` -/

/-- The hypercubic four-orbit multiplicities `(4,6,4,1)` sum to `15`; the
cancellation-preserving gate consumes the *combined* density, so a common
per-orbit bound `u` gives a combined bound `15 u`. -/
noncomputable def combinedOfPerOrbit (u : ℝ) : ℝ := 15 * u

/-- The near per-orbit bound proved in `NearFarRegions.lean`. -/
noncomputable def perOrbitNearBound : ℝ := 2 / 5

/-- The far per-orbit bound proved in `NearFarRegions.lean` (unit numerator). -/
noncomputable def perOrbitFarBound : ℝ := 25 / 64

/-- The shell budget available to Row A1 for the SU(2) normalisation. -/
noncomputable def shellBudgetSU2 : ℝ := 11 / 12

/-- The total cost of the near/far split at radius `r`. -/
noncomputable def splitCost (r : ℝ) : ℝ :=
  r ^ 4 * combinedOfPerOrbit perOrbitNearBound
    + (1 / 16 - r ^ 4) * combinedOfPerOrbit perOrbitFarBound

/-- **The budget passes at `r = 2/5`,** with the Jordan-sharpened far constant:
`(2/5)^4 · 6 + (1/16 − (2/5)^4) · 375/64 = 0.3698… < 11/12`. -/
theorem splitCost_two_fifths_lt_budget : splitCost (2 / 5) < shellBudgetSU2 := by
  unfold splitCost combinedOfPerOrbit perOrbitNearBound perOrbitFarBound shellBudgetSU2
  norm_num

/-- Even twice the split cost fits inside the shell budget: the margin is better
than a factor two. -/
theorem splitCost_two_fifths_double_lt_budget :
    2 * splitCost (2 / 5) < shellBudgetSU2 := by
  unfold splitCost combinedOfPerOrbit perOrbitNearBound perOrbitFarBound shellBudgetSU2
  norm_num

/-- The composed A1a statement: pointwise near and far per-orbit bounds at
radius `2/5` give the cell shell bound with a *number*, and that number is
strictly inside the shell budget. -/
theorem A1a_shell_bound_sharp
    {d : (Fin 4 → ℝ) → ℝ} (hint : IntegrableOn d brillouinCell volume)
    (hnear : ∀ p ∈ nearCellBox (2 / 5),
      -combinedOfPerOrbit perOrbitNearBound ≤ d p)
    (hfar : ∀ p ∈ farCellShell (2 / 5),
      -combinedOfPerOrbit perOrbitFarBound ≤ d p) :
    -splitCost (2 / 5) ≤ ∫ p in brillouinCell, d p := by
  have h := shell_lower_bound (r := 2/5) (by norm_num) (by norm_num) hint hnear hfar
  unfold splitCost
  linarith

/-- The same bound compared with the available shell budget. -/
theorem A1a_shell_bound_at_two_fifths
    {d : (Fin 4 → ℝ) → ℝ} (hint : IntegrableOn d brillouinCell volume)
    (hnear : ∀ p ∈ nearCellBox (2 / 5),
      -combinedOfPerOrbit perOrbitNearBound ≤ d p)
    (hfar : ∀ p ∈ farCellShell (2 / 5),
      -combinedOfPerOrbit perOrbitFarBound ≤ d p) :
    -shellBudgetSU2 < ∫ p in brillouinCell, d p := by
  have h := A1a_shell_bound_sharp hint hnear hfar
  have hb := splitCost_two_fifths_lt_budget
  linarith

end YangMills
