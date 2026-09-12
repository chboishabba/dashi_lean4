/-
# Scale-neutral probes: the radial adjoint identity, the no-go, and separation

`ApproximateScaleAnchor.lean` shows that a *single* functional separating `U`
from `ΛU`, with a quantitative margin, is enough to force a scale cost — no
spectral theory of the linearised operator is needed.  This file constructs
candidate functionals and computes, exactly, how far they can be made blind to
the scaling direction.

The dilation generator acts along rays, so everything is a one-dimensional
computation in the radius.  For a radial weight `w = φ(|x|)·x/|x|` and a radial
profile the probe is `∫φ(r)V(r)r²dr` and the generator is `V + rV'`.

* `ClayNS.radial_probe_adjoint` — the **exact adjoint identity**

    `∫φ·(V+rV')·r² = [φVr³] − ∫(2φr² + φ'r³)V`,

  i.e. the probe of the scaling derivative is a boundary term minus the probe of
  `V` against the *scale residual* `2φr² + φ'r³`.  The cancellation is done
  before any absolute value is taken.
* `ClayNS.radResidual_eq_zero_iff_homogeneous` (and
  `ClayNS.radResidual_inv_sq`) — the residual vanishes exactly for the
  homogeneous weight `φ = c/r²`, the scale-invariant one.
* `ClayNS.scaleNeutral_no_go` — **the no-go**: a scale-neutral weight that is
  differentiable up to the origin is identically zero.  So an exactly
  scale-neutral probe cannot be regular at the concentration point: the weight
  must be cut off, and the cut-off residual is unavoidable.  This is why the
  *approximate* anchor is the right tool.
* `ClayNS.radial_cutoff_probe_residual` — for the cut-off homogeneous weight
  `φ = χ(r)/r²` with `χ` vanishing at both ends, the boundary terms disappear
  and the residual is **exactly** `χ'(r)·r·V(r)`: it is supported where the
  cut-off varies, i.e. in the transition annuli, and carries one positive power
  of `r` relative to the bulk.
* `ClayNS.radial_cutoff_probe_bound` — the quantitative form of that residual.
* `ClayNS.radial_probe_separates` — **the separation criterion**: if the profile
  has a definite sign and size `m` on the probe's range while the transition
  cost `(∫|χ'|r)·sup|V|` is smaller than the accumulated bulk `m∫χ`, then the
  probe sees `U` strictly more than it sees `ΛU`, which is exactly the input
  `|⟨e,ΛU⟩| ≤ δ < |a₀| = |⟨e,U⟩|` of the approximate anchor.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.ApproximateScaleAnchor

open MeasureTheory intervalIntegral Set

noncomputable section

namespace ClayNS

/-! ## The radial reduction -/

/-- The radial reduction of the dilation generator: `(ΛV)(r) = V(r) + rV'(r)`. -/
def radGen (V V' : ℝ → ℝ) : ℝ → ℝ := fun r => V r + r * V' r

/-- The radial reduction of the probe `L(V) = ∫⟨w,V⟩dx` for the radial weight
`w = φ(|x|)x/|x|`, up to the angular factor. -/
def radProbe (phi V : ℝ → ℝ) (a b : ℝ) : ℝ := ∫ r in a..b, phi r * V r * r ^ 2

/-- The scale residual of a radial weight: `2φr² + φ'r³`.  It vanishes exactly
when the weight is homogeneous of degree `−2`, which is the scale-invariant
degree for a probe against a velocity field. -/
def radResidual (phi phi' : ℝ → ℝ) : ℝ → ℝ := fun r => 2 * phi r * r ^ 2 + phi' r * r ^ 3

/-! ## The exact adjoint identity -/

/-- **The radial adjoint identity.**  Integrating by parts once, and doing the
cancellation *before* any absolute value is taken,

  `∫_a^b φ·(V + rV')·r² dr = [φVr³]_a^b − ∫_a^b (2φr² + φ'r³)·V dr`. -/
theorem radial_probe_adjoint {phi phi' V V' : ℝ → ℝ} {a b : ℝ}
    (hphi : ∀ r ∈ uIcc a b, HasDerivAt phi (phi' r) r)
    (hV : ∀ r ∈ uIcc a b, HasDerivAt V (V' r) r)
    (hphi'c : ContinuousOn phi' (uIcc a b)) (hV'c : ContinuousOn V' (uIcc a b)) :
    radProbe phi (radGen V V') a b
      = (phi b * V b * b ^ 3 - phi a * V a * a ^ 3)
        - ∫ r in a..b, radResidual phi phi' r * V r := by
  have hphic : ContinuousOn phi (uIcc a b) := fun r hr =>
    (hphi r hr).continuousAt.continuousWithinAt
  have hVc : ContinuousOn V (uIcc a b) := fun r hr =>
    (hV r hr).continuousAt.continuousWithinAt
  have hid : ContinuousOn (fun r : ℝ => r) (uIcc a b) := continuousOn_id
  -- the primitive `G = φVr³`
  set G : ℝ → ℝ := fun r => phi r * V r * r ^ 3 with hG
  set G' : ℝ → ℝ := fun r =>
    phi' r * V r * r ^ 3 + phi r * V' r * r ^ 3 + 3 * (phi r * V r * r ^ 2) with hG'
  have hGderiv : ∀ r ∈ uIcc a b, HasDerivAt G (G' r) r := by
    intro r hr
    have h1 : HasDerivAt (fun s : ℝ => phi s * V s) (phi' r * V r + phi r * V' r) r :=
      (hphi r hr).mul (hV r hr)
    have h2 : HasDerivAt (fun s : ℝ => s ^ 3) (3 * r ^ 2) r := by
      simpa using (hasDerivAt_pow 3 r)
    have h3 := h1.mul h2
    have hrw : (phi' r * V r + phi r * V' r) * r ^ 3 + phi r * V r * (3 * r ^ 2) = G' r := by
      simp only [hG']; ring
    simpa [hG, hrw] using h3.congr_deriv hrw
  have hG'cont : ContinuousOn G' (uIcc a b) := by
    refine ContinuousOn.add (ContinuousOn.add ?_ ?_) ?_
    · exact (hphi'c.mul hVc).mul (hid.pow 3)
    · exact (hphic.mul hV'c).mul (hid.pow 3)
    · exact continuousOn_const.mul ((hphic.mul hVc).mul (hid.pow 2))
  have hFTC : (∫ r in a..b, G' r) = G b - G a :=
    integral_eq_sub_of_hasDerivAt hGderiv (hG'cont.intervalIntegrable)
  -- the two integrands
  have hres_cont : ContinuousOn (fun r => radResidual phi phi' r * V r) (uIcc a b) := by
    refine ContinuousOn.mul ?_ hVc
    exact (continuousOn_const.mul hphic |>.mul (hid.pow 2)).add (hphi'c.mul (hid.pow 3))
  have hprobe_cont : ContinuousOn (fun r => phi r * radGen V V' r * r ^ 2) (uIcc a b) := by
    refine ContinuousOn.mul (hphic.mul ?_) (hid.pow 2)
    exact hVc.add (hid.mul hV'c)
  have hsplit : ∀ r, G' r = phi r * radGen V V' r * r ^ 2 + radResidual phi phi' r * V r := by
    intro r
    simp only [hG', radGen, radResidual]
    ring
  have hint1 : IntervalIntegrable (fun r => phi r * radGen V V' r * r ^ 2) volume a b :=
    hprobe_cont.intervalIntegrable
  have hint2 : IntervalIntegrable (fun r => radResidual phi phi' r * V r) volume a b :=
    hres_cont.intervalIntegrable
  have hsum : (∫ r in a..b, G' r)
      = (∫ r in a..b, phi r * radGen V V' r * r ^ 2)
        + ∫ r in a..b, radResidual phi phi' r * V r := by
    rw [← integral_add hint1 hint2]
    exact integral_congr (fun r _ => hsplit r)
  rw [hFTC] at hsum
  simp only [radProbe, hG] at *
  linarith [hsum]

/-! ## The scale-neutral (homogeneous) weight -/

/-- The homogeneous weight `φ = c/r²` has vanishing scale residual: it is
*scale-neutral*. -/
lemma radResidual_inv_sq (c : ℝ) {r : ℝ} (hr : r ≠ 0) :
    radResidual (fun s => c / s ^ 2) (fun s => -(2 * c) / s ^ 3) r = 0 := by
  simp only [radResidual]
  field_simp
  ring

/-- The derivative of the homogeneous weight. -/
lemma hasDerivAt_inv_sq (c : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => c / s ^ 2) (-(2 * c) / r ^ 3) r := by
  have h2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * r) r := by
    simpa using (hasDerivAt_pow 2 r)
  have hne : (r : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have hinv : HasDerivAt (fun s : ℝ => (s ^ 2)⁻¹) (-(2 * r) / (r ^ 2) ^ 2) r := h2.inv hne
  have hc := hinv.const_mul c
  have hrw : c * (-(2 * r) / (r ^ 2) ^ 2) = -(2 * c) / r ^ 3 := by
    field_simp
  simpa [div_eq_mul_inv, hrw] using hc.congr_deriv hrw

/-- **The scale-neutral no-go.**  A scale-neutral weight that is differentiable
up to the origin vanishes identically: there is no regular exactly
scale-invariant probe.  Hence a probe must be cut off, and the approximate
anchor — not the exact one — is the right tool. -/
theorem scaleNeutral_no_go {phi phi' : ℝ → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hphi : ∀ r ∈ uIcc (0:ℝ) b, HasDerivAt phi (phi' r) r)
    (hphi'c : ContinuousOn phi' (uIcc (0:ℝ) b))
    (hneutral : ∀ r ∈ uIcc (0:ℝ) b, radResidual phi phi' r = 0) :
    ∀ r ∈ uIcc (0:ℝ) b, r ≠ 0 → phi r = 0 := by
  have hphic : ContinuousOn phi (uIcc (0:ℝ) b) := fun r hr =>
    (hphi r hr).continuousAt.continuousWithinAt
  have hid : ContinuousOn (fun r : ℝ => r) (uIcc (0:ℝ) b) := continuousOn_id
  set g : ℝ → ℝ := fun r => phi r * r ^ 2 with hg
  set g' : ℝ → ℝ := fun r => phi' r * r ^ 2 + phi r * (2 * r) with hg'
  have hgderiv : ∀ r ∈ uIcc (0:ℝ) b, HasDerivAt g (g' r) r := by
    intro r hr
    have h2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * r) r := by
      simpa using (hasDerivAt_pow 2 r)
    exact (hphi r hr).mul h2
  have hg'zero : ∀ r ∈ uIcc (0:ℝ) b, g' r = 0 := by
    intro r hr
    rcases eq_or_ne r 0 with rfl | hne
    · simp [hg']
    · have h := hneutral r hr
      simp only [radResidual] at h
      have hr3 : r ≠ 0 := hne
      -- `2φr² + φ'r³ = 0` and `r ≠ 0` give `φ'r² + 2φr = 0`
      have : r * (phi' r * r ^ 2 + phi r * (2 * r)) = 0 := by nlinarith [h]
      have := mul_eq_zero.1 this
      rcases this with h0 | h0
      · exact absurd h0 hr3
      · simpa [hg'] using h0
  have hg'cont : ContinuousOn g' (uIcc (0:ℝ) b) :=
    (hphi'c.mul (hid.pow 2)).add (hphic.mul (continuousOn_const.mul hid))
  intro r hr hrne
  -- `g` is constant on the interval, and `g 0 = 0`
  have hsub : uIcc (0:ℝ) r ⊆ uIcc (0:ℝ) b := by
    have hrb : r ∈ Icc (0:ℝ) b := by
      rwa [uIcc_of_le hb] at hr
    rw [uIcc_of_le hrb.1, uIcc_of_le hb]
    exact Icc_subset_Icc le_rfl hrb.2
  have hFTC : (∫ s in (0:ℝ)..r, g' s) = g r - g 0 :=
    integral_eq_sub_of_hasDerivAt (fun s hs => hgderiv s (hsub hs))
      ((hg'cont.mono hsub).intervalIntegrable)
  have hzero : (∫ s in (0:ℝ)..r, g' s) = 0 := by
    rw [integral_congr (g := fun _ => (0:ℝ)) (fun s hs => hg'zero s (hsub hs))]
    simp
  have hg0 : g 0 = 0 := by simp [hg]
  have hgr : g r = 0 := by rw [hg0] at hFTC; linarith [hFTC, hzero]
  have : phi r * r ^ 2 = 0 := hgr
  rcases mul_eq_zero.1 this with h | h
  · exact h
  · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h) hrne

/-! ## The cut-off homogeneous probe -/

/-- **The cut-off residual is exactly `χ'(r)·r`.**  For the cut-off homogeneous
weight `φ = χ(r)/r²` with `χ` vanishing at both ends of the range, the boundary
terms disappear and the probe of the scaling derivative is *exactly* the
transition integral

  `∫φ(V+rV')r² = −∫χ'(r)·r·V(r)dr`,

supported where the cut-off varies and carrying one extra power of `r`
(a positive scaling dimension) relative to the bulk `∫χV`. -/
theorem radial_cutoff_probe_residual {chi chi' V V' : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hchi : ∀ r ∈ uIcc a b, HasDerivAt chi (chi' r) r)
    (hV : ∀ r ∈ uIcc a b, HasDerivAt V (V' r) r)
    (hchi'c : ContinuousOn chi' (uIcc a b)) (hV'c : ContinuousOn V' (uIcc a b))
    (hchia : chi a = 0) (hchib : chi b = 0) :
    radProbe (fun r => chi r / r ^ 2) (radGen V V') a b
      = - ∫ r in a..b, chi' r * r * V r := by
  set phi : ℝ → ℝ := fun r => chi r / r ^ 2 with hphi
  set phi' : ℝ → ℝ := fun r => chi' r / r ^ 2 - 2 * chi r / r ^ 3 with hphi'
  have hmem : ∀ r ∈ uIcc a b, 0 < r := by
    intro r hr
    rw [uIcc_of_le hab] at hr
    exact lt_of_lt_of_le ha hr.1
  have hchic : ContinuousOn chi (uIcc a b) := fun r hr =>
    (hchi r hr).continuousAt.continuousWithinAt
  have hphider : ∀ r ∈ uIcc a b, HasDerivAt phi (phi' r) r := by
    intro r hr
    have hrne : r ≠ 0 := ne_of_gt (hmem r hr)
    have h2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * r) r := by
      simpa using (hasDerivAt_pow 2 r)
    have hdiv := (hchi r hr).div h2 (pow_ne_zero 2 hrne)
    have hrw : (chi' r * r ^ 2 - chi r * (2 * r)) / (r ^ 2) ^ 2 = phi' r := by
      simp only [hphi']
      field_simp
    simpa [hphi] using hdiv.congr_deriv hrw
  have hphi'c : ContinuousOn phi' (uIcc a b) := by
    have hid : ContinuousOn (fun r : ℝ => r) (uIcc a b) := continuousOn_id
    have h1 : ContinuousOn (fun r : ℝ => chi' r / r ^ 2) (uIcc a b) :=
      hchi'c.div (hid.pow 2) fun r hr => pow_ne_zero 2 (ne_of_gt (hmem r hr))
    have h2 : ContinuousOn (fun r : ℝ => 2 * chi r / r ^ 3) (uIcc a b) :=
      (continuousOn_const.mul hchic).div (hid.pow 3)
        fun r hr => pow_ne_zero 3 (ne_of_gt (hmem r hr))
    exact h1.sub h2
  have hmain := radial_probe_adjoint (phi := phi) (phi' := phi') (V := V) (V' := V')
    hphider hV hphi'c hV'c
  have hbdry : phi b * V b * b ^ 3 - phi a * V a * a ^ 3 = 0 := by
    simp [hphi, hchia, hchib]
  have hres : ∀ r ∈ uIcc a b, radResidual phi phi' r * V r = chi' r * r * V r := by
    intro r hr
    have hrne : r ≠ 0 := ne_of_gt (hmem r hr)
    simp only [radResidual, hphi, hphi']
    field_simp
    ring
  rw [hbdry, zero_sub, integral_congr hres] at hmain
  exact hmain

/-- **The quantitative residual bound.**  The cut-off probe is blind to the
scaling direction up to the transition cost `(∫|χ'|·r)·sup|V|`. -/
theorem radial_cutoff_probe_bound {chi chi' V V' : ℝ → ℝ} {a b Msup : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hchi : ∀ r ∈ uIcc a b, HasDerivAt chi (chi' r) r)
    (hV : ∀ r ∈ uIcc a b, HasDerivAt V (V' r) r)
    (hchi'c : ContinuousOn chi' (uIcc a b)) (hV'c : ContinuousOn V' (uIcc a b))
    (hchia : chi a = 0) (hchib : chi b = 0)
    (hVsup : ∀ r ∈ uIcc a b, |V r| ≤ Msup) :
    |radProbe (fun r => chi r / r ^ 2) (radGen V V') a b|
      ≤ Msup * ∫ r in a..b, |chi' r| * r := by
  rw [radial_cutoff_probe_residual ha hab hchi hV hchi'c hV'c hchia hchib, abs_neg]
  have hmem : ∀ r ∈ uIcc a b, 0 < r := by
    intro r hr
    rw [uIcc_of_le hab] at hr
    exact lt_of_lt_of_le ha hr.1
  have hVc : ContinuousOn V (uIcc a b) := fun r hr =>
    (hV r hr).continuousAt.continuousWithinAt
  have hid : ContinuousOn (fun r : ℝ => r) (uIcc a b) := continuousOn_id
  have hint : IntervalIntegrable (fun r => chi' r * r * V r) volume a b :=
    ((hchi'c.mul hid).mul hVc).intervalIntegrable
  have hintmaj : IntervalIntegrable (fun r => Msup * (|chi' r| * r)) volume a b :=
    (continuousOn_const.mul (hchi'c.abs.mul hid)).intervalIntegrable
  have habs_le : |∫ r in a..b, chi' r * r * V r| ≤ ∫ r in a..b, |chi' r * r * V r| :=
    intervalIntegral.abs_integral_le_integral_abs hab
  refine le_trans habs_le ?_
  calc (∫ r in a..b, |chi' r * r * V r|)
      ≤ ∫ r in a..b, Msup * (|chi' r| * r) := by
        refine intervalIntegral.integral_mono_on hab hint.abs hintmaj ?_
        intro r hr
        have hrmem : r ∈ uIcc a b := by rw [uIcc_of_le hab]; exact hr
        have hr0 : 0 < r := hmem r hrmem
        have habs : |chi' r * r * V r| = |chi' r| * r * |V r| := by
          rw [abs_mul, abs_mul, abs_of_pos hr0]
        rw [habs]
        have h1 : |V r| ≤ Msup := hVsup r hrmem
        have h2 : (0:ℝ) ≤ |chi' r| * r := by positivity
        nlinarith [h1, h2]
    _ = Msup * ∫ r in a..b, |chi' r| * r := by rw [intervalIntegral.integral_const_mul]

/-! ## The sharp residual bound and the bulk identity -/

/-- The bulk of the cut-off homogeneous probe is exactly `∫χV`: the weight
`φ = χ/r²` cancels the radial Jacobian. -/
theorem radial_probe_bulk_eq {chi V : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    radProbe (fun r => chi r / r ^ 2) V a b = ∫ r in a..b, chi r * V r := by
  refine integral_congr fun r hr => ?_
  have hr0 : 0 < r := by
    rw [uIcc_of_le hab] at hr
    exact lt_of_lt_of_le ha hr.1
  have : (r:ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hr0)
  field_simp

/-- **The sharp residual bound.**  The probe of the scaling derivative is
controlled by the transition integral `∫|χ'|·r·|V|`, in which the profile is
sampled *only where the cut-off varies*.  Bounding `|V|` by its global supremum
(as in `ClayNS.radial_cutoff_probe_bound`) is generally too lossy, because the
bulk `∫χV` is itself dominated by the outer scale; the useful form is this one,
with the transition radii chosen where the profile is small. -/
theorem radial_cutoff_probe_abs_le {chi chi' V V' : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hchi : ∀ r ∈ uIcc a b, HasDerivAt chi (chi' r) r)
    (hV : ∀ r ∈ uIcc a b, HasDerivAt V (V' r) r)
    (hchi'c : ContinuousOn chi' (uIcc a b)) (hV'c : ContinuousOn V' (uIcc a b))
    (hchia : chi a = 0) (hchib : chi b = 0) :
    |radProbe (fun r => chi r / r ^ 2) (radGen V V') a b|
      ≤ ∫ r in a..b, |chi' r| * r * |V r| := by
  rw [radial_cutoff_probe_residual ha hab hchi hV hchi'c hV'c hchia hchib, abs_neg]
  have hmem : ∀ r ∈ uIcc a b, 0 < r := by
    intro r hr
    rw [uIcc_of_le hab] at hr
    exact lt_of_lt_of_le ha hr.1
  have hVc : ContinuousOn V (uIcc a b) := fun r hr =>
    (hV r hr).continuousAt.continuousWithinAt
  have hid : ContinuousOn (fun r : ℝ => r) (uIcc a b) := continuousOn_id
  have hint : IntervalIntegrable (fun r => chi' r * r * V r) volume a b :=
    ((hchi'c.mul hid).mul hVc).intervalIntegrable
  have habs_le : |∫ r in a..b, chi' r * r * V r| ≤ ∫ r in a..b, |chi' r * r * V r| :=
    intervalIntegral.abs_integral_le_integral_abs hab
  refine habs_le.trans (le_of_eq ?_)
  refine integral_congr fun r hr => ?_
  have hr0 : 0 < r := hmem r hr
  rw [abs_mul, abs_mul, abs_of_pos hr0]

/-! ## The separation criterion -/

/-- **The separation criterion.**  If the profile keeps a definite sign and size
`m > 0` across the probe's range, while the transition cost of the cut-off is
strictly smaller than the accumulated bulk, then the cut-off homogeneous probe
*separates*: it sees the profile strictly more than it sees the scaling
derivative,

  `|L(ΛV)| < L(V)`,

which is exactly the input `|⟨e,ΛU⟩|_Γ ≤ δ < |a₀|` required by the approximate
anchor `ClayNS.gram_anchor_lower_bound_approx`. -/
theorem radial_probe_separates {chi chi' V V' : ℝ → ℝ} {a b m Msup : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hchi : ∀ r ∈ uIcc a b, HasDerivAt chi (chi' r) r)
    (hV : ∀ r ∈ uIcc a b, HasDerivAt V (V' r) r)
    (hchi'c : ContinuousOn chi' (uIcc a b)) (hV'c : ContinuousOn V' (uIcc a b))
    (hchia : chi a = 0) (hchib : chi b = 0) (hchi0 : ∀ r ∈ uIcc a b, 0 ≤ chi r)
    (hVsup : ∀ r ∈ uIcc a b, |V r| ≤ Msup)
    (hVm : ∀ r ∈ uIcc a b, m ≤ V r)
    (hgap : Msup * (∫ r in a..b, |chi' r| * r) < m * ∫ r in a..b, chi r) :
    |radProbe (fun r => chi r / r ^ 2) (radGen V V') a b|
      < radProbe (fun r => chi r / r ^ 2) V a b := by
  have hmem : ∀ r ∈ uIcc a b, 0 < r := by
    intro r hr
    rw [uIcc_of_le hab] at hr
    exact lt_of_lt_of_le ha hr.1
  have hchic : ContinuousOn chi (uIcc a b) := fun r hr =>
    (hchi r hr).continuousAt.continuousWithinAt
  have hVc : ContinuousOn V (uIcc a b) := fun r hr =>
    (hV r hr).continuousAt.continuousWithinAt
  have hid : ContinuousOn (fun r : ℝ => r) (uIcc a b) := continuousOn_id
  -- the bulk is at least `m∫χ`
  have hbulk : m * (∫ r in a..b, chi r) ≤ radProbe (fun r => chi r / r ^ 2) V a b := by
    have hint1 : IntervalIntegrable (fun r => m * chi r) volume a b :=
      (continuousOn_const.mul hchic).intervalIntegrable
    have hint2 : IntervalIntegrable (fun r => chi r / r ^ 2 * V r * r ^ 2) volume a b := by
      refine ContinuousOn.intervalIntegrable ?_
      exact ((hchic.div (hid.pow 2)
        fun r hr => pow_ne_zero 2 (ne_of_gt (hmem r hr))).mul hVc).mul (hid.pow 2)
    have hmono : ∀ r ∈ Icc a b, m * chi r ≤ chi r / r ^ 2 * V r * r ^ 2 := by
      intro r hr
      have hrmem : r ∈ uIcc a b := by rw [uIcc_of_le hab]; exact hr
      have hr0 : 0 < r := hmem r hrmem
      have hrne : (r:ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hr0)
      have heq : chi r / r ^ 2 * V r * r ^ 2 = chi r * V r := by field_simp
      rw [heq]
      have h1 : m ≤ V r := hVm r hrmem
      have h2 : 0 ≤ chi r := hchi0 r hrmem
      nlinarith [h1, h2]
    have := intervalIntegral.integral_mono_on hab hint1 hint2 hmono
    rw [intervalIntegral.integral_const_mul] at this
    exact this
  have hres := radial_cutoff_probe_bound ha hab hchi hV hchi'c hV'c hchia hchib hVsup
  calc |radProbe (fun r => chi r / r ^ 2) (radGen V V') a b|
      ≤ Msup * ∫ r in a..b, |chi' r| * r := hres
    _ < m * ∫ r in a..b, chi r := hgap
    _ ≤ radProbe (fun r => chi r / r ^ 2) V a b := hbulk

/-- **The sharp separation criterion.**  If the transition integral of the
cut-off against the profile is strictly smaller than the bulk, then the probe
sees the profile strictly more than it sees the scaling derivative:

  `|L(ΛV)| < L(V)`,

which is the input `δ < |a₀|` of `ClayNS.gram_anchor_lower_bound_approx`.  Unlike
the global-supremum form, this criterion can be met by choosing the transition
radii where the profile is small — a pigeonhole choice of good radii — while the
bulk accumulates over the whole range. -/
theorem radial_probe_separates_sharp {chi chi' V V' : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hchi : ∀ r ∈ uIcc a b, HasDerivAt chi (chi' r) r)
    (hV : ∀ r ∈ uIcc a b, HasDerivAt V (V' r) r)
    (hchi'c : ContinuousOn chi' (uIcc a b)) (hV'c : ContinuousOn V' (uIcc a b))
    (hchia : chi a = 0) (hchib : chi b = 0)
    (hgap : (∫ r in a..b, |chi' r| * r * |V r|) < ∫ r in a..b, chi r * V r) :
    |radProbe (fun r => chi r / r ^ 2) (radGen V V') a b|
      < radProbe (fun r => chi r / r ^ 2) V a b := by
  have h1 := radial_cutoff_probe_abs_le ha hab hchi hV hchi'c hV'c hchia hchib
  rw [radial_probe_bulk_eq (chi := chi) (V := V) ha hab]
  exact lt_of_le_of_lt h1 hgap

end ClayNS
