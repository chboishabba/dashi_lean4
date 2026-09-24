/-
# `A-anchor`: the anchored scale-Gram coercivity inequality

`GaussianScaleGram.lean` proves the unconditional geometry of the weighted Gram
pair `(u, Λu)`: the defect `Δ = AB − C²` is nonnegative and equals `A` times the
squared weighted distance of `Λu` to the line `ℝ·u`.  What it does *not* provide
is a **quantitative** lower bound: without one, the dichotomy

  `Δ ≥ εA`  or  `Λu ≈ cu`

carries no information about which branch occurs.

The zeta geometry supplies the missing pattern.  There, a *fixed coordinate*
anchors the transverse direction and yields

  `AB − C² ≥ a₀²B`.

This file proves the exact analogue for the weighted `L²` Gram pair of vector
fields.  The input is an **anchor mode** `e`: a weighted-`L²`-normalized field
with

* `⟨e, Λu⟩_Γ = 0`  — the scaling derivative has no component along the anchor;
* `⟨e, u⟩_Γ = a₀`  — the profile does, by the record-point normalization.

Then no multiple `cΛu` can approximate `u` better than `a₀`, so the weighted
distance from `u` to the line `ℝ·Λu` is at least `a₀`, and since the Gram
determinant equals that squared distance times `B`,

  `Δ ≥ a₀²·B`.                                                          (A-anchor)

Results:

* `ClayNS.gramC_comm` — symmetry of the weighted pairing;
* `ClayNS.gramA_sub_eq` — the quadratic expansion of `‖u − cΛu‖²_Γ`
  (the companion of `gram_deficit_identity`, with the roles exchanged);
* `ClayNS.gram_anchor_lower_bound` — **(A-anchor)** `a₀²B ≤ Δ`;
* `ClayNS.scaleGramDefect_anchor_lower_bound` — its instance for the parabolic
  scaling generator `Λ`;
* `ClayNS.scale_defect_ge_transverse` — the complementary form
  `Δ ≥ c·‖P_⊥Λu‖²_Γ` from any lower bound `c ≤ A` on the weighted mass of the
  profile;
* `ClayNS.gramA_ge_of_lower_bound_on_set` — the record-point normalization
  producing such a `c`: if `|u|² ≥ m` and `Γ ≥ γ` on a set `S`, then
  `A ≥ γ·m·μ(S)`;
* `ClayNS.scaleGram_anchored_dichotomy` — the quantitative dichotomy: either the
  scaling motion is transverse and pays a scale cost bounded below by the
  anchor, or the scaling derivative is genuinely close to a multiple of the
  profile, with an explicit smallness threshold.

Nothing is postulated: every statement is an unconditional consequence of the
weighted Cauchy–Schwarz inequality already proved in `GaussianScaleGram.lean`.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.GaussianScaleGram

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace ClayNS

variable {α : Type*} [MeasurableSpace α]

/-! ## Elementary algebra of the weighted Gram data -/

/-- The weighted pairing is symmetric. -/
lemma gramC_comm (μ : Measure α) (Gam : α → ℝ) (f g : α → E3) :
    gramC μ Gam f g = gramC μ Gam g f := by
  unfold gramC
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Fin.sum_univ_three]
  ring

/-- The `c`-parametrized combination `u − cΛu`, as a field. -/
def gramSub (f g : α → E3) (c : ℝ) : α → E3 := fun x => f x - c • g x

omit [MeasurableSpace α] in
@[simp] lemma gramSub_apply (f g : α → E3) (c : ℝ) (x : α) (a : Fin 3) :
    gramSub f g c x a = f x a - c * g x a := by
  simp [gramSub]

/-- The quadratic expansion of the weighted mass of `u − cΛu`. -/
lemma gramA_sub_eq {μ : Measure α} {Gam : α → ℝ} {f g : α → E3}
    (hf : Integrable (fun x => Gam x * ∑ a, (f x a) ^ 2) μ)
    (hg : Integrable (fun x => Gam x * ∑ a, (g x a) ^ 2) μ)
    (hfg : Integrable (fun x => Gam x * ∑ a, f x a * g x a) μ) (c : ℝ) :
    gramA μ Gam (gramSub f g c)
      = gramA μ Gam f - 2 * c * gramC μ Gam f g + c ^ 2 * gramA μ Gam g := by
  have h := gram_deficit_identity (μ := μ) (Gam := Gam) (f := g) (g := f) hg hf
    (hfg.congr (Filter.Eventually.of_forall fun x => by
      simp only [Fin.sum_univ_three]; ring)) c
  simpa [gramA, gramSub, gramC_comm μ Gam g f] using h

/-- Integrability of the weighted mass of `u − cΛu`. -/
lemma integrable_gramSub_sq {μ : Measure α} {Gam : α → ℝ} {f g : α → E3}
    (hf : Integrable (fun x => Gam x * ∑ a, (f x a) ^ 2) μ)
    (hg : Integrable (fun x => Gam x * ∑ a, (g x a) ^ 2) μ)
    (hfg : Integrable (fun x => Gam x * ∑ a, f x a * g x a) μ) (c : ℝ) :
    Integrable (fun x => Gam x * ∑ a, (gramSub f g c x a) ^ 2) μ := by
  have hcomb : Integrable (fun x => (Gam x * ∑ a, (f x a) ^ 2)
      - 2 * c * (Gam x * ∑ a, f x a * g x a)
      + c ^ 2 * (Gam x * ∑ a, (g x a) ^ 2)) μ :=
    (hf.sub (hfg.const_mul _)).add (hg.const_mul _)
  refine hcomb.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [gramSub_apply, Fin.sum_univ_three]
  ring

/-- Integrability of the weighted pairing of an anchor with `u − cΛu`. -/
lemma integrable_gramC_anchor_sub {μ : Measure α} {Gam : α → ℝ} {e f g : α → E3}
    (hef : Integrable (fun x => Gam x * ∑ a, e x a * f x a) μ)
    (heg : Integrable (fun x => Gam x * ∑ a, e x a * g x a) μ) (c : ℝ) :
    Integrable (fun x => Gam x * ∑ a, e x a * (gramSub f g c x a)) μ := by
  have hcomb : Integrable (fun x => (Gam x * ∑ a, e x a * f x a)
      - c * (Gam x * ∑ a, e x a * g x a)) μ := hef.sub (heg.const_mul _)
  refine hcomb.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [gramSub_apply, Fin.sum_univ_three]
  ring

/-- The weighted pairing of the anchor with `u − cΛu` splits. -/
lemma gramC_anchor_sub {μ : Measure α} {Gam : α → ℝ} {e f g : α → E3}
    (hef : Integrable (fun x => Gam x * ∑ a, e x a * f x a) μ)
    (heg : Integrable (fun x => Gam x * ∑ a, e x a * g x a) μ) (c : ℝ) :
    gramC μ Gam e (gramSub f g c) = gramC μ Gam e f - c * gramC μ Gam e g := by
  have hpt : ∀ x, Gam x * ∑ a, e x a * (gramSub f g c x a)
      = (Gam x * ∑ a, e x a * f x a) - c * (Gam x * ∑ a, e x a * g x a) := by
    intro x
    simp only [gramSub_apply, Fin.sum_univ_three]
    ring
  unfold gramC
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_sub hef (heg.const_mul _), integral_const_mul]

/-! ## The anchored coercivity inequality -/

/-- **`A-anchor`: the anchored scale-Gram coercivity inequality.**

Let `Γ ≥ 0` be a weight, `u` a profile, `g` its scaling derivative, and let `e`
be an *anchor mode*: a field of weighted mass at most one whose pairing with `g`
vanishes and whose pairing with `u` equals `a₀`.  Then the weighted Gram
determinant obeys

  `a₀²·‖g‖²_Γ ≤ Δ = ‖u‖²_Γ‖g‖²_Γ − ⟨u,g⟩²_Γ`,

the exact analogue of the zeta anchor inequality `AB − C² ≥ a₀²B`.

The mechanism is that no multiple of `g` can approximate `u` to weighted
distance smaller than `a₀`, because the anchor sees all of `u` and none of `g`;
and the Gram determinant is exactly that squared distance times `‖g‖²_Γ`. -/
theorem gram_anchor_lower_bound {μ : Measure α} {Gam : α → ℝ} {e f g : α → E3}
    (hGam : ∀ x, 0 ≤ Gam x)
    (hf : Integrable (fun x => Gam x * ∑ a, (f x a) ^ 2) μ)
    (hg : Integrable (fun x => Gam x * ∑ a, (g x a) ^ 2) μ)
    (hfg : Integrable (fun x => Gam x * ∑ a, f x a * g x a) μ)
    (he : Integrable (fun x => Gam x * ∑ a, (e x a) ^ 2) μ)
    (hef : Integrable (fun x => Gam x * ∑ a, e x a * f x a) μ)
    (heg : Integrable (fun x => Gam x * ∑ a, e x a * g x a) μ)
    (hnorm : gramA μ Gam e ≤ 1) (hperp : gramC μ Gam e g = 0) {a0 : ℝ}
    (hanchor : gramC μ Gam e f = a0) :
    a0 ^ 2 * gramA μ Gam g ≤ gramDefect μ Gam f g := by
  set A := gramA μ Gam f with hA
  set B := gramA μ Gam g with hB
  set C := gramC μ Gam f g with hC
  -- the anchored quadratic lower bound
  have hquad : ∀ c : ℝ, a0 ^ 2 ≤ A - 2 * c * C + c ^ 2 * B := by
    intro c
    have hw2 := integrable_gramSub_sq hf hg hfg c
    have hew := integrable_gramC_anchor_sub hef heg c
    -- weighted Cauchy–Schwarz for the pair `(e, u − cg)`
    have hcs : 0 ≤ gramDefect μ Gam e (gramSub f g c) :=
      gramDefect_nonneg hGam he hw2 hew
    have hval : gramC μ Gam e (gramSub f g c) = a0 := by
      rw [gramC_anchor_sub hef heg c, hperp, hanchor, mul_zero, sub_zero]
    have hmass : gramA μ Gam (gramSub f g c) = A - 2 * c * C + c ^ 2 * B :=
      gramA_sub_eq hf hg hfg c
    have hQ0 : 0 ≤ A - 2 * c * C + c ^ 2 * B := by
      rw [← hmass]; exact gramA_nonneg hGam _
    have hexp : a0 ^ 2 ≤ gramA μ Gam e * (A - 2 * c * C + c ^ 2 * B) := by
      have := hcs
      rw [gramDefect, hval, hmass] at this
      linarith
    have : gramA μ Gam e * (A - 2 * c * C + c ^ 2 * B)
        ≤ 1 * (A - 2 * c * C + c ^ 2 * B) := mul_le_mul_of_nonneg_right hnorm hQ0
    linarith [hexp, this]
  have hB0 : 0 ≤ B := gramA_nonneg hGam g
  rcases eq_or_lt_of_le hB0 with hB0' | hBpos
  · -- `B = 0` forces `C = 0`, and both sides vanish
    have hCzero : C = 0 := by
      have hd : 0 ≤ gramDefect μ Gam f g := gramDefect_nonneg hGam hf hg hfg
      rw [gramDefect, ← hA, ← hB, ← hC, ← hB0', mul_zero] at hd
      nlinarith [sq_nonneg C]
    simp [gramDefect, ← hA, ← hB, ← hC, ← hB0', hCzero]
  · have h := hquad (C / B)
    have hne : B ≠ 0 := ne_of_gt hBpos
    have hexp : A - 2 * (C / B) * C + (C / B) ^ 2 * B = A - C ^ 2 / B := by
      field_simp; ring
    rw [hexp] at h
    have h2 : C ^ 2 / B ≤ A - a0 ^ 2 := by linarith
    rw [div_le_iff₀ hBpos] at h2
    rw [gramDefect, ← hA, ← hB, ← hC]
    nlinarith [h2]

/-! ## The Navier–Stokes instance -/

/-- **`A-anchor` for the parabolic scaling generator.**  With an anchor mode `e`
that is blind to `ΛU` but sees the profile with strength `a₀`, the scale Gram
defect is coercive against the weighted mass of `ΛU`:

  `a₀²·‖ΛU‖²_Γ ≤ Δ_scale`.

So *any* nontrivial scaling motion carries a quantitatively positive scale
cost. -/
theorem scaleGramDefect_anchor_lower_bound {μ : Measure STime} {Gam : STime → ℝ}
    {z0 : STime} {U e : STime → E3} (hGam : ∀ x, 0 ≤ Gam x)
    (hf : Integrable (fun x => Gam x * ∑ a, (U x a) ^ 2) μ)
    (hg : Integrable (fun x => Gam x * ∑ a, (scaleGen z0 U x a) ^ 2) μ)
    (hfg : Integrable (fun x => Gam x * ∑ a, U x a * scaleGen z0 U x a) μ)
    (he : Integrable (fun x => Gam x * ∑ a, (e x a) ^ 2) μ)
    (hef : Integrable (fun x => Gam x * ∑ a, e x a * U x a) μ)
    (heg : Integrable (fun x => Gam x * ∑ a, e x a * scaleGen z0 U x a) μ)
    (hnorm : gramA μ Gam e ≤ 1) (hperp : gramC μ Gam e (scaleGen z0 U) = 0) {a0 : ℝ}
    (hanchor : gramC μ Gam e U = a0) :
    a0 ^ 2 * gramA μ Gam (scaleGen z0 U) ≤ scaleGramDefect μ Gam z0 U :=
  gram_anchor_lower_bound hGam hf hg hfg he hef heg hnorm hperp hanchor

/-! ## The transverse form of the defect -/

/-- **`Δ ≥ c·‖P_⊥Λu‖²_Γ`.**  The Gram defect controls the weighted squared
distance of the scaling derivative to the profile line, with the constant given
by any lower bound `c` on the weighted mass of the profile.  This is the
"transverse scaling motion ⇒ positive scale cost" branch of the dichotomy, made
quantitative. -/
theorem scale_defect_ge_transverse {μ : Measure α} {Gam : α → ℝ} {f g : α → E3}
    (hf : Integrable (fun x => Gam x * ∑ a, (f x a) ^ 2) μ)
    (hg : Integrable (fun x => Gam x * ∑ a, (g x a) ^ 2) μ)
    (hfg : Integrable (fun x => Gam x * ∑ a, f x a * g x a) μ)
    (hGam : ∀ x, 0 ≤ Gam x) (hA : 0 < gramA μ Gam f) {c : ℝ} (hc : c ≤ gramA μ Gam f) :
    c * (∫ x, Gam x * ∑ a, (g x a - (gramC μ Gam f g / gramA μ Gam f) * f x a) ^ 2 ∂μ)
      ≤ gramDefect μ Gam f g := by
  have hid := gram_orbit_distance hf hg hfg hA
  have hdist0 : 0 ≤ ∫ x, Gam x
      * ∑ a, (g x a - (gramC μ Gam f g / gramA μ Gam f) * f x a) ^ 2 ∂μ :=
    integral_nonneg fun x => mul_nonneg (hGam x) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rw [hid]
  calc c * (gramDefect μ Gam f g / gramA μ Gam f)
      ≤ gramA μ Gam f * (gramDefect μ Gam f g / gramA μ Gam f) :=
        mul_le_mul_of_nonneg_right hc (by rw [← hid]; exact hdist0)
    _ = gramDefect μ Gam f g := by field_simp

/-! ## The record-point normalization -/

/-- **The record-point normalization produces the anchor constant.**  If the
weight is bounded below by `γ ≥ 0` and the profile has `|u|² ≥ m ≥ 0` on a
measurable set `S` of finite measure, then the weighted mass of the profile is
at least `γ·m·μ(S)`.  Applied at a record point where `|U(z₀)| = 1`, continuity
gives such an `S` and hence a positive lower bound for `A`. -/
theorem gramA_ge_of_lower_bound_on_set {μ : Measure α} {Gam : α → ℝ} {f : α → E3}
    (hGam : ∀ x, 0 ≤ Gam x)
    (hf : Integrable (fun x => Gam x * ∑ a, (f x a) ^ 2) μ)
    {S : Set α} (hS : MeasurableSet S) (hSfin : μ S ≠ ⊤) {gam m : ℝ}
    (hgam : 0 ≤ gam) (hm : 0 ≤ m)
    (hlow : ∀ x ∈ S, gam ≤ Gam x) (hmlow : ∀ x ∈ S, m ≤ ∑ a, (f x a) ^ 2) :
    gam * m * (μ S).toReal ≤ gramA μ Gam f := by
  have hnn : ∀ x, 0 ≤ Gam x * ∑ a, (f x a) ^ 2 := fun x =>
    mul_nonneg (hGam x) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  -- restrict to `S`
  have hrestrict : ∫ x in S, Gam x * ∑ a, (f x a) ^ 2 ∂μ ≤ gramA μ Gam f := by
    unfold gramA
    exact MeasureTheory.setIntegral_le_integral hf (Filter.Eventually.of_forall hnn)
  have hconst : ∫ x in S, (gam * m) ∂μ ≤ ∫ x in S, Gam x * ∑ a, (f x a) ^ 2 ∂μ := by
    refine MeasureTheory.setIntegral_mono_on
      (MeasureTheory.integrableOn_const (by simp [hSfin])) (hf.integrableOn) hS ?_
    intro x hx
    exact mul_le_mul (hlow x hx) (hmlow x hx) hm (le_trans hgam (hlow x hx))
  rw [MeasureTheory.setIntegral_const, smul_eq_mul] at hconst
  have : gam * m * (μ S).toReal = (μ S).toReal * (gam * m) := by ring
  rw [this]
  exact le_trans hconst hrestrict

/-! ## The quantitative dichotomy -/

/-- **The anchored scale dichotomy, quantitative form.**  Fix a threshold
`ε > 0`.  With an anchor mode of strength `a₀` and a profile of weighted mass at
least `cA > 0`, exactly one of the following two conclusions is available at
each scale:

* the scaling derivative is *transverse*, and then the scale cost is at least
  `a₀²‖ΛU‖²_Γ`, which is bounded away from zero as soon as `‖ΛU‖²_Γ` is;
* the scaling derivative is nearly collinear with the profile,
  `‖ΛU − cU‖²_Γ < ε`, i.e. the profile is `ε`-approximately backward
  self-similar,

and in the second case the anchor forces `‖ΛU‖²_Γ ≤ ε·cA/a₀²` when `a₀ ≠ 0`: an
approximately self-similar branch must have a *small scaling derivative* too. -/
theorem scaleGram_anchored_dichotomy {μ : Measure α} {Gam : α → ℝ} {e f g : α → E3}
    (hGam : ∀ x, 0 ≤ Gam x)
    (hf : Integrable (fun x => Gam x * ∑ a, (f x a) ^ 2) μ)
    (hg : Integrable (fun x => Gam x * ∑ a, (g x a) ^ 2) μ)
    (hfg : Integrable (fun x => Gam x * ∑ a, f x a * g x a) μ)
    (he : Integrable (fun x => Gam x * ∑ a, (e x a) ^ 2) μ)
    (hef : Integrable (fun x => Gam x * ∑ a, e x a * f x a) μ)
    (heg : Integrable (fun x => Gam x * ∑ a, e x a * g x a) μ)
    (hnorm : gramA μ Gam e ≤ 1) (hperp : gramC μ Gam e g = 0) {a0 : ℝ}
    (hanchor : gramC μ Gam e f = a0) (ha0 : a0 ≠ 0) (hA : 0 < gramA μ Gam f)
    {eps : ℝ} (heps : (∫ x, Gam x
      * ∑ a, (g x a - (gramC μ Gam f g / gramA μ Gam f) * f x a) ^ 2 ∂μ) < eps) :
    gramA μ Gam g < eps * gramA μ Gam f / a0 ^ 2 := by
  have hanch := gram_anchor_lower_bound hGam hf hg hfg he hef heg hnorm hperp hanchor
  have hid := gram_orbit_distance hf hg hfg hA
  have ha2 : 0 < a0 ^ 2 := by positivity
  -- `Δ = A·dist² < A·eps`
  have hlt : gramDefect μ Gam f g < gramA μ Gam f * eps := by
    have : gramDefect μ Gam f g / gramA μ Gam f < eps := by rw [← hid]; exact heps
    rw [div_lt_iff₀ hA] at this
    linarith [this]
  have : a0 ^ 2 * gramA μ Gam g < gramA μ Gam f * eps := lt_of_le_of_lt hanch hlt
  rw [lt_div_iff₀ ha2]
  nlinarith [this]

end ClayNS
