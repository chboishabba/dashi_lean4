/-
# The approximate anchor, and probes as anchors

`ScaleAnchor.lean` proves the anchored coercivity inequality `a₀²B ≤ Δ` under the
*exact* orthogonality hypothesis `⟨e, Λu⟩_Γ = 0`.  For Navier–Stokes that
hypothesis is not free: the linearisation around a self-similar profile carries
advection and pressure terms, so an anchor cannot be produced by declaring the
Gaussian-weighted operator self-adjoint.  What one *can* hope to produce is a
**probe** — a single linear functional that annihilates the scaling direction
only approximately, because any exactly scale-neutral weight has to be cut off
somewhere and the cut-off leaves a residual.

This file supplies the two missing links.

## 1. The approximate anchor

`ClayNS.gram_anchor_lower_bound_approx`: if the anchor is only *approximately*
orthogonal to the scaling direction,

  `|⟨e, g⟩_Γ| ≤ δ`,  `⟨e, f⟩_Γ = a₀`,  `‖e‖²_Γ ≤ 1`,

and the collinearity coefficient of the pair is a priori bounded,
`|C|/B ≤ Mc`, then

  `(|a₀| − Mc·δ)²·B ≤ Δ`                                   (approximate anchor)

whenever the bracket is nonnegative.  At `δ = 0` this is exactly the exact
anchor inequality, and it degrades continuously: a residual of size `δ` costs
`Mc·δ` of anchor strength and nothing else.  Combined with the geometric tail
`ε(R) = C2^{−αR}` of `ExpenditureLedger.lean`, a cut-off probe whose residual
carries a positive scaling dimension supplies such a `δ`, as small as one likes.

## 2. Probes are anchors (the Riesz step)

A probe is given by a *weight* `w`, as `L(V) = ∫⟨w,V⟩dμ`.  Dividing by the
Gaussian weight turns it into an anchor mode of the weighted space:

* `ClayNS.gramC_riesz` — `⟨w/Γ, V⟩_Γ = ∫⟨w,V⟩`, so the probe *is* the weighted
  pairing against `e = w/Γ`;
* `ClayNS.gramA_riesz` — `‖w/Γ‖²_Γ = ∫|w|²/Γ`, the normalisation that has to be
  at most one.

Consequently `ClayNS.probe_scale_coercivity` reads the approximate anchor
directly in probe language: a probe that is nearly blind to `ΛU`, sees `U` with
strength `a₀`, and is normalised, forces a quantitative scale-Gram defect.  This
is the precise sense in which "find one explicit Gaussian-weighted probe that
kills `ΛU` but sees `U`" is *sufficient* — and it is strictly weaker than
diagonalising the linearised operator.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.ScaleAnchor

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace ClayNS

variable {α : Type*} [MeasurableSpace α]

/-! ## The approximate anchor inequality -/

/-- **The approximate anchor inequality.**  An anchor that is orthogonal to the
scaling direction only up to `δ` still yields coercivity, with the anchor
strength reduced by `Mc·δ`, where `Mc` bounds the collinearity coefficient
`|C|/B` of the pair.

At `δ = 0` this is `ClayNS.gram_anchor_lower_bound`. -/
theorem gram_anchor_lower_bound_approx {μ : Measure α} {Gam : α → ℝ} {e f g : α → E3}
    (hGam : ∀ x, 0 ≤ Gam x)
    (hf : Integrable (fun x => Gam x * ∑ a, (f x a) ^ 2) μ)
    (hg : Integrable (fun x => Gam x * ∑ a, (g x a) ^ 2) μ)
    (hfg : Integrable (fun x => Gam x * ∑ a, f x a * g x a) μ)
    (he : Integrable (fun x => Gam x * ∑ a, (e x a) ^ 2) μ)
    (hef : Integrable (fun x => Gam x * ∑ a, e x a * f x a) μ)
    (heg : Integrable (fun x => Gam x * ∑ a, e x a * g x a) μ)
    (hnorm : gramA μ Gam e ≤ 1) {del a0 Mc : ℝ} (hdel : 0 ≤ del)
    (hperp : |gramC μ Gam e g| ≤ del)
    (hanchor : gramC μ Gam e f = a0)
    (hcoll : |gramC μ Gam f g| ≤ Mc * gramA μ Gam g)
    (hbracket : 0 ≤ |a0| - Mc * del) :
    (|a0| - Mc * del) ^ 2 * gramA μ Gam g ≤ gramDefect μ Gam f g := by
  set A := gramA μ Gam f with hA
  set B := gramA μ Gam g with hB
  set C := gramC μ Gam f g with hC
  have hB0 : 0 ≤ B := gramA_nonneg hGam g
  -- the quadratic lower bound at an arbitrary coefficient `c`
  have hquad : ∀ c : ℝ, (|a0| - |c| * del) ^ 2 ≤ A - 2 * c * C + c ^ 2 * B ∨
      |a0| - |c| * del < 0 := by
    intro c
    rcases lt_or_ge (|a0| - |c| * del) 0 with hneg | hpos
    · exact Or.inr hneg
    refine Or.inl ?_
    have hw2 := integrable_gramSub_sq hf hg hfg c
    have hew := integrable_gramC_anchor_sub hef heg c
    have hcs : 0 ≤ gramDefect μ Gam e (gramSub f g c) :=
      gramDefect_nonneg hGam he hw2 hew
    have hval : gramC μ Gam e (gramSub f g c) = a0 - c * gramC μ Gam e g :=
      by rw [gramC_anchor_sub hef heg c, hanchor]
    have hmass : gramA μ Gam (gramSub f g c) = A - 2 * c * C + c ^ 2 * B :=
      gramA_sub_eq hf hg hfg c
    have hQ0 : 0 ≤ A - 2 * c * C + c ^ 2 * B := by
      rw [← hmass]; exact gramA_nonneg hGam _
    have hlow : |a0| - |c| * del ≤ |a0 - c * gramC μ Gam e g| := by
      have h1 : |c * gramC μ Gam e g| ≤ |c| * del := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hperp (abs_nonneg c)
      have h2 : |a0| - |c * gramC μ Gam e g| ≤ |a0 - c * gramC μ Gam e g| :=
        abs_sub_abs_le_abs_sub _ _
      linarith
    have hsq : (|a0| - |c| * del) ^ 2 ≤ (a0 - c * gramC μ Gam e g) ^ 2 := by
      have := mul_self_le_mul_self hpos hlow
      rw [← sq_abs (a0 - c * gramC μ Gam e g)]
      nlinarith [this, abs_nonneg (a0 - c * gramC μ Gam e g)]
    have hexp : (a0 - c * gramC μ Gam e g) ^ 2
        ≤ gramA μ Gam e * (A - 2 * c * C + c ^ 2 * B) := by
      have := hcs
      rw [gramDefect, hval, hmass] at this
      linarith
    have hle1 : gramA μ Gam e * (A - 2 * c * C + c ^ 2 * B)
        ≤ 1 * (A - 2 * c * C + c ^ 2 * B) := mul_le_mul_of_nonneg_right hnorm hQ0
    linarith
  rcases eq_or_lt_of_le hB0 with hB0' | hBpos
  · -- degenerate case `B = 0`
    have hCzero : C = 0 := by
      have hd : 0 ≤ gramDefect μ Gam f g := gramDefect_nonneg hGam hf hg hfg
      rw [gramDefect, ← hA, ← hB, ← hC, ← hB0', mul_zero] at hd
      nlinarith [sq_nonneg C]
    simp [gramDefect, ← hA, ← hB, ← hC, ← hB0', hCzero]
  · -- the optimal coefficient `c = C/B`, whose modulus is at most `Mc`
    have hne : B ≠ 0 := ne_of_gt hBpos
    have habs : |C / B| ≤ Mc := by
      rw [abs_div, abs_of_pos hBpos, div_le_iff₀ hBpos]
      exact hcoll
    have hbr : 0 ≤ |a0| - |C / B| * del := by
      have : |C / B| * del ≤ Mc * del := mul_le_mul_of_nonneg_right habs hdel
      linarith
    have h := hquad (C / B)
    have hmain : (|a0| - |C / B| * del) ^ 2 ≤ A - 2 * (C / B) * C + (C / B) ^ 2 * B := by
      rcases h with h | h
      · exact h
      · linarith
    have hexp : A - 2 * (C / B) * C + (C / B) ^ 2 * B = A - C ^ 2 / B := by
      field_simp; ring
    rw [hexp] at hmain
    have hmono : (|a0| - Mc * del) ^ 2 ≤ (|a0| - |C / B| * del) ^ 2 := by
      have h1 : |a0| - Mc * del ≤ |a0| - |C / B| * del := by
        have : |C / B| * del ≤ Mc * del := mul_le_mul_of_nonneg_right habs hdel
        linarith
      nlinarith [hbracket, h1]
    have h2 : C ^ 2 / B ≤ A - (|a0| - Mc * del) ^ 2 := by linarith
    rw [div_le_iff₀ hBpos] at h2
    rw [gramDefect, ← hA, ← hB, ← hC]
    nlinarith [h2]

/-! ## Probes as anchors: the Riesz step -/

/-- The anchor mode attached to a probe weight: `e = w/Γ`. -/
def probeMode (Gam : α → ℝ) (w : α → E3) : α → E3 := fun x => (Gam x)⁻¹ • w x

omit [MeasurableSpace α] in
@[simp] lemma probeMode_apply (Gam : α → ℝ) (w : α → E3) (x : α) (a : Fin 3) :
    probeMode Gam w x a = (Gam x)⁻¹ * w x a := rfl

/-- **The Riesz step, pairing form.**  The weighted pairing of the mode `w/Γ`
with a field is the *unweighted* probe `∫⟨w,V⟩`: the probe and the anchor are
the same functional. -/
lemma gramC_riesz {μ : Measure α} {Gam : α → ℝ} (hpos : ∀ x, 0 < Gam x) (w V : α → E3) :
    gramC μ Gam (probeMode Gam w) V = ∫ x, ∑ a, w x a * V x a ∂μ := by
  unfold gramC
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hx : Gam x ≠ 0 := ne_of_gt (hpos x)
  simp only [probeMode_apply, Fin.sum_univ_three]
  field_simp

/-- **The Riesz step, normalisation form.**  The weighted mass of the mode `w/Γ`
is `∫|w|²/Γ`; requiring it to be at most one is the normalisation of the
approximate anchor. -/
lemma gramA_riesz {μ : Measure α} {Gam : α → ℝ} (hpos : ∀ x, 0 < Gam x) (w : α → E3) :
    gramA μ Gam (probeMode Gam w) = ∫ x, (Gam x)⁻¹ * ∑ a, (w x a) ^ 2 ∂μ := by
  unfold gramA
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hx : Gam x ≠ 0 := ne_of_gt (hpos x)
  simp only [probeMode_apply, Fin.sum_univ_three]
  field_simp

/-! ## The probe form of the coercivity statement -/

/-- **A separating probe forces a scale cost.**  Suppose a weight `w` gives a
probe which

* is normalised in the weighted space, `∫|w|²/Γ ≤ 1`;
* is *nearly blind* to the scaling direction, `|∫⟨w,ΛU⟩| ≤ δ`;
* *sees* the profile, `∫⟨w,U⟩ = a₀`;

and suppose the collinearity coefficient of the pair `(U, ΛU)` is bounded by
`Mc`.  Then the scale-Gram defect is coercive against the weighted mass of the
scaling derivative:

  `(|a₀| − Mc·δ)²·‖ΛU‖²_Γ ≤ Δ_scale`.

No self-adjointness of the linearised operator is used: only one functional that
separates `U` from `ΛU`, with a quantitative separation margin. -/
theorem probe_scale_coercivity {μ : Measure STime} {Gam : STime → ℝ} {z0 : STime}
    {U w : STime → E3} (hpos : ∀ x, 0 < Gam x)
    (hf : Integrable (fun x => Gam x * ∑ a, (U x a) ^ 2) μ)
    (hg : Integrable (fun x => Gam x * ∑ a, (scaleGen z0 U x a) ^ 2) μ)
    (hfg : Integrable (fun x => Gam x * ∑ a, U x a * scaleGen z0 U x a) μ)
    (he : Integrable (fun x => Gam x * ∑ a, (probeMode Gam w x a) ^ 2) μ)
    (hef : Integrable (fun x => Gam x * ∑ a, probeMode Gam w x a * U x a) μ)
    (heg : Integrable (fun x => Gam x * ∑ a, probeMode Gam w x a * scaleGen z0 U x a) μ)
    {del a0 Mc : ℝ} (hdel : 0 ≤ del)
    (hnorm : (∫ x, (Gam x)⁻¹ * ∑ a, (w x a) ^ 2 ∂μ) ≤ 1)
    (hperp : |∫ x, ∑ a, w x a * scaleGen z0 U x a ∂μ| ≤ del)
    (hanchor : (∫ x, ∑ a, w x a * U x a ∂μ) = a0)
    (hcoll : |gramC μ Gam U (scaleGen z0 U)| ≤ Mc * gramA μ Gam (scaleGen z0 U))
    (hbracket : 0 ≤ |a0| - Mc * del) :
    (|a0| - Mc * del) ^ 2 * gramA μ Gam (scaleGen z0 U) ≤ scaleGramDefect μ Gam z0 U := by
  have hGam : ∀ x, 0 ≤ Gam x := fun x => (hpos x).le
  have hnorm' : gramA μ Gam (probeMode Gam w) ≤ 1 := by
    rw [gramA_riesz hpos]; exact hnorm
  have hperp' : |gramC μ Gam (probeMode Gam w) (scaleGen z0 U)| ≤ del := by
    rw [gramC_riesz hpos]; exact hperp
  have hanchor' : gramC μ Gam (probeMode Gam w) U = a0 := by
    rw [gramC_riesz hpos]; exact hanchor
  exact gram_anchor_lower_bound_approx hGam hf hg hfg he hef heg hnorm' hdel hperp'
    hanchor' hcoll hbracket

end ClayNS
