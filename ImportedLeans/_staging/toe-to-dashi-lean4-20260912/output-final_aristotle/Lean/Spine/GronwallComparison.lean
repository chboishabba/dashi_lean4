/-
# The integrating-factor comparison carrier, owned once

This module isolates, as a **domain-neutral spine carrier**, the single piece of
scalar analysis that two otherwise unrelated Navier–Stokes developments in this
corpus both factor through:

* the OpenAI `NavierStokesAndEuler` proof of forced finite-time blowup
  (repository `https://github.com/openai/NavierStokesAndEuler`, pinned commit
  `f9e8bc5b38b6e212696e8a30e3e91517af887bbd`, preserved in this tree under
  `Provenance/openai-ns-20260912/`), whose module
  `NavierStokes/R3/ComparisonGronwall.lean` opens with
  `NavierStokesR3.ComparisonGronwall.exp_neg_mul_le_of_deriv_le`;
* the historical DASHI Lean file `Lean/NavierStokesClosure.lean`, whose
  `NavierStokesClosure.ns1_enstrophy_passage` is the entry point of its
  enstrophy → Beale–Kato–Majda chain.

The two consumers point in *opposite* mathematical directions — the first is a
step inside a blowup construction, the second a step inside a (conditional)
global-regularity chain — and neither is derivable from the other.  What they
share is exactly one lemma: on `Icc 0 T`, the integrating factor
`t ↦ exp (-K t) · E t` is antitone as soon as `E' ≤ K · E` holds on the open
interval, and it stays antitone after subtracting `ε · t` when `0 ≤ K` and
`0 ≤ ε` absorb an affine perturbation.

Both carriers below are stated with derivatives required only on `Ioo 0 T` and
continuity only on `Icc 0 T`, which is the weaker of the two consumers'
hypothesis sets; so each consumer's hypotheses genuinely discharge the carrier's.

## What is and is not claimed

`openai_comparison_gronwall` is a *restatement*, proved here from the carrier,
of the upstream signature.  It is **not** an import of the upstream Lean proof:
the upstream project pins `leanprover/lean4:v4.34.0-rc2` and is not a dependency
of this checkout, so no upstream term is quoted or relied on.  The statement was
transcribed from the preserved source and the two are compared
character-for-character in `NS_OPENAI_ARCHAEOLOGY.md`.

`dashi_ns1_enstrophy_passage` is the statement of
`NavierStokesClosure.ns1_enstrophy_passage`, re-derived from the same carrier,
showing that the historical DASHI consumer factors through it.

Nothing here bears on the Clay problem in either direction.  The carrier is a
scalar comparison lemma; it supplies none of the analytic content of either
development.
-/
import Mathlib

noncomputable section

namespace Spine
namespace GronwallComparison

open Set

/-! ## 1.  The carrier: antitonicity of the integrating factor -/

/-- **Carrier (homogeneous).**  If `E` is continuous on `Icc 0 T`, differentiable
on `Ioo 0 T` with `E' t ≤ K * E t` there, then `t ↦ exp (-K t) * E t` is antitone
on `Icc 0 T`.  No sign condition on `K` is used. -/
theorem homogeneous_antitoneOn {T K : ℝ} {E E' : ℝ → ℝ}
    (hcont : ContinuousOn E (Icc 0 T))
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (hbound : ∀ t ∈ Ioo 0 T, E' t ≤ K * E t) :
    AntitoneOn (fun t => Real.exp (-K * t) * E t) (Icc 0 T) := by
  have hgcont : ContinuousOn (fun t => Real.exp (-K * t) * E t) (Icc 0 T) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hcont
  have hgderiv : ∀ t ∈ Ioo 0 T,
      HasDerivAt (fun t => Real.exp (-K * t) * E t)
        (Real.exp (-K * t) * (E' t - K * E t)) t := by
    intro t ht
    have hexp : HasDerivAt (fun x : ℝ => Real.exp (-K * x)) (Real.exp (-K * t) * (-K * 1)) t :=
      ((hasDerivAt_id t).const_mul (-K)).exp
    have h1 := hexp.mul (hderiv t ht)
    convert h1 using 1
    ring
  refine antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := fun t => Real.exp (-K * t) * (E' t - K * E t))
    (convex_Icc 0 T) hgcont ?_ ?_
  · intro t ht
    exact (hgderiv t (by simpa only [interior_Icc] using ht)).hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Ioo 0 T := by simpa only [interior_Icc] using ht
    have := mul_le_mul_of_nonneg_left (sub_nonpos.mpr (hbound t ht')) (Real.exp_pos (-K * t)).le
    simpa using this

/-- **Carrier (affine perturbation).**  With `0 ≤ K` and `0 ≤ ε`, the bound
`E' t ≤ K * E t + ε` on `Ioo 0 T` makes `t ↦ exp (-K t) * E t - ε * t` antitone
on `Icc 0 T`. -/
theorem affine_antitoneOn {T K ε : ℝ} {E E' : ℝ → ℝ}
    (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hcont : ContinuousOn E (Icc 0 T))
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (hbound : ∀ t ∈ Ioo 0 T, E' t ≤ K * E t + ε) :
    AntitoneOn (fun t => Real.exp (-K * t) * E t - ε * t) (Icc 0 T) := by
  have hgcont : ContinuousOn (fun t => Real.exp (-K * t) * E t - ε * t) (Icc 0 T) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
      hcont).sub (continuous_const.mul continuous_id).continuousOn
  have hgderiv : ∀ t ∈ Ioo 0 T,
      HasDerivAt (fun t => Real.exp (-K * t) * E t - ε * t)
        (Real.exp (-K * t) * (E' t - K * E t) - ε) t := by
    intro t ht
    have hexp : HasDerivAt (fun x : ℝ => Real.exp (-K * x)) (Real.exp (-K * t) * (-K * 1)) t :=
      ((hasDerivAt_id t).const_mul (-K)).exp
    have h1 := (hexp.mul (hderiv t ht)).sub ((hasDerivAt_id t).const_mul ε)
    convert h1 using 1
    ring
  refine antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := fun t => Real.exp (-K * t) * (E' t - K * E t) - ε)
    (convex_Icc 0 T) hgcont ?_ ?_
  · intro t ht
    exact (hgderiv t (by simpa only [interior_Icc] using ht)).hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Ioo 0 T := by simpa only [interior_Icc] using ht
    have hexp1 : Real.exp (-K * t) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hK) ht'.1.le)
    have hfirst : Real.exp (-K * t) * (E' t - K * E t) ≤ Real.exp (-K * t) * ε :=
      mul_le_mul_of_nonneg_left (by linarith [hbound t ht']) (Real.exp_pos _).le
    have hsecond : Real.exp (-K * t) * ε ≤ ε := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hexp1 hε
    linarith

/-! ## 2.  The two endpoint forms of the carrier -/

/-- The homogeneous carrier in endpoint form: `E t ≤ E 0 * exp (K t)`. -/
theorem le_initial_mul_exp {T K : ℝ} {E E' : ℝ → ℝ}
    (hcont : ContinuousOn E (Icc 0 T))
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (hbound : ∀ t ∈ Ioo 0 T, E' t ≤ K * E t) :
    ∀ t ∈ Icc 0 T, E t ≤ E 0 * Real.exp (K * t) := by
  intro t ht
  have hanti := homogeneous_antitoneOn hcont hderiv hbound ⟨le_rfl, ht.2.trans' ht.1⟩ ht ht.1
  simp only [mul_zero, Real.exp_zero, one_mul] at hanti
  have hpos : (0 : ℝ) < Real.exp (K * t) := Real.exp_pos _
  have hcancel : Real.exp (-K * t) * Real.exp (K * t) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  calc E t = Real.exp (-K * t) * E t * Real.exp (K * t) := by
        rw [mul_assoc, mul_comm (E t), ← mul_assoc, hcancel, one_mul]
    _ ≤ E 0 * Real.exp (K * t) := mul_le_mul_of_nonneg_right hanti hpos.le

/-- The affine carrier in endpoint form. -/
theorem exp_neg_mul_le_initial_add {T K ε : ℝ} {E E' : ℝ → ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hcont : ContinuousOn E (Icc 0 T))
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (hbound : ∀ t ∈ Ioo 0 T, E' t ≤ K * E t + ε) :
    ∀ t ∈ Icc 0 T, Real.exp (-K * t) * E t ≤ E 0 + ε * t := by
  intro t ht
  have hanti := affine_antitoneOn hK hε hcont hderiv hbound ⟨le_rfl, hT⟩ ht ht.1
  simp only [mul_zero, Real.exp_zero, one_mul, sub_zero] at hanti
  linarith

/-! ## 3.  Consumer A — the OpenAI whole-space comparison estimate

The statement below is the signature of
`NavierStokesR3.ComparisonGronwall.exp_neg_mul_le_of_deriv_le`, transcribed from
`Provenance/openai-ns-20260912/openai_NavierStokesAndEuler/NavierStokes/R3/ComparisonGronwall.lean`
(lines 24–31), and here derived from the carrier of §1.  Its own consumers in
the upstream tree are `le_exp_mul_of_deriv_le`, `le_uniform_exp_mul_of_deriv_le`,
`le_div_radius_of_deriv_le` and, through `NavierStokes.R3LocalizedEnergyLimit`,
the whole-space uniqueness/limit layer of the blowup construction. -/

/-- Consumer A, discharged: the upstream weighted perturbed Grönwall estimate
with nonpositive initial value factors through `affine_antitoneOn`. -/
theorem openai_comparison_gronwall {T K ε : ℝ} {E E' : ℝ → ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hcont : ContinuousOn E (Icc 0 T)) (hinitial : E 0 ≤ 0)
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (hbound : ∀ t ∈ Ioo 0 T, E' t ≤ K * E t + ε) :
    ∀ t ∈ Icc 0 T, Real.exp (-K * t) * E t ≤ ε * t := by
  intro t ht
  have := exp_neg_mul_le_initial_add hT hK hε hcont hderiv hbound t ht
  linarith

/-- The upstream corollary `le_exp_mul_of_deriv_le`, also from the carrier. -/
theorem openai_le_exp_mul_of_deriv_le {T K ε : ℝ} {E E' : ℝ → ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hcont : ContinuousOn E (Icc 0 T)) (hinitial : E 0 ≤ 0)
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (hbound : ∀ t ∈ Ioo 0 T, E' t ≤ K * E t + ε) :
    ∀ t ∈ Icc 0 T, E t ≤ ε * t * Real.exp (K * t) := by
  intro t ht
  have hw := openai_comparison_gronwall hT hK hε hcont hinitial hderiv hbound t ht
  have hmul := mul_le_mul_of_nonneg_right hw (Real.exp_pos (K * t)).le
  have hcancel : Real.exp (-K * t) * Real.exp (K * t) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  calc E t = Real.exp (-K * t) * E t * Real.exp (K * t) := by
        rw [mul_assoc, mul_comm (E t), ← mul_assoc, hcancel, one_mul]
    _ ≤ ε * t * Real.exp (K * t) := hmul

/-- The upstream corollary `le_uniform_exp_mul_of_deriv_le`, also from the
carrier. -/
theorem openai_le_uniform_exp_mul_of_deriv_le {T K ε : ℝ} {E E' : ℝ → ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hcont : ContinuousOn E (Icc 0 T)) (hinitial : E 0 ≤ 0)
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (hbound : ∀ t ∈ Ioo 0 T, E' t ≤ K * E t + ε) :
    ∀ t ∈ Icc 0 T, E t ≤ ε * T * Real.exp (K * T) := by
  intro t ht
  refine (openai_le_exp_mul_of_deriv_le hT hK hε hcont hinitial hderiv hbound t ht).trans ?_
  exact mul_le_mul (mul_le_mul_of_nonneg_left ht.2 hε)
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hK))
    (Real.exp_pos _).le (mul_nonneg hε hT)

/-- The upstream corollary `le_div_radius_of_deriv_le`, the *last* link before
the module boundary: it is the only theorem of `NavierStokes.R3.ComparisonGronwall`
used outside that module on the endpoint path, at
`NavierStokes/R3/WholeSpaceEnergyLimit.lean:88`.  Deriving it here completes the
factorisation of the on-path consumer through the carrier. -/
theorem openai_le_div_radius_of_deriv_le {T K C R : ℝ} {E E' : ℝ → ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hC : 0 ≤ C) (hR : 0 < R)
    (hcont : ContinuousOn E (Icc 0 T)) (hinitial : E 0 = 0)
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (hbound : ∀ t ∈ Ioo 0 T, E' t ≤ K * E t + C / R) :
    ∀ t ∈ Icc 0 T, E t ≤ (C * T * Real.exp (K * T)) / R := by
  intro t ht
  have hle := openai_le_uniform_exp_mul_of_deriv_le hT hK (div_nonneg hC hR.le)
    hcont hinitial.le hderiv hbound t ht
  calc E t ≤ C / R * T * Real.exp (K * T) := hle
    _ = (C * T * Real.exp (K * T)) / R := by ring

/-! ## 4.  Consumer B — the historical DASHI enstrophy passage

The statement below is the signature of
`NavierStokesClosure.ns1_enstrophy_passage` (`Lean/NavierStokesClosure.lean`),
the first link of that file's enstrophy → Beale–Kato–Majda chain; `ns2`, `ns3`
and `ns4` in that file are its downstream consumers.  It is derived here from
the *homogeneous* carrier, with `K := -2α`: note that no sign condition on `α`
is available, which is exactly why the homogeneous carrier is stated without
one. -/

/-- Consumer B, discharged: the DASHI enstrophy passage factors through
`homogeneous_antitoneOn`.  Hypotheses are those of the original: `Z` is
differentiable on all of `ℝ` and the differential inequality holds for `t ≥ 0`.
The carrier needs strictly less. -/
theorem dashi_ns1_enstrophy_passage
    (Z Z' : ℝ → ℝ) (α : ℝ)
    (hderiv : ∀ t, HasDerivAt Z (Z' t) t)
    (hineq : ∀ t, 0 ≤ t → Z' t ≤ -2 * α * Z t) :
    ∀ t, 0 ≤ t → Z t ≤ Z 0 * Real.exp (-2 * α * t) := by
  intro t ht
  have hcont : ContinuousOn Z (Icc 0 (t + 1)) := fun s _ =>
    ((hderiv s).continuousAt).continuousWithinAt
  refine le_initial_mul_exp (K := -2 * α) (E' := Z') hcont (fun s _ => hderiv s)
    (fun s hs => hineq s hs.1.le) t ⟨ht, by linarith⟩

/-- The `H¹` form, `ns2_vorticity_control`, follows from Consumer B unchanged. -/
theorem dashi_ns2_vorticity_control
    (Y Y' : ℝ → ℝ) (α : ℝ)
    (hYnn : ∀ t, 0 ≤ Y t)
    (hderiv : ∀ t, HasDerivAt Y (Y' t) t)
    (hineq : ∀ t, 0 ≤ t → Y' t ≤ -2 * α * Y t) :
    ∀ t, 0 ≤ t → Real.sqrt (Y t) ≤ Real.sqrt (Y 0) * Real.exp (-α * t) := by
  intro t ht
  have hY := dashi_ns1_enstrophy_passage Y Y' α hderiv hineq t ht
  have h1 : Real.sqrt (Y t) ≤ Real.sqrt (Y 0 * Real.exp (-2 * α * t)) :=
    Real.sqrt_le_sqrt hY
  refine h1.trans_eq ?_
  have h2 : Real.exp (-2 * α * t) = Real.exp (-α * t) ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  rw [Real.sqrt_mul (hYnn 0), h2, Real.sqrt_sq (Real.exp_nonneg _)]

/-! ## 5.  Consumer C — the Agda A7 residual-depletion comparison clause

`DASHI.Physics.Closure.NSA7ResidualDepletionGronwallBoundary` is a fail-closed
Agda receipt: its `A7GronwallClause` is a 14-constructor enumeration of the
steps the intended residual-depletion argument would need, and the module
proves none of them.  One constructor,
`gronwallComparisonForZPrimeWithPositiveSlope`, names the scalar comparison in
the module header, `Z' ≥ α β Z − α C`, used there to drive `D_r → 0`.

That clause is the *reflection* of the affine carrier: applying
`affine_antitoneOn` to `-Z` discharges it outright.  The theorem below is that
discharge.  It closes only the scalar clause: the surrounding A7 argument
(A6 assembly, A8 monotonicity, A9 CKN/BKM) is untouched, and the Agda module
has no consumer of this statement to re-point, so this is a one-directional
donation into the Agda lane rather than a factorisation of an existing chain. -/

/-- Consumer C, discharged: the lower-comparison form `Z' ≥ K·Z − ε` gives the
matching exponential lower bound.  With `K := α β` and `ε := α C` this is the
Agda A7 clause `gronwallComparisonForZPrimeWithPositiveSlope`. -/
theorem agda_a7_residual_depletion_comparison {T K ε : ℝ} {Z Z' : ℝ → ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hcont : ContinuousOn Z (Icc 0 T))
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt Z (Z' t) t)
    (hbound : ∀ t ∈ Ioo 0 T, K * Z t - ε ≤ Z' t) :
    ∀ t ∈ Icc 0 T, (Z 0 - ε * t) * Real.exp (K * t) ≤ Z t := by
  intro t ht
  have hneg := exp_neg_mul_le_initial_add (E := fun s => -Z s) (E' := fun s => -Z' s)
    hT hK hε hcont.neg (fun s hs => (hderiv s hs).neg)
    (fun s hs => by have := hbound s hs; linarith) t ht
  have hstep : Z 0 - ε * t ≤ Real.exp (-K * t) * Z t := by
    simp only [mul_neg] at hneg
    linarith
  have hmul := mul_le_mul_of_nonneg_right hstep (Real.exp_pos (K * t)).le
  have hcancel : Real.exp (-K * t) * Real.exp (K * t) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  calc (Z 0 - ε * t) * Real.exp (K * t)
      ≤ Real.exp (-K * t) * Z t * Real.exp (K * t) := hmul
    _ = Z t := by rw [mul_assoc, mul_comm (Z t), ← mul_assoc, hcancel, one_mul]

end GronwallComparison
end Spine
