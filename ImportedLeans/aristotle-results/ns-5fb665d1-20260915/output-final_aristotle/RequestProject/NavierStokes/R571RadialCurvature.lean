/-
# R571 Gate-A radial leaves: the `A1` transport-gradient and `A2`
transport-curvature envelopes, paid.

## Lane

Lane **B** (unforced periodic `T³`) of `Docs/roadmaps/NSProofControl20260915.md`.
Nothing here is transported to lane A (unforced `R³`) and nothing here uses the
released forced C/D material.

## Which `A1`/`A2` these are

The names `A1` and `A2` collide across two source corpora, and this file is
about the **B-carrier** pair, not the TOE pair:

* **B-carrier (this file).** `A1` and `A2` are the two *radial Taylor envelope
  constants* of
  `DASHI.Physics.Closure.NSTriadKNR571PhysicalSecondMomentEnvelopeSplitExact`,
  i.e. the fields `transportGradient` and `transportCurvature` of
  `R571RadialTaylorEnvelope`:

  ```text
  |L|  ≤ |y|   A1          (linear radial increment)
  |R±| ≤ |y|²  A2          (radial Taylor remainders)
  ```

* **TOE source-local (not this file).** `NSUnforced` calls its two *reductions*
  `A1` (the `CommutatorOnlySpacetimeBudget568` route) and `A2` (the critical
  production ceiling).  Those are different objects; see
  `RequestProject.NavierStokes.NSLaneDiscipline` for the reconciliation.

## What is proved

`DASHI.Physics.Closure.NSTriadKNR571RadialCurvatureBoundaryExact` records that
after the preferred Taylor choice the `+` remainder is *exactly zero*, so the
whole `A2` leaf collapses to the single centred second-difference bound for the
homochiral R571 multiplier `m_σ(k) = σ‖k‖`, and states explicitly that no
uniform `|y|² A2` estimate is claimed there.

This file supplies that estimate, on a real inner-product carrier:

```text
0 ≤ ‖k+y‖ - 2‖k‖ + ‖k-y‖ ≤ ‖y‖² / ‖k‖ .
```

Consequences on the B carrier:

* `abs_centeredRadialDefect_le` — the `A2` leaf with `A2 = 1/‖k‖`;
* `abs_centeredRadialDefect_le_of_one_le_norm` — on the periodic integer
  lattice every nonzero centre mode has `‖k‖ ≥ 1`, so **`A2 = 1` holds
  uniformly, with no dependence on the Galerkin cutoff**;
* `abs_radialIncrement_le` — the `A1` leaf with `A1 = 1`, also cutoff-uniform.

No PDE input, no cutoff bookkeeping and no Boolean ledger is used.  The two
state-side leaves `G1`, `G2` are *not* paid here; they are the remaining named
obligations, carried in
`RequestProject.NavierStokes.R571PairedSecondMoment`.
-/
import Mathlib
import NSUnforced.HelicalMultiplierDifference

noncomputable section

namespace RequestProject.NavierStokes.R571

open DASHI.NS.Unforced

variable {E : Type*} [NormedAddCommGroup E]

/-! ## The Euclidean-radius second difference -/

/-- **Convexity half.**  The centred second difference of the norm is
nonnegative.  (This is the sign the signed R571 route must preserve: the defect
never helps by accident.) -/
theorem norm_second_difference_nonneg [NormedSpace ℝ E] (x y : E) :
    0 ≤ ‖x + y‖ - 2 * ‖x‖ + ‖x - y‖ := by
  have h : ‖(x + y) + (x - y)‖ ≤ ‖x + y‖ + ‖x - y‖ := norm_add_le _ _
  have hx : (x + y) + (x - y) = (2 : ℝ) • x := by rw [two_smul]; abel
  rw [hx, norm_smul] at h
  simp only [Real.norm_ofNat] at h
  linarith

/-- **The curvature half — the `A2` estimate.**  For the Euclidean norm on a
real inner-product space,

`‖x+y‖ - 2‖x‖ + ‖x-y‖ ≤ ‖y‖² / ‖x‖`.

The proof is exact: the parallelogram law gives
`‖x+y‖ + ‖x-y‖ ≤ 2√(‖x‖² + ‖y‖²)`, and `√(a²+t²) ≤ a + t²/(2a)`. -/
theorem norm_second_difference_le [InnerProductSpace ℝ E] (x y : E) (hx : x ≠ 0) :
    ‖x + y‖ - 2 * ‖x‖ + ‖x - y‖ ≤ ‖y‖ ^ 2 / ‖x‖ := by
  set a := ‖x‖ with ha
  set t := ‖y‖ with ht
  have hapos : 0 < a := by rw [ha]; exact norm_pos_iff.2 hx
  have hpar : ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (a ^ 2 + t ^ 2) := by
    rw [ha, ht]; simpa [sq] using parallelogram_law_with_norm ℝ x y
  have hsq : (‖x + y‖ + ‖x - y‖) ^ 2 ≤ 4 * (a ^ 2 + t ^ 2) := by
    nlinarith [sq_nonneg (‖x + y‖ - ‖x - y‖)]
  have hS : a ^ 2 + t ^ 2 ≤ (a + t ^ 2 / (2 * a)) ^ 2 := by
    have he : (a + t ^ 2 / (2 * a)) ^ 2 = a ^ 2 + t ^ 2 + (t ^ 2 / (2 * a)) ^ 2 := by
      field_simp; ring
    nlinarith [sq_nonneg (t ^ 2 / (2 * a))]
  have hsum_nonneg : 0 ≤ ‖x + y‖ + ‖x - y‖ := by positivity
  have hrhs_nonneg : 0 ≤ 2 * (a + t ^ 2 / (2 * a)) := by positivity
  have hfinal : ‖x + y‖ + ‖x - y‖ ≤ 2 * (a + t ^ 2 / (2 * a)) := by nlinarith
  have hd : t ^ 2 / a = 2 * (t ^ 2 / (2 * a)) := by field_simp
  linarith

/-! ## The R571 radial symbol and its two Gate-A leaves -/

/-- The homochiral R571 radial multiplier `m_σ(k) = σ‖k‖`, built from the donor
`HelicitySign.signedRadius` carrier so that the sign convention is literally the
Agda R311/R571 one. -/
def radialSymbol (s : HelicitySign) (k : E) : ℝ := HelicitySign.signedRadius s ‖k‖

@[simp] theorem radialSymbol_plus (k : E) :
    radialSymbol HelicitySign.plus k = ‖k‖ := rfl

@[simp] theorem radialSymbol_minus (k : E) :
    radialSymbol HelicitySign.minus k = -‖k‖ := rfl

/-- `|m_σ(x) - m_σ(x')| = | ‖x‖ - ‖x'‖ |`: the sign drops out of every radial
increment. -/
theorem abs_radialSymbol_sub (s : HelicitySign) (x x' : E) :
    |radialSymbol s x - radialSymbol s x'| = |‖x‖ - ‖x'‖| := by
  cases s
  · rfl
  · simp only [radialSymbol_minus]
    rw [show -‖x‖ - -‖x'‖ = -(‖x‖ - ‖x'‖) by ring, abs_neg]

/-- **The `A1` leaf, paid with `A1 = 1`.**  The linear radial increment of the
R571 multiplier costs exactly one displacement, uniformly in the centre mode and
hence uniformly in the Galerkin cutoff. -/
theorem abs_radialIncrement_le (s : HelicitySign) (k y : E) :
    |radialSymbol s (k + y) - radialSymbol s k| ≤ ‖y‖ := by
  rw [abs_radialSymbol_sub]
  have h1 : ‖k + y‖ - ‖k‖ ≤ ‖y‖ := by
    have := norm_add_le k y; linarith
  have h2 : ‖k‖ - ‖k + y‖ ≤ ‖y‖ := by
    have : ‖k‖ = ‖(k + y) + (-y)‖ := by congr 1; abel
    have h := norm_add_le (k + y) (-y)
    rw [norm_neg] at h
    linarith [this ▸ h]
  exact abs_sub_le_iff.2 ⟨h1, h2⟩

/-- The centred radial defect of
`DASHI.Physics.Closure.NSTriadKNR571RadialCurvatureSquareGapExact`:
`D = (m(k-y) - m(k)) + (m(k+y) - m(k))`.  With the preferred Taylor linear model
this is the *only* surviving remainder, so the `A2` leaf is exactly a bound on
`|D|`. -/
def centeredRadialDefect (s : HelicitySign) (k y : E) : ℝ :=
  (radialSymbol s (k - y) - radialSymbol s k) + (radialSymbol s (k + y) - radialSymbol s k)

/-- The defect is the signed centred second difference of the norm. -/
theorem centeredRadialDefect_eq (s : HelicitySign) (k y : E) :
    centeredRadialDefect s k y =
      HelicitySign.signedRadius s (‖k + y‖ - 2 * ‖k‖ + ‖k - y‖) := by
  cases s <;> simp only [centeredRadialDefect, radialSymbol_plus, radialSymbol_minus,
    HelicitySign.signedRadius_plus, HelicitySign.signedRadius_minus] <;> ring

/-- **The `A2` leaf, paid with `A2 = 1/‖k‖`.**  For every helicity sign, every
nonzero centre mode `k` and every displacement `y`,

`|D| ≤ ‖y‖² / ‖k‖`. -/
theorem abs_centeredRadialDefect_le [InnerProductSpace ℝ E] (s : HelicitySign) {k : E}
    (y : E) (hk : k ≠ 0) :
    |centeredRadialDefect s k y| ≤ ‖y‖ ^ 2 / ‖k‖ := by
  have hnn := norm_second_difference_nonneg k y
  have hub := norm_second_difference_le k y hk
  rw [centeredRadialDefect_eq]
  cases s
  · rw [HelicitySign.signedRadius_plus, abs_of_nonneg hnn]; exact hub
  · rw [HelicitySign.signedRadius_minus, abs_neg, abs_of_nonneg hnn]; exact hub

/-- **The `A2` leaf on the periodic lattice, paid with `A2 = 1`.**  Every nonzero
mode of `T³` has `‖k‖ ≥ 1`, so the radial curvature envelope is the absolute
constant `1`: it depends on neither the centre mode nor the Galerkin cutoff. -/
theorem abs_centeredRadialDefect_le_of_one_le_norm [InnerProductSpace ℝ E]
    (s : HelicitySign) {k : E} (y : E) (hk : 1 ≤ ‖k‖) : |centeredRadialDefect s k y| ≤ ‖y‖ ^ 2 := by
  have hk0 : k ≠ 0 := by
    intro h; rw [h, norm_zero] at hk; linarith
  refine le_trans (abs_centeredRadialDefect_le s y hk0) ?_
  rw [div_le_iff₀ (by linarith : (0:ℝ) < ‖k‖)]
  nlinarith [sq_nonneg ‖y‖]

/-- **Non-vacuity of the `A2` payment.**  The defect is genuinely nonzero, so
`abs_centeredRadialDefect_le` is not a bound on the zero function: on the real
line with `k = 1`, `y = 2` the centred second difference equals `2`. -/
theorem centeredRadialDefect_ne_zero :
    centeredRadialDefect HelicitySign.plus (1 : ℝ) (2 : ℝ) = 2 := by
  norm_num [centeredRadialDefect, radialSymbol, HelicitySign.signedRadius]

/-- **The `A2` constant cannot be improved by more than a fixed factor.**  For a
displacement orthogonal to the centre mode the defect is already within `20 %`
of the bound `‖y‖²/‖k‖`: taking `k = 1`, `y = i` in `ℂ` (a two-dimensional real
inner-product space) the defect is `2√2 - 2 ≥ 4/5`, while the bound is `1`.  So
the quadratic envelope of `abs_centeredRadialDefect_le` is the true order, not
an artefact of the proof. -/
theorem centeredRadialDefect_bound_is_order_sharp :
    (4 : ℝ) / 5 * (‖Complex.I‖ ^ 2 / ‖(1 : ℂ)‖)
      ≤ |centeredRadialDefect HelicitySign.plus (1 : ℂ) Complex.I| := by
  have hp : ‖(1 : ℂ) + Complex.I‖ = Real.sqrt 2 := by
    simp [Complex.norm_def, Complex.normSq_apply]; norm_num
  have hm : ‖(1 : ℂ) - Complex.I‖ = Real.sqrt 2 := by
    simp [Complex.norm_def, Complex.normSq_apply]; norm_num
  have hs : (4 : ℝ) / 5 ≤ 2 * Real.sqrt 2 - 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hval : centeredRadialDefect HelicitySign.plus (1 : ℂ) Complex.I
      = 2 * Real.sqrt 2 - 2 := by
    simp only [centeredRadialDefect, radialSymbol, HelicitySign.signedRadius, hp, hm]
    norm_num; ring
  rw [hval, abs_of_nonneg (by linarith)]
  simpa using hs

end RequestProject.NavierStokes.R571
