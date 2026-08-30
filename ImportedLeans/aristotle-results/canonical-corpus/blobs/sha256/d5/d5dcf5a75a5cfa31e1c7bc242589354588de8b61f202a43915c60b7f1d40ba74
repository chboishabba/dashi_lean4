/-
**What the bounded-height route actually yields, unconditionally.**

Putting together the two halves proved in this cycle:

* the **floor** (`LocalHeight.lean`): a window retaining `m` coordinates with
  `256 derivMass² ≤ 9π² m L² α²` carries `(81/16384) L⁶ α² ≤ Δ`;
* the **ceiling** (`LocalTraceScale.lean`): the retained energy of the very same
  window is at most `Bφ(α,L) = taperMass(φ,α)² + derivMass(φ,α)² L²/(2π²)`,
  *independently of the window length*, and `Δ ≤ ‖a‖²‖b‖² ≤ Bφ²` by
  Cauchy–Schwarz,

one gets an inequality with no prime input at all:

    `finiteGridGramDefect_le_normBound_sq` :  Δ ≤ Bφ(α,L)²
    `source_local_route_constraint`        :  (81/16384) L⁶ α² ≤ Bφ(α,L)² .

This is the honest content of the localization idea: the *self*-budget of a
single zero's window already constrains the offset, without any arithmetic —
and therefore the arithmetic can only help if it beats `Bφ`.  The catch is
visible in `Bφ` itself: the taper masses `taperMass(φ,α) = ∫|φ| e^{−αu}` and
`derivMass(φ,α) = ∫|φ'| e^{−αu}` are taken against a taper of width `≍ L`, so
they grow like `e^{αL/2}` in the off-line direction.  The corollary
`offset_le_of_quadratic_norm_bound` isolates exactly what an `α`-uniform
quadratic bound `Bφ ≤ Cb L²` would give — `|α| ≤ (128/9)·Cb/L` — and hence
exactly which estimate the programme would have to earn.

Nothing here refers to `ζ`, and nothing is assumed about the zeros.
-/
import RiemannAnalytic.LocalHeight

namespace RiemannAnalytic

open Complex Finset

/-- The window-independent bound on the retained energy of one zero's window
vector, in the source normalisation `h = 2π/L`. -/
noncomputable def windowEnergyBound (φ : ℝ → ℝ) (L α : ℝ) : ℝ :=
  taperMass φ α ^ 2 + derivMass φ α ^ 2 * L ^ 2 / (2 * Real.pi ^ 2)

theorem windowEnergyBound_nonneg (φ : ℝ → ℝ) (L α : ℝ) : 0 ≤ windowEnergyBound φ L α := by
  unfold windowEnergyBound
  have : (0 : ℝ) < Real.pi := Real.pi_pos
  positivity

/-- **The ceiling.**  The one-sided window Gram defect of a single zero is at
most the square of the window energy bound — Cauchy–Schwarz plus the
window-length-free norm bound. -/
theorem finiteGridGramDefect_le_normBound_sq {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    {L : ℝ} (hL : 0 < L) (α : ℝ) (d : ℕ) :
    finiteGridGramDefect φ (2 * Real.pi / L) α d ≤ windowEnergyBound φ L α ^ 2 := by
  classical
  set u := gridVec φ (2 * Real.pi / L) (-(Complex.I * (α : ℂ))) d with hu
  have htotal : ∑ k, ‖u k‖ ^ 2 ≤ windowEnergyBound φ L α :=
    gridVec_normSq_source_le hφ hL α d
  have hre : reOf u ⬝ᵥ reOf u ≤ windowEnergyBound φ L α :=
    le_trans (reOf_dotProduct_self_le_total u) htotal
  have him : imOf u ⬝ᵥ imOf u ≤ windowEnergyBound φ L α :=
    le_trans (imOf_dotProduct_self_le_total u) htotal
  have hre0 : 0 ≤ reOf u ⬝ᵥ reOf u := by
    rw [reOf_dotProduct_self]; exact Finset.sum_nonneg fun k _ => sq_nonneg _
  have him0 : 0 ≤ imOf u ⬝ᵥ imOf u := by
    rw [imOf_dotProduct_self]; exact Finset.sum_nonneg fun k _ => sq_nonneg _
  have hdef : finiteGridGramDefect φ (2 * Real.pi / L) α d
      ≤ (reOf u ⬝ᵥ reOf u) * (imOf u ⬝ᵥ imOf u) := by
    unfold finiteGridGramDefect gramDefect
    nlinarith [sq_nonneg (reOf u ⬝ᵥ imOf u)]
  nlinarith [hdef, hre, him, hre0, him0]

/-- **The unconditional constraint produced by the bounded-height route.**

For a source-regime taper and any window long enough to dominate the lattice
tail, the transverse offset of a hypothetical zero satisfies

    (81/16384) L⁶ α² ≤ Bφ(α, L)² ,

where `Bφ` is the window energy bound.  No arithmetic input is used: the floor
and the ceiling both come from the taper. -/
theorem source_local_route_constraint {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) (hnn : ∀ t, 0 ≤ φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L)
    {a : ℝ} (ha : 3 * L / 8 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1) (α : ℝ) {m : ℕ}
    (hm : 1 ≤ m) (hbig : 256 * derivMass φ α ^ 2 ≤ 9 * Real.pi ^ 2 * m * L ^ 2 * α ^ 2) :
    81 / 16384 * L ^ 6 * α ^ 2 ≤ windowEnergyBound φ L α ^ 2 := by
  have hfloor :=
    localGramDefect_floor_of_window_length hφ hev hnn hL h2R ha hplat α hm hbig
  have hceil := finiteGridGramDefect_le_normBound_sq hφ hL α (m + 1)
  linarith

/-- **What an `α`-uniform quadratic norm bound would buy.**  If the window energy
bound obeys `Bφ(α,L) ≤ Cb L²` — the shape the local budget needs — then the
offset is confined to `|α| ≤ (128/9)·Cb/L`.  The hypothesis is exactly the
estimate the programme has to earn: the twisted taper masses in `Bφ` are taken
against a taper of width `≍ L`, so they are not `α`-uniform for free. -/
theorem offset_le_of_quadratic_norm_bound {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) (hnn : ∀ t, 0 ≤ φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L)
    {a : ℝ} (ha : 3 * L / 8 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1) (α : ℝ) {m : ℕ}
    (hm : 1 ≤ m) (hbig : 256 * derivMass φ α ^ 2 ≤ 9 * Real.pi ^ 2 * m * L ^ 2 * α ^ 2)
    {Cb : ℝ} (hCb : 0 ≤ Cb) (hnorm : windowEnergyBound φ L α ≤ Cb * L ^ 2) :
    |α| ≤ 128 / 9 * Cb / L := by
  have hcon := source_local_route_constraint hφ hev hnn hL h2R ha hplat α hm hbig
  have hB0 := windowEnergyBound_nonneg φ L α
  have hsq : windowEnergyBound φ L α ^ 2 ≤ Cb ^ 2 * L ^ 4 := by nlinarith
  have hα : α ^ 2 ≤ (16384 / 81) * Cb ^ 2 / L ^ 2 := by
    have hL6 : (0 : ℝ) < L ^ 6 := by positivity
    have h1 : 81 / 16384 * L ^ 6 * α ^ 2 ≤ Cb ^ 2 * L ^ 4 := by linarith
    have hL2 : (0 : ℝ) < L ^ 2 := by positivity
    rw [le_div_iff₀ hL2]
    nlinarith [sq_nonneg α, hL.le]
  have habs : |α| ^ 2 ≤ (128 / 9 * Cb / L) ^ 2 := by
    have hL2 : (0 : ℝ) < L ^ 2 := by positivity
    have hval : (128 / 9 * Cb / L) ^ 2 = (16384 / 81) * Cb ^ 2 / L ^ 2 := by
      field_simp
      ring
    rw [sq_abs, hval]
    exact hα
  have hrhs : 0 ≤ 128 / 9 * Cb / L := by positivity
  nlinarith [abs_nonneg α, habs, hrhs]

end RiemannAnalytic
