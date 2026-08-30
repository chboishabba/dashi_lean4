/-
# Row A1a — a single Fourier mode cannot carry a volume-uniform floor

The Gaussian coefficient `βZ_j` is a *normalised* momentum average over the
finite torus: the Brillouin sum divided by the number of modes.  A witness
consisting of one momentum (such as the corner momentum of
`TransverseBubbleEntry`) therefore enters with weight `1/|Λ|`, which tends to
zero as the volume grows, unless its multiplicity grows proportionally with the
volume.

This file proves that dichotomy in sharp form.

* `multiplicity_ge_of_uniform_floor` : if the integrand is bounded by `M` and
  supported on a set `S` of modes, then a floor `b` on the normalised average
  *forces* `|S| ≥ (b/M)·|Λ|`.  So the contributing set must have cardinality
  proportional to the volume.
* `average_le_of_bounded_multiplicity` and `no_uniform_floor_of_bounded_support`
  : conversely, a support of *fixed* cardinality gives an average that tends to
  `0`, so no positive floor survives the infinite-volume limit.

This is exactly the reason the A1a route is rewritten from "one corner
momentum" to "one positive-volume momentum patch" (`PositivePatchEnclosure`):
a patch of positive Lebesgue measure contains a number of torus modes
proportional to the volume, a single mode does not.
-/
import Mathlib

namespace YangMills

open Finset Filter Topology

/-- The normalised average of a mode function over a finite mode set. -/
noncomputable def modeAverage {iota : Type*} [Fintype iota] (f : iota → ℝ) : ℝ :=
  (∑ i, f i) / (Fintype.card iota)

/-- **A floor on the normalised average forces proportional multiplicity.**
If the integrand is bounded above by `M > 0` and vanishes off a set `S` of
modes, then a lower bound `b` on the normalised average forces the contributing
set to have at least `(b/M)·|Λ|` elements. -/
theorem multiplicity_ge_of_uniform_floor {iota : Type*} [Fintype iota]
    {f : iota → ℝ} {S : Finset iota} {M b : ℝ}
    (hsupp : ∀ i ∉ S, f i = 0) (hMf : ∀ i, f i ≤ M)
    (hM : 0 < M) (hb : b ≤ modeAverage f) :
    (b / M) * (Fintype.card iota) ≤ S.card := by
  rcases Nat.eq_zero_or_pos (Fintype.card iota) with hcard | hcard
  · have : Fintype.card iota = 0 := hcard
    simp [this]
  have hcardR : (0 : ℝ) < (Fintype.card iota) := by exact_mod_cast hcard
  have hsum : ∑ i, f i ≤ M * S.card := by
    have h1 : ∑ i ∈ S, f i = ∑ i, f i :=
      Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => hsupp i hi)
    have h2 : ∑ i ∈ S, f i ≤ ∑ _i ∈ S, M := Finset.sum_le_sum (fun i _ => hMf i)
    rw [← h1]
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using h2
  have hbsum : b * (Fintype.card iota) ≤ ∑ i, f i := by
    rw [modeAverage, le_div_iff₀ hcardR] at hb
    exact hb
  have : b * (Fintype.card iota) ≤ M * S.card := le_trans hbsum hsum
  rw [div_mul_eq_mul_div, div_le_iff₀ hM]
  linarith

/-- With the integrand bounded by `M ≥ 0` and supported on at most `m` modes,
the normalised average is at most `M·m/|Λ|`. -/
theorem average_le_of_bounded_multiplicity {iota : Type*} [Fintype iota]
    {f : iota → ℝ} {S : Finset iota} {M : ℝ} {m : ℕ}
    (hsupp : ∀ i ∉ S, f i = 0) (hMf : ∀ i, f i ≤ M)
    (hM : 0 ≤ M) (hcard : S.card ≤ m) :
    modeAverage f ≤ M * m / (Fintype.card iota) := by
  rcases Nat.eq_zero_or_pos (Fintype.card iota) with hc | hc
  · simp [modeAverage, hc]
  have hcardR : (0 : ℝ) < (Fintype.card iota) := by exact_mod_cast hc
  have hsum : ∑ i, f i ≤ M * m := by
    have h1 : ∑ i ∈ S, f i = ∑ i, f i :=
      Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => hsupp i hi)
    have h2 : ∑ i ∈ S, f i ≤ ∑ _i ∈ S, M := Finset.sum_le_sum (fun i _ => hMf i)
    have h3 : (S.card : ℝ) ≤ m := by exact_mod_cast hcard
    have : ∑ i, f i ≤ M * S.card := by
      rw [← h1]
      simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using h2
    nlinarith
  rw [modeAverage, div_le_div_iff_of_pos_right hcardR]
  exact hsum

/-- The single-mode weight on a four-dimensional torus with `N` sites per
direction tends to zero. -/
theorem singleMode_weight_tendsto_zero (M : ℝ) :
    Tendsto (fun N : ℕ => M / (N : ℝ) ^ 4) atTop (𝓝 0) := by
  have h : Tendsto (fun N : ℕ => ((N : ℝ) ^ 4)⁻¹) atTop (𝓝 0) := by
    have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ 4) atTop atTop :=
      (tendsto_pow_atTop (n := 4) (by norm_num)).comp tendsto_natCast_atTop_atTop
    exact hpow.inv_tendsto_atTop
  simpa [div_eq_mul_inv, mul_comm] using h.const_mul M

/-- **No positive floor from a bounded number of modes.**  If only `m` modes
contribute, each at most `M`, then beyond a finite volume the normalised average
falls below any prescribed positive floor `b`.  Hence a corner-momentum witness,
whose multiplicity does not grow with the volume, cannot produce a
volume-uniform Gaussian floor. -/
theorem no_uniform_floor_of_bounded_support (M b : ℝ) (hb : 0 < b) (m : ℕ) :
    ∀ᶠ N : ℕ in atTop, M * m / (N : ℝ) ^ 4 < b := by
  have h := singleMode_weight_tendsto_zero (M * m)
  have := h.eventually (eventually_lt_nhds hb)
  simpa using this

/-- Packaged contrapositive: a scale-uniform *and* volume-uniform floor `b > 0`
for a family of normalised mode averages, with integrands bounded by `M`, forces
the number of contributing modes to grow at least like `(b/M)·|Λ|`. -/
theorem contributingModes_grow_linearly {iota : ℕ → Type*} [∀ n, Fintype (iota n)]
    {f : ∀ n, iota n → ℝ} {S : ∀ n, Finset (iota n)} {M b : ℝ}
    (hsupp : ∀ n, ∀ i ∉ S n, f n i = 0)
    (hMf : ∀ n i, f n i ≤ M) (hM : 0 < M) (hb : ∀ n, b ≤ modeAverage (f n)) :
    ∀ n, (b / M) * (Fintype.card (iota n)) ≤ (S n).card := fun n =>
  multiplicity_ge_of_uniform_floor (hsupp n) (hMf n) hM (hb n)

end YangMills
