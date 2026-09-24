/-
**Q6.1 — how tall must the window be?  The bounded-height retention threshold.**

The bounded-height programme asks whether a window of *fixed* ordinate height
`H` — ideally `H = 1` — still retains enough transverse energy for the Gram
floor

    Δ_{ρ,H} ≥ (81/16384) L⁶ α² .

The existing machinery answers this quantitatively rather than yes/no.  The
floor of `OneSidedGram.lean` holds as soon as the lattice tail is dominated,

    derivMass(φ,α)² / (h² m)  ≤  (9/1024) L⁴ α² ,      h = 2π/L,

so with `m` grid points in the window this is a *lower bound on the number of
retained coordinates*, and hence — since the window height is `H = m h` — a
lower bound on the height.  This file makes that explicit:

* `tail_le_of_window_length`: `256 · derivMass² ≤ 9π² m L² α²` suffices;
* `localGramDefect_floor_of_window_length`: hence the source floor
  `(81/16384) L⁶α² ≤ Δ` for such a window;
* `tail_le_of_window_height`: in terms of the ordinate height `H = m h`, the
  sufficient condition is `512 · derivMass² ≤ 9π H L³ α²`;
* `unitHeightThreshold` and `unit_height_dichotomy`: **the answer for `H = 1`.**
  Either the offset is already below the explicit threshold

      |α| ≤ √(512 · derivMass(φ,α)² / (9π L³))   ( ≍ L^{-3/2} for a taper of
                                                   bounded twisted-derivative
                                                   mass ),

  or a unit-height window already carries the full source floor.

So the localization scale demanded by *retention* is `H ≳ derivMass²/(L³α²)`,
which is bounded — indeed `H = 1` — exactly for offsets `|α| ≳ L^{-3/2}`, and
grows as the offset shrinks.  This is the honest form of the "local retention"
question: a fixed height suffices only above an explicit offset threshold, and
below that threshold the offset is already `o(1)`.

Nothing here refers to `ζ`.
-/
import RiemannAnalytic.LocalTraceScale
import RiemannAnalytic.WeightedGramTarget

namespace RiemannAnalytic

open Complex Finset

/-! ### Sufficient window length -/

/-- **Sufficient number of retained coordinates.**  If the window keeps `m`
coordinates with `256 · derivMass² ≤ 9π² m L² α²`, the lattice tail is dominated
at the level required by the source floor. -/
theorem tail_le_of_window_length {φ : ℝ → ℝ} {L α : ℝ} (hL : 0 < L) {m : ℕ} (hm : 1 ≤ m)
    (hbig : 256 * derivMass φ α ^ 2 ≤ 9 * Real.pi ^ 2 * m * L ^ 2 * α ^ 2) :
    derivMass φ α ^ 2 / ((2 * Real.pi / L) ^ 2 * m) ≤ 9 / 1024 * L ^ 4 * α ^ 2 := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hden : (0 : ℝ) < (2 * Real.pi / L) ^ 2 * m := by positivity
  rw [div_le_iff₀ hden]
  have hval : 9 / 1024 * L ^ 4 * α ^ 2 * ((2 * Real.pi / L) ^ 2 * m)
      = 9 * Real.pi ^ 2 * m * L ^ 2 * α ^ 2 / 256 := by
    field_simp
    ring
  rw [hval]
  linarith

/-- **The bounded-window source floor.**  A window retaining `m` coordinates
with `256 · derivMass² ≤ 9π² m L² α²` carries the full source Gram floor. -/
theorem localGramDefect_floor_of_window_length {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) (hnn : ∀ t, 0 ≤ φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L)
    {a : ℝ} (ha : 3 * L / 8 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1) (α : ℝ) {m : ℕ}
    (hm : 1 ≤ m) (hbig : 256 * derivMass φ α ^ 2 ≤ 9 * Real.pi ^ 2 * m * L ^ 2 * α ^ 2) :
    81 / 16384 * L ^ 6 * α ^ 2 ≤ finiteGridGramDefect φ (2 * Real.pi / L) α (m + 1) := by
  have htail := tail_le_of_window_length (φ := φ) hL hm hbig
  have hfloor := finiteGridGramDefect_source_floor hφ hev hnn hL h2R ha hplat α hm
  have hL2 : (0 : ℝ) < 9 / 16 * L ^ 2 := by positivity
  nlinarith [htail, hfloor, hL2]

/-! ### The same in terms of the ordinate height -/

/-- **Sufficient window height.**  A window of ordinate height `H` at grid
spacing `h = 2π/L` retains about `m ≍ H L/2π` coordinates; if it retains at
least that many and `512 · derivMass² ≤ 9π H L³ α²`, the tail is dominated. -/
theorem tail_le_of_window_height {φ : ℝ → ℝ} {L α H : ℝ} (hL : 0 < L) (hH : 0 < H) {m : ℕ}
    (hm : 1 ≤ m) (hcount : H * L / (2 * Real.pi) ≤ m)
    (hbig : 512 * derivMass φ α ^ 2 ≤ 9 * Real.pi * H * L ^ 3 * α ^ 2) :
    derivMass φ α ^ 2 / ((2 * Real.pi / L) ^ 2 * m) ≤ 9 / 1024 * L ^ 4 * α ^ 2 := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  refine tail_le_of_window_length hL hm ?_
  have hstep : 9 * Real.pi ^ 2 * (H * L / (2 * Real.pi)) * L ^ 2 * α ^ 2
      ≤ 9 * Real.pi ^ 2 * m * L ^ 2 * α ^ 2 := by
    have h0 : (0 : ℝ) ≤ 9 * Real.pi ^ 2 * L ^ 2 * α ^ 2 := by positivity
    nlinarith [hcount, sq_nonneg α]
  have hval : 9 * Real.pi ^ 2 * (H * L / (2 * Real.pi)) * L ^ 2 * α ^ 2
      = 9 * Real.pi * H * L ^ 3 * α ^ 2 / 2 := by
    field_simp
  rw [hval] at hstep
  linarith

/-- The offset threshold below which a unit-height window is *not* known to
retain the floor: `|α| ≤ √(512 derivMass²/(9π L³))`. -/
noncomputable def unitHeightThreshold (φ : ℝ → ℝ) (L α : ℝ) : ℝ :=
  Real.sqrt (512 * derivMass φ α ^ 2 / (9 * Real.pi * L ^ 3))

/-- **The unit-height dichotomy (the answer to "is `H = 1` enough?").**

For every hypothetical offset `α`, at least one of the following holds:

* `|α| ≤ unitHeightThreshold φ L α` — the offset is already below the explicit
  threshold `≍ derivMass · L^{-3/2}`; or
* a window of unit ordinate height (any `m ≥ L/2π` retained coordinates) carries
  the full source Gram floor `(81/16384) L⁶ α² ≤ Δ`.

There is no third case: bounded height suffices exactly above the threshold. -/
theorem unit_height_dichotomy {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) (hnn : ∀ t, 0 ≤ φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L)
    {a : ℝ} (ha : 3 * L / 8 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1) (α : ℝ) {m : ℕ}
    (hm : 1 ≤ m) (hcount : L / (2 * Real.pi) ≤ m) :
    |α| ≤ unitHeightThreshold φ L α
      ∨ 81 / 16384 * L ^ 6 * α ^ 2 ≤ finiteGridGramDefect φ (2 * Real.pi / L) α (m + 1) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  by_cases hbig : 512 * derivMass φ α ^ 2 ≤ 9 * Real.pi * L ^ 3 * α ^ 2
  · refine Or.inr ?_
    have htail : derivMass φ α ^ 2 / ((2 * Real.pi / L) ^ 2 * m) ≤ 9 / 1024 * L ^ 4 * α ^ 2 := by
      refine tail_le_of_window_height (H := 1) hL one_pos hm (by simpa using hcount) ?_
      simpa using hbig
    have hfloor := finiteGridGramDefect_source_floor hφ hev hnn hL h2R ha hplat α hm
    have hL2 : (0 : ℝ) < 9 / 16 * L ^ 2 := by positivity
    nlinarith [htail, hfloor, hL2]
  · refine Or.inl ?_
    push_neg at hbig
    have hden : (0 : ℝ) < 9 * Real.pi * L ^ 3 := by positivity
    have hsq : α ^ 2 < 512 * derivMass φ α ^ 2 / (9 * Real.pi * L ^ 3) := by
      rw [lt_div_iff₀ hden]
      linarith
    have habs : |α| ^ 2 < 512 * derivMass φ α ^ 2 / (9 * Real.pi * L ^ 3) := by
      rwa [sq_abs]
    unfold unitHeightThreshold
    have h0 : 0 ≤ 512 * derivMass φ α ^ 2 / (9 * Real.pi * L ^ 3) := by positivity
    nlinarith [Real.sq_sqrt h0, Real.sqrt_nonneg (512 * derivMass φ α ^ 2 / (9 * Real.pi * L ^ 3)),
      abs_nonneg α]

end RiemannAnalytic
