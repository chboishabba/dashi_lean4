/-
**The prime-side target, written in Gram language.**

The source-native positive object attached to a hypothetical off-line zero `ρ`
is not a loosely defined "imaginary energy" but the Gram determinant of the
one-sided source window,

    Δ_ρ = ‖a_ρ‖² ‖b_ρ‖² − ⟪a_ρ, b_ρ⟫²  ≥  c L⁶ α_ρ²,

the floor being `finiteGridGramDefect_source_floor` (`OneSidedGram.lean`).  The
central prospective theorem is therefore best stated as a **weighted
transverse-area budget**

    ∑_{ρ ∈ P_T} m_ρ² Δ_ρ  ≤  E(T),

where `E(T) = E_prime + E_tail + E_mixed` is whatever the prime side can supply.

This file defines that quantity (`weightedGramSum`) and proves, unconditionally,
what such a budget buys:

* every individual zero is confined to an explicit tube
  `|α_ρ| ≤ √(E / (c L⁶))` (`abs_offset_le_of_budget`, `offset_tube_of_budget`);
* the offsets satisfy a *density* bound `∑_ρ α_ρ² ≤ E / c`
  (`sum_offset_sq_le_of_budget`);
* a budget smaller than a single target's floor rules that target out
  (`budget_lt_floor_excludes`);
* a vanishing budget puts every zero of the family exactly on the critical line
  (`all_on_line_of_budget_nonpos`).

The budget itself is an explicit hypothesis in each statement, never an axiom or
a postulate: producing `E(T)` unconditionally for the actual zeros of `ζ`
remains the missing prime-side theorem, and nothing here asserts it.
-/
import RiemannAnalytic.GramDetectability

namespace RiemannAnalytic

open Finset

/-! ### The weighted Gram sum -/

/-- The weighted transverse-area functional `∑_ρ m_ρ² Δ_ρ` of a finite family of
zeros with multiplicities `mult` and Gram defects `defect`. -/
def weightedGramSum {ι : Type*} (s : Finset ι) (mult defect : ι → ℝ) : ℝ :=
  ∑ i ∈ s, mult i ^ 2 * defect i

theorem weightedGramSum_nonneg {ι : Type*} {s : Finset ι} {mult defect : ι → ℝ}
    (hd : ∀ i ∈ s, 0 ≤ defect i) : 0 ≤ weightedGramSum s mult defect :=
  Finset.sum_nonneg fun i hi => mul_nonneg (sq_nonneg _) (hd i hi)

/-- Each term of the weighted Gram sum is at most the whole sum. -/
theorem term_le_weightedGramSum {ι : Type*} [DecidableEq ι] {s : Finset ι} {mult defect : ι → ℝ}
    (hd : ∀ i ∈ s, 0 ≤ defect i) {i : ι} (hi : i ∈ s) :
    mult i ^ 2 * defect i ≤ weightedGramSum s mult defect :=
  Finset.single_le_sum (f := fun j => mult j ^ 2 * defect j)
    (fun j hj => mul_nonneg (sq_nonneg _) (hd j hj)) hi

/-! ### What a budget buys -/

/-- **Individual tube from a weighted budget.**  If every defect obeys the
quadratic floor `c α_i² ≤ Δ_i` with `c > 0`, every multiplicity is at least one,
and the weighted sum is at most `E`, then each transverse offset obeys
`α_i² ≤ E / c`. -/
theorem offset_sq_le_of_budget {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {mult defect offset : ι → ℝ} {c E : ℝ} (hc : 0 < c)
    (hfloor : ∀ i ∈ s, c * offset i ^ 2 ≤ defect i)
    (hmult : ∀ i ∈ s, 1 ≤ mult i ^ 2)
    (hbudget : weightedGramSum s mult defect ≤ E) {i : ι} (hi : i ∈ s) :
    offset i ^ 2 ≤ E / c := by
  have hdnn : ∀ j ∈ s, 0 ≤ defect j := by
    intro j hj
    have := hfloor j hj
    nlinarith [sq_nonneg (offset j), hc]
  have hterm := term_le_weightedGramSum (mult := mult) (defect := defect) hdnn hi
  have h1 : c * offset i ^ 2 ≤ mult i ^ 2 * defect i := by
    have hfl := hfloor i hi
    have hm := hmult i hi
    nlinarith [sq_nonneg (offset i), hdnn i hi, hc]
  have h2 : c * offset i ^ 2 ≤ E := le_trans h1 (le_trans hterm hbudget)
  rw [le_div_iff₀ hc]
  linarith

/-- The same conclusion in tube form: `|α_i| ≤ √(E / c)`. -/
theorem abs_offset_le_of_budget {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {mult defect offset : ι → ℝ} {c E : ℝ} (hc : 0 < c)
    (hfloor : ∀ i ∈ s, c * offset i ^ 2 ≤ defect i)
    (hmult : ∀ i ∈ s, 1 ≤ mult i ^ 2)
    (hbudget : weightedGramSum s mult defect ≤ E) {i : ι} (hi : i ∈ s) :
    |offset i| ≤ Real.sqrt (E / c) := by
  have h := offset_sq_le_of_budget hc hfloor hmult hbudget hi
  have habs : |offset i| ^ 2 ≤ E / c := by rwa [sq_abs]
  have hnn : 0 ≤ |offset i| := abs_nonneg _
  nlinarith [Real.sq_sqrt (le_trans (sq_nonneg (offset i)) h),
    Real.sqrt_nonneg (E / c), habs]

/-- **Weighted transverse-area density.**  A budget `E` bounds the total squared
offset of the whole family: `∑_i α_i² ≤ E / c`. -/
theorem sum_offset_sq_le_of_budget {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {mult defect offset : ι → ℝ} {c E : ℝ} (hc : 0 < c)
    (hfloor : ∀ i ∈ s, c * offset i ^ 2 ≤ defect i)
    (hmult : ∀ i ∈ s, 1 ≤ mult i ^ 2)
    (hbudget : weightedGramSum s mult defect ≤ E) :
    ∑ i ∈ s, offset i ^ 2 ≤ E / c := by
  have hdnn : ∀ j ∈ s, 0 ≤ defect j := by
    intro j hj
    have := hfloor j hj
    nlinarith [sq_nonneg (offset j), hc]
  have hstep : ∀ i ∈ s, c * offset i ^ 2 ≤ mult i ^ 2 * defect i := by
    intro i hi
    have hfl := hfloor i hi
    have hm := hmult i hi
    nlinarith [sq_nonneg (offset i), hdnn i hi, hc]
  have hsum : ∑ i ∈ s, c * offset i ^ 2 ≤ weightedGramSum s mult defect :=
    Finset.sum_le_sum hstep
  have hmul : c * ∑ i ∈ s, offset i ^ 2 ≤ E := by
    rw [Finset.mul_sum]
    linarith [hsum, hbudget]
  rw [le_div_iff₀ hc]
  linarith

/-- **A budget below a single target's floor rules that target out.**  If the
budget is strictly smaller than the floor already forced by one member of the
family, the hypotheses are contradictory — i.e. that off-line target cannot
occur inside the family. -/
theorem budget_lt_floor_excludes {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {mult defect offset : ι → ℝ} {c E : ℝ} (hc : 0 < c)
    (hfloor : ∀ i ∈ s, c * offset i ^ 2 ≤ defect i)
    (hmult : ∀ i ∈ s, 1 ≤ mult i ^ 2)
    (hbudget : weightedGramSum s mult defect ≤ E) {i : ι} (hi : i ∈ s)
    (hsmall : E < c * offset i ^ 2) : False := by
  have h := offset_sq_le_of_budget hc hfloor hmult hbudget hi
  rw [le_div_iff₀ hc] at h
  linarith

/-- **A vanishing budget puts the whole family on the critical line.** -/
theorem all_on_line_of_budget_nonpos {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {mult defect offset : ι → ℝ} {c E : ℝ} (hc : 0 < c) (hE : E ≤ 0)
    (hfloor : ∀ i ∈ s, c * offset i ^ 2 ≤ defect i)
    (hmult : ∀ i ∈ s, 1 ≤ mult i ^ 2)
    (hbudget : weightedGramSum s mult defect ≤ E) :
    ∀ i ∈ s, offset i = 0 := by
  intro i hi
  have h := offset_sq_le_of_budget hc hfloor hmult hbudget hi
  have hle : offset i ^ 2 ≤ 0 := by
    have : E / c ≤ 0 := div_nonpos_of_nonpos_of_nonneg hE hc.le
    linarith
  have : offset i ^ 2 = 0 := le_antisymm hle (sq_nonneg _)
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this

/-! ### The source instantiation -/

/-- **The source-window floor supplies the hypothesis `hfloor` at the explicit
constant `c = (81/16384) L⁶`.**

For a family of transverse offsets whose lattice tails are absorbed by the
window, the one-sided Gram defect of each member obeys the quadratic floor, so
the weighted budget statements above apply verbatim with
`defect i = finiteGridGramDefect φ (2π/L) (offset i) (m+1)`. -/
theorem source_floor_family {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) (hnn : ∀ t, 0 ≤ φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L)
    {a : ℝ} (ha : 3 * L / 8 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1) {m : ℕ} (hm : 1 ≤ m)
    {ι : Type*} {s : Finset ι} (offset : ι → ℝ)
    (htail : ∀ i ∈ s, derivMass φ (offset i) ^ 2 / ((2 * Real.pi / L) ^ 2 * m)
      ≤ 9 / 1024 * L ^ 4 * offset i ^ 2) :
    ∀ i ∈ s, 81 / 16384 * L ^ 6 * offset i ^ 2
      ≤ finiteGridGramDefect φ (2 * Real.pi / L) (offset i) (m + 1) := by
  intro i hi
  have hfloor := finiteGridGramDefect_source_floor hφ hev hnn hL h2R ha hplat (offset i) hm
  have hL2 : (0 : ℝ) < 9 / 16 * L ^ 2 := by positivity
  have hstep : 81 / 16384 * L ^ 6 * offset i ^ 2
      ≤ 9 / 16 * L ^ 2 * (9 / 512 * L ^ 4 * offset i ^ 2
        - derivMass φ (offset i) ^ 2 / ((2 * Real.pi / L) ^ 2 * m)) := by
    nlinarith [htail i hi, hL2]
  linarith

/-- **The tube from a source-side weighted budget.**

If the weighted Gram sum of a finite family of hypothetical zeros — with the
one-sided source-window defects and multiplicities at least one — is at most
`E`, then every member of the family lies inside the explicit tube

    |α_ρ| ≤ √(E / ((81/16384) L⁶))

around the critical line.  The budget `E` is the hypothesis; it is exactly the
quantity a prime-side second-moment bound would have to supply. -/
theorem source_budget_tube {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) (hnn : ∀ t, 0 ≤ φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L)
    {a : ℝ} (ha : 3 * L / 8 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1) {m : ℕ} (hm : 1 ≤ m)
    {ι : Type*} [DecidableEq ι] {s : Finset ι} (offset mult : ι → ℝ)
    (htail : ∀ i ∈ s, derivMass φ (offset i) ^ 2 / ((2 * Real.pi / L) ^ 2 * m)
      ≤ 9 / 1024 * L ^ 4 * offset i ^ 2)
    (hmult : ∀ i ∈ s, 1 ≤ mult i ^ 2) {E : ℝ}
    (hbudget : weightedGramSum s mult
        (fun i => finiteGridGramDefect φ (2 * Real.pi / L) (offset i) (m + 1)) ≤ E)
    {i : ι} (hi : i ∈ s) :
    |offset i| ≤ Real.sqrt (E / (81 / 16384 * L ^ 6)) := by
  have hc : (0 : ℝ) < 81 / 16384 * L ^ 6 := by positivity
  exact abs_offset_le_of_budget hc
    (source_floor_family hφ hev hnn hL h2R ha hplat hm offset htail) hmult hbudget hi

end RiemannAnalytic
