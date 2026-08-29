import RequestProject.UniversalTraceRepair
import RequestProject.GF27
import RequestProject.BigFieldSizeScan

/-!
# The twist, in detail: the data behind the six-part series

`RequestProject/UniversalTraceRepair.lean` proves the general statement: the Frobenius orbit
sum `Tr(x) = ∑_{i<k} x^(p^i)` of a field with `p^k` elements restricts on the prime subfield
to the *scalar* `a ↦ k·a`, so when `p ∣ k` it annihilates `𝔽ₚ` and no rescaling `c · Tr` can
bring it back; but twisting the **argument** instead of the value,

`R_c(x) = Tr(c · x)` with `Tr(c) = 1`,

always is a retraction onto `𝔽ₚ`.

This file zooms in on that twist and provides the data that
`RequestProject/TwistSeriesViz.lean` draws as the six animated panels
`svg/twist-1-…svg` … `svg/twist-6-…svg`.  Three layers:

* **The general law** — `scalar_repair_iff_not_dvd`: a rescaling of the orbit sum fixes `1`
  *exactly* when `p ∤ k`.  So "the additive dial is dead" is literally the divisibility
  `p ∣ k`, and that is the precise dividing line between the two repairs.
* **A complete worked field** — everything for `GF(27) = 𝔽₃[t]/(t³ − t − 1)`, which is a dead
  dial (`p = k = 3`), computed and checked by the kernel:
  * `GF27Twist.trace3_coords` : the orbit sum is `x ↦ −x.c₂`, i.e. it reads off the `t²`
    coordinate; in particular it kills the whole prime subfield
    (`GF27Twist.trace3_primeSubfield_zero`) and no rescaling repairs it
    (`GF27Twist.no_rescaling_repair`) — yet it is onto `𝔽₃` with three fibres of nine
    (`GF27Twist.trace3_fibre_card`).
  * `GF27Twist.theTwist = 2t²` has `Tr(2t²) = 1`, and the twisted map is
    `R(x) = x.c₀ + x.c₂` (`GF27Twist.twistMap_coords`): additive, `𝔽₃`-linear, with values in
    `𝔽₃`, onto, idempotent and the identity on `𝔽₃` — a genuine retraction
    (`GF27Twist.twistMap_isRetraction`), equal to the general twisted trace
    (`GF27Twist.twistMap_eq_twistedTrace`).  It is not multiplicative
    (`GF27Twist.twistMap_not_multiplicative`): the repair costs the multiplicative structure.
  * There is not one twist but nine (`GF27Twist.twistConstants_card`), giving nine *distinct*
    retractions (`GF27Twist.twists_pairwise_distinct`); as `𝔽₃`-linear functionals they are
    exactly the nine that send `1 ↦ 1` (`GF27Twist.twistFunctionals_eq`).
* **A census** — over the scan `q = 2 … 1824`, the sizes whose additive dial is dead are
  exactly `4, 16, 27, 64, 256, 729, 1024` (`TwistCensus.deadDialSizes_eq`): seven of the 310
  field sizes, the only ones where the twist is not a convenience but a necessity.  Exactly
  one of them, `q = 729`, is also a failure of the multiplicative orbit product
  (`TwistCensus.deadDial_failing_sizes`).
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Finset

namespace FrobeniusPrimeSubfield

variable {K : Type*} [Field K] {p n : ℕ} [hp : Fact p.Prime] [CharP K p]

omit hp in
/-- **The exact dividing line between the two repairs.**  Some rescaling `x ↦ c · Tr(x)` of
the Frobenius orbit sum fixes `1` — and hence, being `𝔽ₚ`-linear, the whole prime subfield —
if and only if `p ∤ n`.  When `p ∣ n` the dial is dead and only the twist
`x ↦ Tr(c · x)` survives (`twistedTrace_isRetraction`). -/
theorem scalar_repair_iff_not_dvd :
    (∃ c : K, c * frobTrace p n (1 : K) = 1) ↔ ¬ p ∣ n := by
  constructor
  · rintro ⟨c, hc⟩ hpn
    exact no_scalar_repair_of_dvd hpn c hc
  · intro hpn
    refine ⟨(n : K)⁻¹, ?_⟩
    have hn0 : (n : K) ≠ 0 := fun h => hpn ((CharP.cast_eq_zero_iff K p n).1 h)
    rw [frobTrace_of_pow_char_eq_self (one_pow p), mul_one, inv_mul_cancel₀ hn0]

end FrobeniusPrimeSubfield

/-! ## A complete worked example: the twist on `GF(27)` -/

namespace GF27Twist

open FrobeniusPrimeSubfield GF27

/-- The Frobenius orbit sum of `GF(27)`, `Tr(x) = x + x³ + x⁹`, written with the fast
kernel-friendly power so that every statement below is decidable by computation. -/
def trace3 (x : GF27) : GF27 := x + pow' x 3 + pow' x 9

theorem trace3_eq (x : GF27) : trace3 x = x + x ^ 3 + x ^ 9 := by
  simp [trace3, pow'_eq]

/-- The orbit sum of this file is the general Frobenius orbit sum `frobTrace 3 3`. -/
theorem frobTrace_eq_trace3 (x : GF27) : frobTrace 3 3 x = trace3 x := by
  rw [trace3_eq, frobTrace]
  norm_num [Finset.sum_range_succ]

/-- **The orbit sum of `GF(27)` reads off the `t²` coordinate**: `Tr(x) = −x.c₂`. -/
theorem trace3_coords : ∀ x : GF27, trace3 x = ⟨2 * x.c2, 0, 0⟩ := by decide

/-- **The dead dial.**  On the prime subfield `𝔽₃ = {x : x.c₁ = x.c₂ = 0}` the orbit sum of
`GF(27)` is identically zero — it is the scalar `a ↦ 3a`, and `3 = 0` in characteristic `3`. -/
theorem trace3_primeSubfield_zero : ∀ x : GF27, x.c1 = 0 → x.c2 = 0 → trace3 x = 0 := by decide

/-- Consequently **no rescaling of the orbit sum repairs it**: `c · Tr(1) = 0 ≠ 1` for every
scalar `c`.  (The general statement is `no_scalar_repair_of_dvd`.) -/
theorem no_rescaling_repair : ∀ c : GF27, c * trace3 1 ≠ 1 := by decide

/-- Even so the orbit sum is **onto** `𝔽₃`, with all three fibres of the same size `9`: it is
not small, it is merely aimed wrongly. -/
theorem trace3_fibre_card : ∀ a : GF27, a.c1 = 0 → a.c2 = 0 →
    (univ.filter fun x : GF27 => trace3 x = a).card = 9 := by decide

/-! ### The twisting constants -/

/-- The legitimate twists: the elements `c` with `Tr(c) = 1`. -/
def twistConstants : Finset GF27 := univ.filter fun c => trace3 c = 1

/-- There are nine of them — a whole affine plane of twists, not one. -/
theorem twistConstants_card : twistConstants.card = 9 := by decide

/-- Explicitly, the twists are the elements whose `t²` coordinate is `2`. -/
theorem mem_twistConstants_iff : ∀ c : GF27, c ∈ twistConstants ↔ c.c2 = 2 := by decide

/-- The twist used in the pictures: `c = 2t²`. -/
def theTwist : GF27 := ⟨0, 0, 2⟩

theorem trace3_theTwist : trace3 theTwist = 1 := by decide

/-! ### The twisted map -/

/-- The twisted orbit sum `R(x) = Tr(c · x)` of `GF(27)` for `c = 2t²`. -/
def twistMap (x : GF27) : GF27 := trace3 (theTwist * x)

/-- **What the twist does in coordinates**: `R(x) = x.c₀ + x.c₂`.  Where the untwisted orbit
sum saw only the `t²` coordinate — and so was blind to `𝔽₃` — the twisted one sees the
constant coordinate as well. -/
theorem twistMap_coords : ∀ x : GF27, twistMap x = ⟨x.c0 + x.c2, 0, 0⟩ := by decide

theorem twistMap_mem_primeSubfield : ∀ x : GF27, (twistMap x).c1 = 0 ∧ (twistMap x).c2 = 0 := by
  decide

/-- **The repair**: the twisted map is the identity on the prime subfield. -/
theorem twistMap_id_on_primeSubfield : ∀ x : GF27, x.c1 = 0 → x.c2 = 0 → twistMap x = x := by
  decide

theorem twistMap_add : ∀ x y : GF27, twistMap (x + y) = twistMap x + twistMap y := by
  decide +kernel

theorem twistMap_smul : ∀ a x : GF27, a.c1 = 0 → a.c2 = 0 →
    twistMap (a * x) = a * twistMap x := by decide +kernel

theorem twistMap_idempotent : ∀ x : GF27, twistMap (twistMap x) = twistMap x := by
  decide +kernel

theorem twistMap_surjective : ∀ a : GF27, a.c1 = 0 → a.c2 = 0 → ∃ x : GF27, twistMap x = a := by
  decide

/-- Each of the three fibres of the repaired map again has nine elements. -/
theorem twistMap_fibre_card : ∀ a : GF27, a.c1 = 0 → a.c2 = 0 →
    (univ.filter fun x : GF27 => twistMap x = a).card = 9 := by decide

/-- **`R(x) = Tr(2t² · x)` is an additive retraction of `GF(27)` onto `𝔽₃`**: additive,
`𝔽₃`-linear, with values in `𝔽₃`, onto `𝔽₃`, the identity there, and idempotent. -/
theorem twistMap_isRetraction :
    (∀ x y : GF27, twistMap (x + y) = twistMap x + twistMap y) ∧
    (∀ a x : GF27, a.c1 = 0 → a.c2 = 0 → twistMap (a * x) = a * twistMap x) ∧
    (∀ x : GF27, (twistMap x).c1 = 0 ∧ (twistMap x).c2 = 0) ∧
    (∀ a : GF27, a.c1 = 0 → a.c2 = 0 → ∃ x : GF27, twistMap x = a) ∧
    (∀ a : GF27, a.c1 = 0 → a.c2 = 0 → twistMap a = a) ∧
    (∀ x : GF27, twistMap (twistMap x) = twistMap x) :=
  ⟨twistMap_add, twistMap_smul, twistMap_mem_primeSubfield, twistMap_surjective,
    twistMap_id_on_primeSubfield, twistMap_idempotent⟩

/-- **What the twist costs.**  The repaired map is not multiplicative: `R(t² · t) = 1` while
`R(t²) · R(t) = 0`.  (It cannot be: a multiplicative retraction of `GF(27)` onto `𝔽₃` is the
orbit product, and that one is not additive.) -/
theorem twistMap_not_multiplicative :
    twistMap ((⟨0, 0, 1⟩ : GF27) * ⟨0, 1, 0⟩) ≠ twistMap ⟨0, 0, 1⟩ * twistMap ⟨0, 1, 0⟩ := by
  decide

/-- The concrete twisted map is the general twisted trace of
`RequestProject/UniversalTraceRepair.lean`. -/
theorem twistMap_eq_twistedTrace (x : GF27) : twistMap x = twistedTrace 3 3 theTwist x := by
  rw [twistedTrace, frobTrace_eq_trace3, twistMap]

/-- …and therefore the abstract retraction statement holds for it, on the nose. -/
theorem twistMap_retraction_abstract :
    (∀ x y : GF27, twistMap (x + y) = twistMap x + twistMap y) ∧
      (∀ a x : GF27, a ^ 3 = a → twistMap (a * x) = a * twistMap x) ∧
      (∀ x : GF27, twistMap x ∈ Set.range (primeSubfieldHom GF27 3)) ∧
      (∀ a ∈ Set.range (primeSubfieldHom GF27 3), twistMap a = a) ∧
      (∀ a ∈ Set.range (primeSubfieldHom GF27 3), ∃ x : GF27, twistMap x = a) := by
  have hc : frobTrace 3 3 theTwist = 1 := by rw [frobTrace_eq_trace3]; exact trace3_theTwist
  obtain ⟨h1, h2, h3, h4, h5⟩ := twistedTrace_isRetraction (p := 3) (n := 3) GF27.card_eq hc
  refine ⟨fun x y => ?_, fun a x ha => ?_, fun x => ?_, fun a ha => ?_, fun a ha => ?_⟩
  · simp only [twistMap_eq_twistedTrace]; exact h1 x y
  · simp only [twistMap_eq_twistedTrace]; exact h2 a x ha
  · simp only [twistMap_eq_twistedTrace]; exact h3 x
  · simp only [twistMap_eq_twistedTrace]; exact h4 a ha
  · obtain ⟨x, hx⟩ := h5 a ha
    exact ⟨x, by simp only [twistMap_eq_twistedTrace]; exact hx⟩

/-! ### The space of twists -/

/-- Different twists give genuinely different retractions. -/
theorem twists_pairwise_distinct : ∀ c ∈ twistConstants, ∀ d ∈ twistConstants, c ≠ d →
    ∃ x : GF27, trace3 (c * x) ≠ trace3 (d * x) := by decide +kernel

/-- Each twist `c`, read as an `𝔽₃`-linear functional, is recorded by its values on the basis
`1, t, t²`: `(c, R_c(1), R_c(t), R_c(t²))`. -/
def twistFunctionals : List (GF27 × GF27 × GF27 × GF27) :=
  (enum.filter fun c => trace3 c = 1).map fun c =>
    (c, trace3 (c * 1), trace3 (c * ⟨0, 1, 0⟩), trace3 (c * ⟨0, 0, 1⟩))

/-- The nine twists, listed in the order of `GF27.enum`. -/
theorem twistFunctionals_length : twistFunctionals.length = 9 := by decide

/-- **The nine twists are exactly the nine `𝔽₃`-linear functionals sending `1 ↦ 1`**: the
first value is always `1`, and the other two run over all nine pairs. -/
theorem twistFunctionals_eq :
    twistFunctionals.map (fun r => (r.1.c2.val, r.1.c1.val, r.1.c0.val,
        r.2.1.c0.val, r.2.2.1.c0.val, r.2.2.2.c0.val)) =
      [(2, 0, 0, 1, 0, 1), (2, 1, 0, 1, 2, 1), (2, 2, 0, 1, 1, 1),
       (2, 0, 1, 1, 0, 0), (2, 1, 1, 1, 2, 0), (2, 2, 1, 1, 1, 0),
       (2, 0, 2, 1, 0, 2), (2, 1, 2, 1, 2, 2), (2, 2, 2, 1, 1, 2)] := by
  decide

end GF27Twist

/-! ## The census: where the twist is indispensable -/

namespace TwistCensus

open BigFieldSizeScan

/-- The field sizes `q = p^k ≤ 1824` whose **additive dial is dead**, i.e. `p ∣ k`: exactly
those where the orbit sum annihilates the prime subfield and only the twist repairs it. -/
def deadDialSizes : List ℕ :=
  bigScan.filterMap fun r =>
    match r.2 with
    | some (p, k, _) => if p ∣ k then some r.1 else none
    | none => none

/-- **Seven of the 310 field sizes below 1825 have a dead additive dial**:
`4 = 2², 16 = 2⁴, 27 = 3³, 64 = 2⁶, 256 = 2⁸, 729 = 3⁶, 1024 = 2¹⁰`. -/
theorem deadDialSizes_eq : deadDialSizes = [4, 16, 27, 64, 256, 729, 1024] := by
  decide +kernel

/-- Only one of the seven, `q = 729 = 3⁶`, is also a failure of the multiplicative orbit
product; it is the size where the picture `svg/repair-gears-3d.svg` says "twist instead". -/
theorem deadDial_failing_sizes :
    (bigScan.filterMap fun r =>
      match r.2 with
      | some (p, k, d) => if p ∣ k ∧ d ≠ 0 then some (r.1, p, k, d) else none
      | none => none) = [(729, 3, 6, 1)] := by
  decide +kernel

end TwistCensus
