import Mathlib
import RequestProject.T2vsT3

/-!
# A delta diagram for each panel of the `T₂` against `T₃` plate

`RequestProject/T2vsT3.lean` compares the two sequences

`t₂(m) = τ(2)τ(m) = -24 τ(m)`   and   `t₃(m) = τ(3)τ(m) = 252 τ(m)`

pointwise, in six panels: the two sequences themselves (A), their product (B), their difference
(C), their quotient (D), their power (E) and their remainder (F). Each panel is a *sequence*.
This file turns each panel into a *function on the upper half plane* — its delta diagram — by
feeding the panel's sequence into the same partial `q`-expansion
`DeltaWordGraphs.heckeApprox` that draws `Δ` itself, and says exactly how the resulting picture
is related to the picture of `Δ`.

The answers are not the same for the six panels, and that is the point of the plates:

| panel | series                          | its picture                                                    |
| ----- | ------------------------------- | -------------------------------------------------------------- |
| A     | `t₂`, `t₃`                      | `Δ` scaled by `-24` and by `252`; `21 f₂ = -2 f₃`               |
| B     | `t₂ · t₃ = -6048 τ²`            | `-6048` times the *Hadamard square* `∑ τ(m)² qᵐ`, not `Δ`       |
| C     | `t₂ - t₃ = -276 τ`              | `Δ` scaled by `-276`: a genuine multiple of `Δ`                 |
| D     | `t₂ / t₃`                       | in `ℚ` the constant `-2/21` times `∑ qᵐ`; in `ℤ` minus the mask of `τ(m) > 0` |
| E     | `t₂ ^ t₃`                       | no convergent series; its *logarithm* `\|t₃(m)\| log\|t₂(m)\|` has one |
| F     | `t₂ % t₃`                       | `Δ` cut at the sign of `τ` and its two halves scaled `228` and `-24` |

`diffT_smul_tau` on the one hand, and `prodT_not_smul_tau`, `quotT_not_smul_tau`,
`modT_not_smul_tau` on the other, make the distinction precise: only the difference (and, in
panel A, the two sequences themselves) is a constant multiple of `τ` on the compared range; the
product is quadratic in `τ`, and the quotient and the remainder both look at the *sign* of `τ(m)`
and therefore cannot be any rescaling of it.

Everything is stated on `1 ≤ m ≤ 20`, the range on which `DeltaWordGraphs.wordT3_eq` certifies
the coefficients against the eta product `q ∏ (1 - qᵐ)²⁴`.
-/

namespace T2vsT3Delta

open DeltaGraph DeltaWordGraphs T2vsT3

set_option maxRecDepth 100000
set_option exponentiation.threshold 1000

/-! ## The plotted function of an arbitrary sequence -/

/-- The partial sum `∑_{m=1}^{N} c(m) qᵐ` of a `q`-expansion with arbitrary complex
coefficients: the function drawn in each of the six delta diagrams. For integer `c` this is
`DeltaWordGraphs.heckeApprox`, and for `c = τ` it is `DeltaGraph.deltaApprox`. -/
noncomputable def cApprox (c : ℕ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ m ∈ Finset.range N, c (m + 1) * qParam z ^ (m + 1)

theorem cApprox_int (c : ℕ → ℤ) (N : ℕ) (z : ℂ) :
    cApprox (fun m => (c m : ℂ)) N z = heckeApprox c N z := rfl

theorem cApprox_tau (N : ℕ) (z : ℂ) : cApprox (fun m => (tau m : ℂ)) N z = deltaApprox N z := rfl

/-- Every one of these pictures has horizontal period one, for the same reason `Δ` does. -/
theorem cApprox_periodic (c : ℕ → ℂ) (N : ℕ) (z : ℂ) : cApprox c N (z + 1) = cApprox c N z := by
  simp [cApprox, qParam_add_one]

/-- Only the coefficients up to `N` matter. -/
theorem cApprox_congr {c d : ℕ → ℂ} {N : ℕ} (h : ∀ m, 1 ≤ m → m ≤ N → c m = d m) (z : ℂ) :
    cApprox c N z = cApprox d N z := by
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [h (m + 1) (Nat.le_add_left 1 m) (Finset.mem_range.mp hm)]

/-- A sequence that is `lam` times another one on the plotted range has picture `lam` times the
other's. This one lemma produces every proportionality statement below. -/
theorem cApprox_smul {c d : ℕ → ℂ} {lam : ℂ} {N : ℕ} (h : ∀ m, 1 ≤ m → m ≤ N → c m = lam * d m)
    (z : ℂ) : cApprox c N z = lam * cApprox d N z := by
  rw [cApprox_congr h z, cApprox, cApprox, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring

/-- Pictures add coefficientwise. -/
theorem cApprox_add (c d : ℕ → ℂ) (N : ℕ) (z : ℂ) :
    cApprox (fun m => c m + d m) N z = cApprox c N z + cApprox d N z := by
  rw [cApprox, cApprox, cApprox, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun m _ => by ring

/-! ## Panel A — the two sequences

Both are `Δ` rescaled, by `τ(2)` and by `τ(3)`. The two scales are of opposite sign and in the
ratio `2 : 21`, so the two pictures are anti-parallel: same shape, opposite phase, and one
`10.5` times the other. -/

theorem panelA_T2 (z : ℂ) : heckeApprox wordT2 20 z = (-24 : ℂ) * deltaApprox 20 z := by
  refine heckeApprox_eq_smul (c := wordT2) (lam := -24) (N := 20) (fun m h1 h2 => ?_) z |>.trans
    (by push_cast; ring)
  rw [wordT2_eq m (Finset.mem_Icc.mpr ⟨h1, by omega⟩), tauT_eq_tau h1 (by omega)]

theorem panelA_T3 (z : ℂ) : heckeApprox wordT3 20 z = (252 : ℂ) * deltaApprox 20 z := by
  refine heckeApprox_eq_smul (c := wordT3) (lam := 252) (N := 20) (fun m h1 h2 => ?_) z |>.trans
    (by push_cast; ring)
  rw [wordT3_eq m (Finset.mem_Icc.mpr ⟨h1, h2⟩), tauT_eq_tau h1 (by omega)]

/-- **The two pictures are anti-parallel.** `21 f₂ = -2 f₃` everywhere on the upper half plane:
the pointwise ratio `τ(2)/τ(3) = -2/21` of panel D, seen as one identity between functions. -/
theorem panelA_antiparallel (z : ℂ) :
    21 * heckeApprox wordT2 20 z = -(2 * heckeApprox wordT3 20 z) := by
  rw [panelA_T2, panelA_T3]; ring

/-! ## Panel B — the product

The pointwise product of two `q`-expansions is their Hadamard product, not the product of the
two functions: the picture of panel B is `τ(6) = -6048` times the picture of the *square* of the
coefficient sequence of `Δ`. That series is not a modular form (it is the diagonal that
Rankin–Selberg studies), and its coefficients are all of one sign — negative, because `τ(2)` and
`τ(3)` are of opposite sign. -/

/-- The Hadamard square of `Δ`'s coefficient sequence, `m ↦ τ(m)²`. -/
def tauSqT (m : ℕ) : ℤ := tauT m ^ 2

/-- **The product panel is the Hadamard square, scaled by `τ(6)`.** -/
theorem panelB_eq (z : ℂ) :
    heckeApprox prodT 20 z = (-6048 : ℂ) * heckeApprox tauSqT 20 z := by
  rw [← cApprox_int, ← cApprox_int]
  refine cApprox_smul (lam := (-6048 : ℂ)) (fun m h1 h2 => ?_) z
  rw [prodT_eq (Finset.mem_Icc.mpr ⟨h1, h2⟩), tauSqT]
  push_cast; ring

/-- Every coefficient of the product panel is negative: the two graphs point opposite ways at
every `m`, so the Hadamard product has a constant sign. -/
theorem panelB_coeffs_neg : ∀ m ∈ Finset.Icc 1 20, prodT m < 0 := fun _ hm => prodT_neg hm

/-- The product panel is **not** a rescaling of `Δ`: it is quadratic in `τ`. Witnesses: at
`m = 1` a scale would have to be `-6048`, at `m = 2` it would have to be `145152`. -/
theorem prodT_not_smul_tau : ¬ ∃ c : ℤ, ∀ m ∈ Finset.Icc 1 20, prodT m = c * tauT m := by
  rintro ⟨c, h⟩
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  rw [show prodT 1 = -6048 from by decide, show tauT 1 = 1 from by decide] at h1
  rw [show prodT 2 = -3483648 from by decide, show tauT 2 = -24 from by decide] at h2
  omega

/-! ## Panel C — the difference

The one comparison that stays inside the space: `t₂ - t₃ = (τ(2) - τ(3)) τ`, so the picture of
panel C is the picture of `Δ` scaled by `-276`, turned over because `-276 < 0`. -/

/-- The difference is a constant multiple of `τ` on the whole compared range. -/
theorem diffT_smul_tau : ∀ m ∈ Finset.Icc 1 20, diffT m = -276 * tauT m :=
  fun _ hm => (diffT_eq hm).1

/-- **The difference panel is `Δ` itself, scaled by `τ(2) - τ(3) = -276`.** -/
theorem panelC_eq (z : ℂ) : heckeApprox diffT 20 z = (-276 : ℂ) * deltaApprox 20 z := by
  refine heckeApprox_eq_smul (c := diffT) (lam := -276) (N := 20) (fun m h1 h2 => ?_) z |>.trans
    (by push_cast; ring)
  rw [(diffT_eq (Finset.mem_Icc.mpr ⟨h1, h2⟩)).1, tauT_eq_tau h1 (by omega)]

/-- The difference panel is the picture of panel A's two curves subtracted, as it must be. -/
theorem panelC_sub (z : ℂ) :
    heckeApprox diffT 20 z = heckeApprox wordT2 20 z - heckeApprox wordT3 20 z := by
  rw [panelC_eq, panelA_T2, panelA_T3]; ring

/-! ## Panel D — the quotient

Division throws the scale away, and with it every trace of `Δ`. In `ℚ` the quotient is the
constant `-2/21`, so its picture is that constant times the bare geometric sum `∑ qᵐ`; inside
`ℤ` the rounding leaves only a `0/1` mask recording where `τ(m) > 0`. -/

/-- The mask of the positive coefficients of `Δ`. -/
def posMaskT (m : ℕ) : ℤ := if 0 < tauT m then 1 else 0

/-- **The rational quotient panel is a geometric series.** -/
theorem panelD_rat (z : ℂ) :
    cApprox (fun m => (ratioT m : ℂ)) 20 z = (-2 / 21 : ℂ) * cApprox (fun _ => 1) 20 z := by
  refine cApprox_smul (lam := (-2 / 21 : ℂ)) (fun m h1 h2 => ?_) z
  rw [ratioT_eq (Finset.mem_Icc.mpr ⟨h1, h2⟩)]
  push_cast; ring

/-- **The integer quotient panel is minus a sign mask.** -/
theorem panelD_int (z : ℂ) : heckeApprox quotT 20 z = -heckeApprox posMaskT 20 z := by
  rw [← cApprox_int, ← cApprox_int]
  refine (cApprox_smul (lam := (-1 : ℂ)) (fun m h1 h2 => ?_) z).trans (by ring)
  rw [quotT_eq (Finset.mem_Icc.mpr ⟨h1, h2⟩), posMaskT]
  split <;> push_cast <;> ring

/-- The quotient panel is **not** a rescaling of `Δ`: it sees only the sign of `τ`. -/
theorem quotT_not_smul_tau : ¬ ∃ c : ℤ, ∀ m ∈ Finset.Icc 1 20, quotT m = c * tauT m := by
  rintro ⟨c, h⟩
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  rw [show quotT 1 = -1 from by decide, show tauT 1 = 1 from by decide] at h1
  rw [show quotT 2 = 0 from by decide, show tauT 2 = -24 from by decide] at h2
  omega

/-! ## Panel E — the power

`t₂(m) ^ |t₃(m)|` has hundreds of digits at `m = 1` and grows past every scale afterwards, so
there is no convergent series to draw. Its *logarithm* is perfectly tame, and that is what the
plate plots: `log (t₂ ^ t₃) = |t₃(m)| · log |t₂(m)|`, which is `252 |τ(m)| log (24 |τ(m)|)`. -/

/-- The logarithm of the pointwise power — the coefficient sequence drawn in panel E. -/
noncomputable def powLogCoeff (m : ℕ) : ℝ :=
  ((wordT3 m).natAbs : ℝ) * Real.log |(wordT2 m : ℝ)|

/-- **The power, on a logarithmic scale.** `log (t₂ ^ t₃) = |t₃(m)| log |t₂(m)|`: the exponent is
even, so the power is positive and its logarithm is exactly the plotted coefficient. -/
theorem log_powT {m : ℕ} (hm : m ∈ Finset.Icc 1 20) :
    Real.log ((powT m : ℤ) : ℝ) = powLogCoeff m := by
  have heven : Even (wordT3 m).natAbs := by
    rw [t3_eq hm, Int.natAbs_mul]
    exact Even.mul_right (by decide) _
  have hcast : ((powT m : ℤ) : ℝ) = |(wordT2 m : ℝ)| ^ (wordT3 m).natAbs := by
    rw [powT]
    push_cast
    exact (heven.pow_abs _).symm
  rw [hcast, Real.log_pow, powLogCoeff]

/-- The plotted coefficient in terms of `τ`: `252 |τ(m)| · log (24 |τ(m)|)`. -/
theorem powLogCoeff_eq {m : ℕ} (hm : m ∈ Finset.Icc 1 20) :
    powLogCoeff m = 252 * |(tauT m : ℝ)| * Real.log (24 * |(tauT m : ℝ)|) := by
  have hna : ∀ n : ℤ, ((n.natAbs : ℝ)) = |(n : ℝ)| := by
    intro n
    simp
  have h2 : |(wordT2 m : ℝ)| = 24 * |(tauT m : ℝ)| := by
    rw [t2_eq hm]
    push_cast
    rw [abs_mul]
    norm_num
  have h3 : ((wordT3 m).natAbs : ℝ) = 252 * |(tauT m : ℝ)| := by
    rw [hna, t3_eq hm]
    push_cast
    rw [abs_mul]
    norm_num
  rw [powLogCoeff, h2, h3]

/-- The plotted coefficients of panel E are all strictly positive: `|t₂(m)| ≥ 24 > 1`, so each
logarithm is positive, and the picture never changes sign. -/
theorem powLogCoeff_pos {m : ℕ} (hm : m ∈ Finset.Icc 1 20) : 0 < powLogCoeff m := by
  have hτ : (1 : ℝ) ≤ |(tauT m : ℝ)| := by
    have h : (1 : ℤ) ≤ |tauT m| := Int.one_le_abs (tauT_ne_zero hm)
    calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
      _ ≤ ((|tauT m| : ℤ) : ℝ) := by exact_mod_cast h
      _ = |(tauT m : ℝ)| := by push_cast; ring
  rw [powLogCoeff_eq hm]
  have h24 : (24 : ℝ) * 1 ≤ 24 * |(tauT m : ℝ)| := by linarith
  have hlog : 0 < Real.log (24 * |(tauT m : ℝ)|) := Real.log_pos (by linarith)
  have : (0 : ℝ) < 252 * |(tauT m : ℝ)| := by linarith
  positivity

/-! ## Panel F — the remainder

The remainder cuts `Δ` in two along the sign of `τ` and scales the two halves differently, by
`τ(3) - τ(2) = 228` and by `-τ(2) = -24`. That is why its picture is neither `Δ` nor a multiple
of it, while still being built out of nothing but `Δ`. -/

/-- The positive part of the coefficient sequence of `Δ`. -/
def tauPosT (m : ℕ) : ℤ := if 0 < tauT m then tauT m else 0

/-- The negative part of the coefficient sequence of `Δ`. -/
def tauNegT (m : ℕ) : ℤ := if 0 < tauT m then 0 else tauT m

/-- The two halves add up to `Δ`. -/
theorem tauPosT_add_tauNegT (m : ℕ) : tauPosT m + tauNegT m = tauT m := by
  rw [tauPosT, tauNegT]; split <;> ring

/-- **The remainder, split at the sign of `τ`.** -/
theorem modT_split {m : ℕ} (hm : m ∈ Finset.Icc 1 20) :
    modT m = 228 * tauPosT m - 24 * tauNegT m := by
  rw [modT_eq hm, tauPosT, tauNegT]
  split <;> ring

/-- **The two halves of `Δ`, in the picture.** -/
theorem panelF_halves (z : ℂ) :
    heckeApprox tauPosT 20 z + heckeApprox tauNegT 20 z = deltaApprox 20 z := by
  rw [← cApprox_int, ← cApprox_int, ← cApprox_add, ← cApprox_tau]
  refine cApprox_congr (fun m h1 h2 => ?_) z
  rw [← tauT_eq_tau h1 (by omega), ← tauPosT_add_tauNegT m]
  push_cast; ring

/-- **The remainder panel.** Its picture is the positive half of `Δ` scaled by `228` minus the
negative half scaled by `24`. -/
theorem panelF_eq (z : ℂ) :
    heckeApprox modT 20 z =
      228 * heckeApprox tauPosT 20 z - 24 * heckeApprox tauNegT 20 z := by
  rw [← cApprox_int, ← cApprox_int, ← cApprox_int]
  have hsum : ∀ m, 1 ≤ m → m ≤ 20 →
      ((modT m : ℂ)) = 228 * (tauPosT m : ℂ) + (-24) * (tauNegT m : ℂ) := by
    intro m h1 h2
    rw [modT_split (Finset.mem_Icc.mpr ⟨h1, h2⟩)]
    push_cast; ring
  rw [cApprox_congr hsum z,
    cApprox_add (fun m => 228 * (tauPosT m : ℂ)) (fun m => (-24) * (tauNegT m : ℂ)) 20 z,
    cApprox_smul (c := fun m => 228 * (tauPosT m : ℂ)) (d := fun m => (tauPosT m : ℂ))
      (lam := 228) (fun m _ _ => rfl) z,
    cApprox_smul (c := fun m => (-24 : ℂ) * (tauNegT m : ℂ)) (d := fun m => (tauNegT m : ℂ))
      (lam := -24) (fun m _ _ => rfl) z]
  ring

/-- The remainder panel is **not** a rescaling of `Δ` either: at `m = 1` a scale would have to be
`228`, at `m = 2` it would have to be `-24`. -/
theorem modT_not_smul_tau : ¬ ∃ c : ℤ, ∀ m ∈ Finset.Icc 1 20, modT m = c * tauT m := by
  rintro ⟨c, h⟩
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  rw [show modT 1 = 228 from by decide, show tauT 1 = 1 from by decide] at h1
  rw [show modT 2 = 576 from by decide, show tauT 2 = -24 from by decide] at h2
  omega

/-! ## The six diagrams, side by side

Exactly two of the six panels draw a constant multiple of `Δ`: panel A (twice over) and panel C.
The other three each fail for their own reason — the product is quadratic, the quotient and the
remainder are sign-sensitive, and the power has no convergent series at all. -/

/-- The summary drawn under the six plates. -/
theorem panels_smul_or_not :
    (∀ m ∈ Finset.Icc 1 20, wordT2 m = -24 * tauT m) ∧
      (∀ m ∈ Finset.Icc 1 20, wordT3 m = 252 * tauT m) ∧
      (∀ m ∈ Finset.Icc 1 20, diffT m = -276 * tauT m) ∧
      (¬ ∃ c : ℤ, ∀ m ∈ Finset.Icc 1 20, prodT m = c * tauT m) ∧
      (¬ ∃ c : ℤ, ∀ m ∈ Finset.Icc 1 20, quotT m = c * tauT m) ∧
      (¬ ∃ c : ℤ, ∀ m ∈ Finset.Icc 1 20, modT m = c * tauT m) :=
  ⟨fun _ hm => t2_eq hm, fun _ hm => t3_eq hm, diffT_smul_tau, prodT_not_smul_tau,
    quotT_not_smul_tau, modT_not_smul_tau⟩

end T2vsT3Delta
