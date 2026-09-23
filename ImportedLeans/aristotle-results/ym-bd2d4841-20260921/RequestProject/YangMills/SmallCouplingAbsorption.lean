/-
# Row A1 — explicit small-coupling quartic absorption

The last arithmetic step of the Row A1 margin is the absorption of the quartic
interaction debt into half of the Gaussian floor:

    C_β γ⁴ ≤ b/2   ⟹   b/2 ≤ β_Z + β_Int.

Solving `C_β γ⁴ ≤ b/2` for `γ` naively produces a fourth root.  This file gives
a *constructive, root-free* admissible coupling,

    γ_* = (1/2)·b/(C_β + b),

and proves the three facts that make it work, for every `b > 0` and every finite
`C_β ≥ 0`:

* `criticalCoupling_pos`, `criticalCoupling_le_half` : `0 < γ_* ≤ 1/2`;
* `criticalCoupling_mul_le_half` : `C_β·γ_* ≤ b/2`;
* `Cbeta_mul_criticalCoupling_pow_le_half` : `C_β·γ_*⁴ ≤ b/2`, because
  `γ_*⁴ ≤ γ_*` on `(0,1]`.

The consequence (`half_floor_of_smallCoupling`) is that **no numerical value of
`C_β` is needed**: if the source produces *any* finite uniform `C_β` and *any*
uniform Gaussian floor `b_patch > 0`, then a sufficiently small coupling exists
constructively and the shell coefficient is at least `b_patch/2`.

Nothing here asserts a value for `b_patch` or for `C_β`.
-/
import Mathlib

namespace YangMills

/-- The constructive admissible coupling `γ_* = (1/2)·b/(C_β + b)`. -/
noncomputable def criticalCoupling (b Cb : ℝ) : ℝ := b / (2 * (Cb + b))

theorem criticalCoupling_pos {b Cb : ℝ} (hb : 0 < b) (hC : 0 ≤ Cb) :
    0 < criticalCoupling b Cb := by
  have : 0 < 2 * (Cb + b) := by linarith
  exact div_pos hb this

theorem criticalCoupling_le_half {b Cb : ℝ} (hb : 0 < b) (hC : 0 ≤ Cb) :
    criticalCoupling b Cb ≤ 1 / 2 := by
  have hden : 0 < 2 * (Cb + b) := by linarith
  rw [criticalCoupling, div_le_iff₀ hden]
  linarith

theorem criticalCoupling_le_one {b Cb : ℝ} (hb : 0 < b) (hC : 0 ≤ Cb) :
    criticalCoupling b Cb ≤ 1 :=
  le_trans (criticalCoupling_le_half hb hC) (by norm_num)

/-- `C_β·γ_* ≤ b/2`: the *linear* absorption, which is where the choice of
`γ_*` comes from. -/
theorem criticalCoupling_mul_le_half {b Cb : ℝ} (hb : 0 < b) (hC : 0 ≤ Cb) :
    Cb * criticalCoupling b Cb ≤ b / 2 := by
  have hden : 0 < 2 * (Cb + b) := by linarith
  rw [criticalCoupling, mul_div_assoc', div_le_iff₀ hden]
  nlinarith

/-- On `(0,1]` the fourth power is below the value itself. -/
theorem pow_four_le_self {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : x ^ 4 ≤ x := by
  have h3 : x ^ 3 ≤ 1 := pow_le_one₀ hx hx1
  calc x ^ 4 = x * x ^ 3 := by ring
    _ ≤ x * 1 := by nlinarith
    _ = x := by ring

/-- **The quartic absorption, with no fourth root and no numerical `C_β`.** -/
theorem Cbeta_mul_criticalCoupling_pow_le_half {b Cb : ℝ} (hb : 0 < b) (hC : 0 ≤ Cb) :
    Cb * criticalCoupling b Cb ^ 4 ≤ b / 2 := by
  have h1 : criticalCoupling b Cb ^ 4 ≤ criticalCoupling b Cb :=
    pow_four_le_self (le_of_lt (criticalCoupling_pos hb hC)) (criticalCoupling_le_one hb hC)
  have h2 : Cb * criticalCoupling b Cb ^ 4 ≤ Cb * criticalCoupling b Cb :=
    mul_le_mul_of_nonneg_left h1 hC
  exact le_trans h2 (criticalCoupling_mul_le_half hb hC)

/-- **The absorption step itself.**  A Gaussian floor `b` and a quartic
interaction debt whose coefficient satisfies `C_β γ⁴ ≤ b/2` leave at least half
the floor. -/
theorem half_floor_of_quartic_absorption {betaZ betaInt Cb g gamma b : ℝ}
    (hZ : b ≤ betaZ) (hInt : -(Cb * g ^ 4) ≤ betaInt)
    (hC : 0 ≤ Cb) (hg0 : 0 ≤ g) (hg : g ≤ gamma)
    (habs : Cb * gamma ^ 4 ≤ b / 2) :
    b / 2 ≤ betaZ + betaInt := by
  have hpow : g ^ 4 ≤ gamma ^ 4 := pow_le_pow_left₀ hg0 hg 4
  have : Cb * g ^ 4 ≤ Cb * gamma ^ 4 := mul_le_mul_of_nonneg_left hpow hC
  linarith

/-- **The constructive conclusion.**  For *any* uniform floor `b > 0` and *any*
finite `C_β ≥ 0`, the explicit coupling `γ_*` makes the shell coefficient at
least `b/2`. -/
theorem half_floor_of_smallCoupling {betaZ betaInt Cb g b : ℝ}
    (hb : 0 < b) (hC : 0 ≤ Cb)
    (hZ : b ≤ betaZ) (hInt : -(Cb * g ^ 4) ≤ betaInt)
    (hg0 : 0 ≤ g) (hg : g ≤ criticalCoupling b Cb) :
    b / 2 ≤ betaZ + betaInt :=
  half_floor_of_quartic_absorption hZ hInt hC hg0 hg
    (Cbeta_mul_criticalCoupling_pow_le_half hb hC)

/-- Hence strict positivity of the shell coefficient. -/
theorem beta_pos_of_smallCoupling {betaZ betaInt Cb g b : ℝ}
    (hb : 0 < b) (hC : 0 ≤ Cb)
    (hZ : b ≤ betaZ) (hInt : -(Cb * g ^ 4) ≤ betaInt)
    (hg0 : 0 ≤ g) (hg : g ≤ criticalCoupling b Cb) :
    0 < betaZ + betaInt :=
  lt_of_lt_of_le (by linarith) (half_floor_of_smallCoupling hb hC hZ hInt hg0 hg)

/-! ## Boundary tests -/

/-- The coupling really is explicit: at `b = 1/10`, `C_β = 5` one gets
`γ_* = 1/102`. -/
theorem criticalCoupling_example : criticalCoupling (1 / 10) 5 = 1 / 102 := by
  unfold criticalCoupling; norm_num

/-- Smallness is load-bearing: at coupling `1` and `C_β = 5` the quartic debt
exceeds the whole floor `b = 1/10`, so the absorption fails. -/
theorem quartic_absorption_needs_smallness :
    ¬ ((5 : ℝ) * (1 : ℝ) ^ 4 ≤ (1 / 10 : ℝ) / 2) := by norm_num

/-- The absorption threshold degenerates as the floor degenerates: with `b = 0`
the critical coupling is `0`. -/
theorem criticalCoupling_zero_floor (Cb : ℝ) : criticalCoupling 0 Cb = 0 := by
  unfold criticalCoupling; simp

end YangMills
