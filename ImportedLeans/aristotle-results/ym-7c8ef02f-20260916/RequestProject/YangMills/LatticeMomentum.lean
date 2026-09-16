/-
# Row A1a — literal four-dimensional lattice momentum data

This file fixes, once and for all, the *literal* momentum-space objects that the
whole A1a near/far analysis is phrased in, and proves the elementary identities
and inequalities they satisfy.

Conventions (fixed here and used unchanged downstream).

* A Brillouin-zone point is a map `p : Fin 4 → ℝ` with `|p μ| ≤ 1/2`.
  The physical momentum is `2 π p μ`, i.e. `p` is the momentum in units of the
  inverse lattice spacing divided by `2π`.  With this normalisation the whole
  Brillouin zone is the unit cube `[-1/2, 1/2]^4` and the positive orthant cell
  `[0,1/2]^4` has measure `1/16`.

* The single lattice trigonometric atom is `sinAtom x = sin (π x)`; it is the
  literal `sin(a p_μ /2)` of the Wilson action in the above normalisation.

* `phat x = 2 sinAtom x` is the literal lattice momentum `p̂_μ`, and
  `phatSq p = ∑_μ (p̂_μ)^2` is the literal Wilson inverse propagator scalar
  (the denominator of every one-loop orbit density).

Nothing in this file is an interface: every declaration is an actual real-valued
expression or a proved statement about one.
-/
import Mathlib

namespace YangMills

open Real Finset

/-! ## 1. The literal atoms -/

/-- The literal lattice sine atom `sin(π x)`.  In the normalisation fixed above
this is `sin(a p_μ / 2)` for the physical momentum `2π x`. -/
noncomputable def sinAtom (x : ℝ) : ℝ := Real.sin (π * x)

/-- The literal lattice momentum component `p̂_μ = 2 sin(a p_μ/2)`. -/
noncomputable def phat (x : ℝ) : ℝ := 2 * sinAtom x

/-- The literal Wilson inverse propagator scalar `p̂² = ∑_μ p̂_μ²`. -/
noncomputable def phatSq (p : Fin 4 → ℝ) : ℝ := ∑ μ : Fin 4, (phat (p μ)) ^ 2

@[simp] lemma sinAtom_zero : sinAtom 0 = 0 := by simp [sinAtom]

@[simp] lemma phat_zero : phat 0 = 0 := by simp [phat]

lemma sinAtom_neg (x : ℝ) : sinAtom (-x) = -sinAtom x := by
  simp [sinAtom, mul_neg]

lemma phat_neg (x : ℝ) : phat (-x) = -phat x := by
  simp [phat, sinAtom_neg]

lemma abs_sinAtom_le_one (x : ℝ) : |sinAtom x| ≤ 1 := by
  simpa [sinAtom] using Real.abs_sin_le_one (π * x)

lemma phat_sq_eq (x : ℝ) : (phat x) ^ 2 = 4 * (sinAtom x) ^ 2 := by
  simp only [phat]; ring

lemma phat_sq_le_four (x : ℝ) : (phat x) ^ 2 ≤ 4 := by
  have h : |sinAtom x| ≤ 1 := abs_sinAtom_le_one x
  have h2 : (sinAtom x) ^ 2 ≤ 1 := by
    nlinarith [sq_abs (sinAtom x), abs_nonneg (sinAtom x)]
  rw [phat_sq_eq]; linarith

lemma phatSq_nonneg (p : Fin 4 → ℝ) : 0 ≤ phatSq p :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Every single axis contributes at most `4` and hence `p̂² ≤ 16`. -/
lemma phatSq_le_sixteen (p : Fin 4 → ℝ) : phatSq p ≤ 16 := by
  have hle : phatSq p ≤ ∑ _μ : Fin 4, (4 : ℝ) :=
    Finset.sum_le_sum fun μ _ => phat_sq_le_four (p μ)
  have hsum : (∑ _μ : Fin 4, (4 : ℝ)) = 16 := by simp; norm_num
  linarith [hle, hsum.le, hsum.ge]

/-- A single axis is dominated by the full `p̂²`. -/
lemma phat_sq_le_phatSq (p : Fin 4 → ℝ) (μ : Fin 4) : (phat (p μ)) ^ 2 ≤ phatSq p :=
  Finset.single_le_sum (f := fun ν : Fin 4 => (phat (p ν)) ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ μ)

/-! ## 2. The literal Wilson inverse propagator tensor and its Ward identity -/

/-- The literal tree-level Wilson inverse propagator in transverse form,
`K_{μν}(p) = δ_{μν} p̂² − p̂_μ p̂_ν`.  This is an actual expression, not a field
of a record. -/
noncomputable def wilsonInversePropagator (p : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  (if μ = ν then phatSq p else 0) - phat (p μ) * phat (p ν)

/-- **Ward / transversality identity** for the literal inverse propagator:
`∑_ν p̂_ν K_{μν}(p) = 0`. -/
theorem wilsonInversePropagator_transverse (p : Fin 4 → ℝ) (μ : Fin 4) :
    ∑ ν : Fin 4, phat (p ν) * wilsonInversePropagator p μ ν = 0 := by
  have hsplit : ∀ ν : Fin 4,
      phat (p ν) * wilsonInversePropagator p μ ν
        = (if μ = ν then phat (p ν) * phatSq p else 0)
          - phat (p μ) * (phat (p ν)) ^ 2 := by
    intro ν
    by_cases h : μ = ν <;> simp [wilsonInversePropagator, h] <;> ring
  rw [Finset.sum_congr rfl (fun ν _ => hsplit ν), Finset.sum_sub_distrib]
  have h1 : ∑ ν : Fin 4, (if μ = ν then phat (p ν) * phatSq p else 0)
      = phat (p μ) * phatSq p := by
    simp
  have h2 : ∑ ν : Fin 4, phat (p μ) * (phat (p ν)) ^ 2
      = phat (p μ) * phatSq p := by
    rw [← Finset.mul_sum]; rfl
  rw [h1, h2, sub_self]

/-- The inverse propagator is symmetric. -/
lemma wilsonInversePropagator_symm (p : Fin 4 → ℝ) (μ ν : Fin 4) :
    wilsonInversePropagator p μ ν = wilsonInversePropagator p ν μ := by
  by_cases h : μ = ν
  · simp [h]
  · simp [wilsonInversePropagator, h, Ne.symm h, mul_comm]

/-! ## 3. Jordan's inequality on the atom, and the outer sine gap -/

/-- **Jordan's inequality in the lattice normalisation**: `sin(π x) ≥ 2x` on
`[0, 1/2]`.  (Sharp at both endpoints.) -/
theorem two_mul_le_sinAtom {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    2 * x ≤ sinAtom x := by
  have hpi := Real.pi_pos
  have h := Real.mul_le_sin (x := π * x) (by positivity) (by nlinarith)
  have hid : 2 / π * (π * x) = 2 * x := by field_simp
  simpa [sinAtom, hid] using h

/-- The atom is nonnegative on `[0,1/2]`. -/
lemma sinAtom_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : 0 ≤ sinAtom x :=
  le_trans (by linarith) (two_mul_le_sinAtom h0 h1)

/-- **Outer Brillouin sine gap, in absolute value.**  If an axis leaves the
box of radius `2/5` (and stays inside the Brillouin zone) then its atom has
modulus at least `4/5`. -/
theorem abs_sinAtom_ge_of_far {x : ℝ} (h : 2 / 5 ≤ |x|) (h' : |x| ≤ 1 / 2) :
    4 / 5 ≤ |sinAtom x| := by
  rcases abs_cases x with ⟨hx, _⟩ | ⟨hx, _⟩
  · have h0 : (0:ℝ) ≤ x := by rw [hx] at h; linarith
    have h1 : x ≤ 1 / 2 := by rw [hx] at h'; linarith
    have h2 : 2 / 5 ≤ x := by rw [hx] at h; linarith
    have hj := two_mul_le_sinAtom h0 h1
    have hnn : 0 ≤ sinAtom x := sinAtom_nonneg h0 h1
    rw [abs_of_nonneg hnn]; linarith
  · have hx' : |x| = -x := hx
    have h0 : (0:ℝ) ≤ -x := by rw [hx'] at h; linarith
    have h1 : -x ≤ 1 / 2 := by rw [hx'] at h'; linarith
    have h2 : 2 / 5 ≤ -x := by rw [hx'] at h; linarith
    have hm := two_mul_le_sinAtom h0 h1
    have hnn : 0 ≤ sinAtom (-x) := sinAtom_nonneg h0 h1
    rw [sinAtom_neg] at hm hnn
    rw [abs_of_nonpos (by linarith : sinAtom x ≤ 0)]
    linarith

/-- The gap constant `87/128` used by the far-region budget is implied by the
sharper Jordan constant `4/5`. -/
theorem abs_sinAtom_ge_87_128_of_far {x : ℝ} (h : 2 / 5 ≤ |x|) (h' : |x| ≤ 1 / 2) :
    (87 : ℝ) / 128 ≤ |sinAtom x| :=
  le_trans (by norm_num) (abs_sinAtom_ge_of_far h h')

/-- Consequently a far axis floors its own contribution to `p̂²` by `64/25`
(sharper than the `7569/4096` floor coming from `87/128`). -/
theorem phat_sq_ge_of_far {x : ℝ} (h : 2 / 5 ≤ |x|) (h' : |x| ≤ 1 / 2) :
    (64 : ℝ) / 25 ≤ (phat x) ^ 2 := by
  have h1 : (4:ℝ)/5 ≤ |sinAtom x| := abs_sinAtom_ge_of_far h h'
  have h3 : |sinAtom x| ^ 2 = (sinAtom x) ^ 2 := sq_abs _
  rw [phat_sq_eq, ← h3]
  nlinarith [abs_nonneg (sinAtom x)]

end YangMills
