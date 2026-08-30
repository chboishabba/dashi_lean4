import RiemannAnalytic.OneSidedGram
import RiemannAnalytic.LocalSchur
import RiemannAnalytic.SourceCoefficient

/-!
# Elimination residue = normalized transverse Gram defect

`LocalSchur.lean` proves the variational statements about the Schur complement
in matrix form; `OneSidedGram.lean` defines the transverse Gram defect
`ΔGram(a,b) = (a·a)(b·b) − (a·b)²` that the whole anchored route consumes.  This
short module records the exact identity connecting the two, for the `2 × 2`
Gram matrix of a single pair of directions:

```
    b·b − (a·b)²/(a·a)   =   ΔGram(a,b) / (a·a).
```

The left-hand side is the residue left after **eliminating** the direction `a`
(the Schur complement of the `a`-block in the Gram matrix of `(a,b)`, i.e. the
minimum of the full quadratic form over the eliminated coordinate); the
right-hand side is the transverse Gram defect **normalized** by the energy of
the eliminated direction.  So the anchored transverse defect is not merely a
convenient geometric witness: up to the normalization `1/(a·a)` it *is* the
residue of the elimination.

Consequences proved here:

* `eliminationResidue_eq_gramDefect_div` — the identity itself;
* `eliminationResidue_nonneg` — the residue is nonnegative (Cauchy–Schwarz);
* `eliminationResidue_eq_zero_iff` — it vanishes exactly when the Gram defect
  does, i.e. exactly when `b` is parallel to `a`;
* `eliminationResidue_ge_of_gramDefect_floor` — **floor transport**: any lower
  bound `F ≤ ΔGram(a,b)` together with an energy bound `a·a ≤ E` gives the
  Schur-effective floor `F/E ≤` residue.  This is what an anchored argument
  based on the Schur-effective observable rather than the raw defect would
  consume.

Nothing here proves the Riemann Hypothesis, and nothing here is assumed
elsewhere.
-/

namespace RiemannAnalytic

open Matrix

variable {n : Type*} [Fintype n]

/-- The residue left by eliminating the direction `a` from the pair `(a, b)`:
the Schur complement of the `a`-block in the `2 × 2` Gram matrix of `(a, b)`. -/
noncomputable def eliminationResidue (a b : n → ℝ) : ℝ :=
  (b ⬝ᵥ b) - (a ⬝ᵥ b) ^ 2 / (a ⬝ᵥ a)

/-- **Elimination residue = normalized transverse Gram defect.** -/
theorem eliminationResidue_eq_gramDefect_div (a b : n → ℝ) (ha : a ⬝ᵥ a ≠ 0) :
    eliminationResidue a b = gramDefect a b / (a ⬝ᵥ a) := by
  unfold eliminationResidue gramDefect
  field_simp

/-- The elimination residue is nonnegative. -/
theorem eliminationResidue_nonneg (a b : n → ℝ) (ha : 0 < a ⬝ᵥ a) :
    0 ≤ eliminationResidue a b := by
  rw [eliminationResidue_eq_gramDefect_div a b (ne_of_gt ha)]
  exact div_nonneg (gramDefect_nonneg a b) ha.le

/-- The elimination residue vanishes exactly when the transverse Gram defect
does. -/
theorem eliminationResidue_eq_zero_iff (a b : n → ℝ) (ha : 0 < a ⬝ᵥ a) :
    eliminationResidue a b = 0 ↔ gramDefect a b = 0 := by
  rw [eliminationResidue_eq_gramDefect_div a b (ne_of_gt ha)]
  exact div_eq_zero_iff.trans (or_iff_left (ne_of_gt ha))

/-- **Floor transport to the Schur-effective observable.**  A lower bound for
the transverse Gram defect, together with an upper bound for the energy of the
eliminated direction, is a lower bound for the elimination residue. -/
theorem eliminationResidue_ge_of_gramDefect_floor {a b : n → ℝ} {F E : ℝ}
    (ha : 0 < a ⬝ᵥ a) (haE : a ⬝ᵥ a ≤ E) (hF : F ≤ gramDefect a b) (hF0 : 0 ≤ F) :
    F / E ≤ eliminationResidue a b := by
  have hE : 0 < E := lt_of_lt_of_le ha haE
  rw [eliminationResidue_eq_gramDefect_div a b (ne_of_gt ha)]
  calc F / E ≤ F / (a ⬝ᵥ a) := by
        exact div_le_div_of_nonneg_left hF0 ha haE
    _ ≤ gramDefect a b / (a ⬝ᵥ a) := by
        exact div_le_div_of_nonneg_right hF ha.le

/-! ### What the Schur-effective pivot does to the normalization gate -/

/-- **The elimination residue never exceeds the raw transverse energy.**  This is
the scalar form of `schur_form_le_compression_form`: eliminating a direction can
only *lower* the observable.  Consequently a pivot from the raw anchored defect
to the Schur-effective one can only lower the geometric floor, hence can only
make the normalization gate harder to satisfy — never easier. -/
theorem eliminationResidue_le_transverse (a b : n → ℝ) (ha : 0 < a ⬝ᵥ a) :
    eliminationResidue a b ≤ b ⬝ᵥ b := by
  unfold eliminationResidue
  have : 0 ≤ (a ⬝ᵥ b) ^ 2 / (a ⬝ᵥ a) := by positivity
  linarith

/-- **The Schur-effective pivot does not change the verdict.**  Replacing the
geometric floor constant `c` by `c/E` (which is what a pivot to the
Schur-effective observable does, `E ≥ 1` being an upper bound for the energy of
the eliminated direction) is the same as replacing the source coefficient
`C_src` by `E·C_src`.  Since `E ≥ 1`, a polylogarithmic `C_src` stays
polylogarithmic, and `gate_fails_of_polylog_loss` still applies. -/
theorem schurEffective_gate_fails_of_polylog {N A : ℕ} {c t κ Csrc S E : ℝ}
    (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ)) (hc : 0 < c) (hE : 1 ≤ E)
    (hlow : κ * Real.sqrt N ≤ Csrc * (Real.log N) ^ A * (t ^ 2 * S ^ 2))
    (hCsrc : 0 ≤ Csrc)
    (hthr : c * (2 * ((A : ℝ) + 4)) ^ (A + 4) ≤ 120000 * κ) :
    ¬ (120000 * (Real.log N) ^ 2 * (E * Csrc * t ^ 2 * S ^ 2) < c * (Real.log N) ^ 6) := by
  refine gate_fails_of_polylog_loss (A := A) (Csrc := E * Csrc) hN hc ?_ hthr
  have hstep : Csrc * (Real.log N) ^ A * (t ^ 2 * S ^ 2)
      ≤ E * Csrc * (Real.log N) ^ A * (t ^ 2 * S ^ 2) := by
    have hnn : (0 : ℝ) ≤ Csrc * (Real.log N) ^ A * (t ^ 2 * S ^ 2) := by positivity
    nlinarith [hnn, hE]
  linarith [hlow, hstep]

end RiemannAnalytic
