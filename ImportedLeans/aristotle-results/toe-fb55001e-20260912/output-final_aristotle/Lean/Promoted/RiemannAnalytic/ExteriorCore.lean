/-
# G21 — the pole-quotiented two-channel exterior observable, exact algebra

G20 (`PoleErrorAutopsy.lean`) closed the one-channel route: after exact
subtraction of the deterministic pole term, the literal transported residual is
a linear functional of the Chebyshev discrepancy, and a green gate there is an
RH-strength estimate.  The post-G20 proposal is to stop refining the *one*
arithmetic observer and instead build a genuinely relational, two-channel
observable, quotienting out the known common (pole) mode and measuring the
orientation of what is left.

This module contains the **exact algebra** of that proposal; no estimates
occur here.

* `wedge2` is the naive two-point, two-channel determinant.  Its exact
  expansion `wedge2_pole_expansion` shows that the pole/error *mixed* terms
  `c₁ (m ∧ E₂) + c₂ (E₁ ∧ m)` survive, and
  `wedge2_mixed_terms_survive` exhibits data where they are nonzero: the raw
  `2 × 2` determinant does **not** annihilate the pole response.

* `augDet3` is the three-sample determinant augmented by the known common
  profile `m` as a third row.  `augDet3_pole_annihilation` is the exact
  statement that both `M ∧ M` and `M ∧ E` disappear:
  `det (c₁ m + E₁, c₂ m + E₂, m) = det (E₁, E₂, m)` — an identity, not an
  asymptotic.

* `augDet4` is the four-sample determinant augmented by **two** nuisance rows.
  This is needed for the contrastive-derivative channel pair, whose two pole
  responses are `m` and `m′` and are therefore *not* a rank-one family (see
  `ExteriorGate.lean`); with two nuisance rows the annihilation is again exact
  (`augDet4_pole_annihilation`).

* `compensatedPair` is the equivalent "exact quotient" presentation
  `T_{ij} = m_j S(x_i) − m_i S(x_j) = m_j E(x_i) − m_i E(x_j)`
  (`compensatedPair_eq_error`).

The dimension count behind the design is `#samples − #nuisance rows ≥ 2`:
two samples minus a one-dimensional common mode leaves one transverse
dimension, in which no nontrivial 2-form exists.
-/
import Mathlib

open Matrix

namespace RiemannAnalytic

noncomputable section

/-! ## Two-sample, two-channel wedge (the naive proposal) -/

/-- The naive two-point two-channel determinant
`S₁(x₁)S₂(x₂) − S₁(x₂)S₂(x₁)`, with `u` the samples of channel 1 and `w` the
samples of channel 2. -/
def wedge2 (u w : Fin 2 → ℂ) : ℂ := u 0 * w 1 - u 1 * w 0

theorem wedge2_self (u : Fin 2 → ℂ) : wedge2 u u = 0 := by
  simp [wedge2]; ring

theorem wedge2_antisymm (u w : Fin 2 → ℂ) : wedge2 u w = -wedge2 w u := by
  simp [wedge2]; ring

/-- Exact expansion of the naive wedge when both channels carry the same
rank-one common mode `m`: the `M ∧ M` term dies, but the two mixed terms
`c₁ (m ∧ E₂)` and `c₂ (E₁ ∧ m)` survive. -/
theorem wedge2_pole_expansion (c₁ c₂ : ℂ) (m E₁ E₂ : Fin 2 → ℂ) :
    wedge2 (fun j => c₁ * m j + E₁ j) (fun j => c₂ * m j + E₂ j)
      = wedge2 E₁ E₂ + c₁ * wedge2 m E₂ + c₂ * wedge2 E₁ m := by
  simp [wedge2]; ring

/-- The naive two-point determinant does **not** annihilate the pole response:
there are data for which the mixed pole/error terms are nonzero.  (Channel
coefficients `c₁ = c₂ = 1`, common mode `m = (1,0)`, errors `E₁ = 0`,
`E₂ = (0,1)`.) -/
theorem wedge2_mixed_terms_survive :
    ∃ (c₁ c₂ : ℂ) (m E₁ E₂ : Fin 2 → ℂ),
      wedge2 (fun j => c₁ * m j + E₁ j) (fun j => c₂ * m j + E₂ j) ≠ wedge2 E₁ E₂ := by
  refine ⟨1, 1, ![1, 0], ![0, 0], ![0, 1], ?_⟩
  simp [wedge2]

/-! ## Three samples, one nuisance row -/

/-- The augmented three-sample determinant with rows: channel 1 samples,
channel 2 samples, and the known common profile `m`. -/
def augDet3 (u w m : Fin 3 → ℂ) : ℂ := Matrix.det (Matrix.of ![u, w, m])

theorem augDet3_eq (u w m : Fin 3 → ℂ) :
    augDet3 u w m = u 0 * (w 1 * m 2 - w 2 * m 1) - u 1 * (w 0 * m 2 - w 2 * m 0)
      + u 2 * (w 0 * m 1 - w 1 * m 0) := by
  simp [augDet3, Matrix.det_fin_three]
  ring

theorem augDet3_add_left (u v w m : Fin 3 → ℂ) :
    augDet3 (u + v) w m = augDet3 u w m + augDet3 v w m := by
  simp [augDet3_eq]; ring

theorem augDet3_smul_left (c : ℂ) (u w m : Fin 3 → ℂ) :
    augDet3 (c • u) w m = c * augDet3 u w m := by
  simp [augDet3_eq, Pi.smul_apply, smul_eq_mul]; ring

theorem augDet3_antisymm (u w m : Fin 3 → ℂ) : augDet3 u w m = -augDet3 w u m := by
  simp [augDet3_eq]; ring

theorem augDet3_self (u m : Fin 3 → ℂ) : augDet3 u u m = 0 := by
  simp [augDet3_eq]; ring

theorem augDet3_nuisance_left (w m : Fin 3 → ℂ) : augDet3 m w m = 0 := by
  simp [augDet3_eq]; ring

theorem augDet3_nuisance_right (u m : Fin 3 → ℂ) : augDet3 u m m = 0 := by
  simp [augDet3_eq]; ring

/-- **Lemma 2 of the G21 experiment, three-sample form.**  If both channel
responses carry the *same* rank-one common mode `m`, the augmented determinant
annihilates the common mode **and** all mixed common/residual terms exactly:
`det (c₁m + E₁, c₂m + E₂, m) = det (E₁, E₂, m)`.  No asymptotics, no
majorization. -/
theorem augDet3_pole_annihilation (c₁ c₂ : ℂ) (m E₁ E₂ : Fin 3 → ℂ) :
    augDet3 (fun j => c₁ * m j + E₁ j) (fun j => c₂ * m j + E₂ j) m
      = augDet3 E₁ E₂ m := by
  simp [augDet3_eq]; ring

/-! ## The equivalent compensated (exact quotient) presentation -/

/-- The exactly compensated pair vector `T_{ij} = m_j S(x_i) − m_i S(x_j)`. -/
def compensatedPair (S m : Fin 3 → ℂ) (i j : Fin 3) : ℂ := m j * S i - m i * S j

/-- Compensation removes the common mode identically: with `S = c·m + E` the
compensated pair depends only on the residual `E`. -/
theorem compensatedPair_eq_error (c : ℂ) (m E : Fin 3 → ℂ) (i j : Fin 3) :
    compensatedPair (fun k => c * m k + E k) m i j = compensatedPair E m i j := by
  simp [compensatedPair]; ring

/-! ## Four samples, two nuisance rows -/

/-- The augmented four-sample determinant with rows: channel 1 samples,
channel 2 samples, and the two known nuisance profiles `p`, `q`. -/
def augDet4 (u w p q : Fin 4 → ℂ) : ℂ := Matrix.det (Matrix.of ![u, w, p, q])

private theorem of4_updateRow_zero (r₀ r₁ r₂ r₃ a : Fin 4 → ℂ) :
    Matrix.updateRow (Matrix.of ![r₀, r₁, r₂, r₃]) 0 a = Matrix.of ![a, r₁, r₂, r₃] := by
  ext i j; fin_cases i <;> simp

private theorem of4_updateRow_one (r₀ r₁ r₂ r₃ a : Fin 4 → ℂ) :
    Matrix.updateRow (Matrix.of ![r₀, r₁, r₂, r₃]) 1 a = Matrix.of ![r₀, a, r₂, r₃] := by
  ext i j; fin_cases i <;> simp

/-- Adding a multiple of the third row to the first leaves `augDet4` unchanged. -/
theorem augDet4_add_smul_row2_to_row0 (c : ℂ) (u w p q : Fin 4 → ℂ) :
    augDet4 (fun j => u j + c * p j) w p q = augDet4 u w p q := by
  have h := Matrix.det_updateRow_add_smul_self (Matrix.of ![u, w, p, q])
      (i := (0 : Fin 4)) (j := (2 : Fin 4)) (by decide) c
  have hrow : (Matrix.of ![u, w, p, q] : Matrix (Fin 4) (Fin 4) ℂ) 0
      + c • (Matrix.of ![u, w, p, q] : Matrix (Fin 4) (Fin 4) ℂ) 2
      = fun j => u j + c * p j := by
    funext j; simp
  rw [hrow, of4_updateRow_zero] at h
  exact h

/-- Adding a multiple of the fourth row to the first leaves `augDet4` unchanged. -/
theorem augDet4_add_smul_row3_to_row0 (c : ℂ) (u w p q : Fin 4 → ℂ) :
    augDet4 (fun j => u j + c * q j) w p q = augDet4 u w p q := by
  have h := Matrix.det_updateRow_add_smul_self (Matrix.of ![u, w, p, q])
      (i := (0 : Fin 4)) (j := (3 : Fin 4)) (by decide) c
  have hrow : (Matrix.of ![u, w, p, q] : Matrix (Fin 4) (Fin 4) ℂ) 0
      + c • (Matrix.of ![u, w, p, q] : Matrix (Fin 4) (Fin 4) ℂ) 3
      = fun j => u j + c * q j := by
    funext j; simp
  rw [hrow, of4_updateRow_zero] at h
  exact h

/-- Adding a multiple of the third row to the second leaves `augDet4` unchanged. -/
theorem augDet4_add_smul_row2_to_row1 (c : ℂ) (u w p q : Fin 4 → ℂ) :
    augDet4 u (fun j => w j + c * p j) p q = augDet4 u w p q := by
  have h := Matrix.det_updateRow_add_smul_self (Matrix.of ![u, w, p, q])
      (i := (1 : Fin 4)) (j := (2 : Fin 4)) (by decide) c
  have hrow : (Matrix.of ![u, w, p, q] : Matrix (Fin 4) (Fin 4) ℂ) 1
      + c • (Matrix.of ![u, w, p, q] : Matrix (Fin 4) (Fin 4) ℂ) 2
      = fun j => w j + c * p j := by
    funext j; simp
  rw [hrow, of4_updateRow_one] at h
  exact h

/-- Adding a multiple of the fourth row to the second leaves `augDet4` unchanged. -/
theorem augDet4_add_smul_row3_to_row1 (c : ℂ) (u w p q : Fin 4 → ℂ) :
    augDet4 u (fun j => w j + c * q j) p q = augDet4 u w p q := by
  have h := Matrix.det_updateRow_add_smul_self (Matrix.of ![u, w, p, q])
      (i := (1 : Fin 4)) (j := (3 : Fin 4)) (by decide) c
  have hrow : (Matrix.of ![u, w, p, q] : Matrix (Fin 4) (Fin 4) ℂ) 1
      + c • (Matrix.of ![u, w, p, q] : Matrix (Fin 4) (Fin 4) ℂ) 3
      = fun j => w j + c * q j := by
    funext j; simp
  rw [hrow, of4_updateRow_one] at h
  exact h

/-- **Lemma 2 of the G21 experiment, four-sample form.**  With the two known
nuisance profiles `p, q` adjoined as rows, any component of either channel in
`span {p, q}` is annihilated exactly, together with all mixed terms:
`det (c₁p + d₁q + E₁, c₂p + d₂q + E₂, p, q) = det (E₁, E₂, p, q)`.
This is the version required by the contrastive-derivative channel pair, whose
pole responses are the two independent profiles `m` and `m′`. -/
theorem augDet4_pole_annihilation (c₁ d₁ c₂ d₂ : ℂ) (p q E₁ E₂ : Fin 4 → ℂ) :
    augDet4 (fun j => c₁ * p j + d₁ * q j + E₁ j)
      (fun j => c₂ * p j + d₂ * q j + E₂ j) p q = augDet4 E₁ E₂ p q := by
  have e₁ : (fun j => c₁ * p j + d₁ * q j + E₁ j)
      = fun j => ((fun k => E₁ k + c₁ * p k) j) + d₁ * q j := by
    funext j; ring
  have e₂ : (fun j => c₂ * p j + d₂ * q j + E₂ j)
      = fun j => ((fun k => E₂ k + c₂ * p k) j) + d₂ * q j := by
    funext j; ring
  rw [e₁, e₂, augDet4_add_smul_row3_to_row0, augDet4_add_smul_row2_to_row0,
    augDet4_add_smul_row3_to_row1, augDet4_add_smul_row2_to_row1]

theorem augDet4_add_left (u v w p q : Fin 4 → ℂ) :
    augDet4 (u + v) w p q = augDet4 u w p q + augDet4 v w p q := by
  have h := Matrix.det_updateRow_add (Matrix.of ![u, w, p, q]) 0 u v
  rw [of4_updateRow_zero, of4_updateRow_zero, of4_updateRow_zero] at h
  exact h

theorem augDet4_smul_left (c : ℂ) (u w p q : Fin 4 → ℂ) :
    augDet4 (c • u) w p q = c * augDet4 u w p q := by
  have h := Matrix.det_updateRow_smul (Matrix.of ![u, w, p, q]) 0 c u
  rw [of4_updateRow_zero, of4_updateRow_zero] at h
  exact h

theorem augDet4_add_right (u w v p q : Fin 4 → ℂ) :
    augDet4 u (w + v) p q = augDet4 u w p q + augDet4 u v p q := by
  have h := Matrix.det_updateRow_add (Matrix.of ![u, w, p, q]) 1 w v
  rw [of4_updateRow_one, of4_updateRow_one, of4_updateRow_one] at h
  exact h

theorem augDet4_smul_right (c : ℂ) (u w p q : Fin 4 → ℂ) :
    augDet4 u (c • w) p q = c * augDet4 u w p q := by
  have h := Matrix.det_updateRow_smul (Matrix.of ![u, w, p, q]) 1 c w
  rw [of4_updateRow_one, of4_updateRow_one] at h
  exact h

theorem augDet4_self (u p q : Fin 4 → ℂ) : augDet4 u u p q = 0 := by
  refine Matrix.det_zero_of_row_eq (i := (0 : Fin 4)) (j := (1 : Fin 4)) (by decide) ?_
  funext j; simp

theorem augDet4_nuisance_left (w p q : Fin 4 → ℂ) : augDet4 p w p q = 0 := by
  refine Matrix.det_zero_of_row_eq (i := (0 : Fin 4)) (j := (2 : Fin 4)) (by decide) ?_
  funext j; simp

theorem augDet4_nuisance_left' (w p q : Fin 4 → ℂ) : augDet4 q w p q = 0 := by
  refine Matrix.det_zero_of_row_eq (i := (0 : Fin 4)) (j := (3 : Fin 4)) (by decide) ?_
  funext j; simp

theorem augDet4_antisymm (u w p q : Fin 4 → ℂ) : augDet4 u w p q = -augDet4 w u p q := by
  have h0 : augDet4 (u + w) (u + w) p q = 0 := augDet4_self _ _ _
  rw [augDet4_add_left, augDet4_add_right, augDet4_add_right, augDet4_self,
    augDet4_self] at h0
  linear_combination h0

end

end RiemannAnalytic
