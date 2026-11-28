import Mathlib

/-!
# Physical R726 signed-defect scaling and exact comparison threshold

The original finite nonzero-output R406 forcing pair is resolvent weighted
by 1/(ν*(input mass sum)), while R722/R723's coherent commutator is the
unlifted original algebraic work. For one FIXED divergence-free Fourier
velocity at physical time 0, projected nonlinear forcing is independent of
the positive viscosity ν, so R406(ν)=R406(1)/ν but Combined(ν)=Combined(1).

The actual 316-incidence Q(i,sqrt2,sqrt3) physical witnesses and exact
strict signs live in Agda #1551
scripts/check_ns_r726_signed_defect_physical_source_exact_20261128.py.
This module is just the exact REAL order-theoretic consequences of that
physical source scaling: a proposed universal zero-defect
R406 <= Combined comparison cannot follow from rate positivity and is
false at some positive viscosities on a fixed physical initial state
with positive R406(1) and positive combined commutator.

The corrected original typed R726/R727 route pays a signed physical
defect ceiling, independent of the Fourier cutoff. No numerical or
continuum NS regularity theorem is asserted.
-/

namespace DASHI.NavierStokes.R726Defect

/-- Positive-viscosity quotient: preserve the physical rate factor, rather
than comparing quantities of different source rate homogeneities. -/
theorem signed_defect_positive_iff
    (r combined ν : ℝ) (hν : 0 < ν) :
    0 < r / ν - combined ↔ ν * combined < r := by
  rw [sub_pos]
  constructor
  · intro h
    have h' := (lt_div_iff₀ hν).mp h
    nlinarith only [h']
  · intro h
    apply (lt_div_iff₀ hν).mpr
    nlinarith only [h]

theorem signed_defect_negative_iff
    (r combined ν : ℝ) (hν : 0 < ν) :
    r / ν - combined < 0 ↔ r < ν * combined := by
  rw [sub_neg]
  constructor
  · intro h
    have h' := (div_lt_iff₀ hν).mp h
    nlinarith only [h']
  · intro h
    apply (div_lt_iff₀ hν).mpr
    nlinarith only [h]

/-- For any genuine positive initial R406 and positive physical coherent
combined work, changing only ν reverses the exact initial signed defect.
The Fourier state is held fixed; only the original physical rate changes. -/
theorem same_source_two_viscosities_opposite_defects
    (r combined : ℝ) (hr : 0 < r) (hc : 0 < combined) :
    ∃ ν₊ ν₋ : ℝ,
      0 < ν₊ ∧ 0 < ν₋ ∧
      0 < r / ν₊ - combined ∧
      r / ν₋ - combined < 0 := by
  refine ⟨r / (2 * combined), 2 * r / combined,
    by positivity, by positivity, ?_, ?_⟩
  · apply (signed_defect_positive_iff _ _ (r / (2 * combined))
      (by positivity)).mpr
    have h : (r / (2 * combined)) * combined = r / 2 := by
      field_simp [ne_of_gt hc]
      ring
    rw [h]
    linarith
  · apply (signed_defect_negative_iff _ _ (2 * r / combined)
      (by positivity)).mpr
    have h : (2 * r / combined) * combined = 2 * r := by
      field_simp [ne_of_gt hc]
      ring
    rw [h]
    linarith

/-- The ratio threshold is a BIDI, not an unconditional sign transfer
from R687's rate-lifted positivity. -/
theorem uncompensated_R726_iff_viscosity_threshold
    (r combined ν : ℝ) (hν : 0 < ν) :
    r / ν ≤ combined ↔ r ≤ ν * combined := by
  simpa [mul_comm] using (div_le_iff₀ hν :
    r / ν ≤ combined ↔ r ≤ combined * ν)

end DASHI.NavierStokes.R726Defect
