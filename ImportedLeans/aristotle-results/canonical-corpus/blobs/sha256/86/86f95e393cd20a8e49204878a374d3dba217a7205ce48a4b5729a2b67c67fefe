/-
# Even + odd parity assembly

The two preceding modules give, separately, a strict sign for the actual
finite-radius parity minors at small observation radius:

* `OddTaylorDeterminant.exists_radius_oddFiniteRadiusDeterminant_neg`;
* `EvenTaylorDeterminant.exists_radius_evenFiniteRadiusDeterminant_neg`.

The parity-minor ledger needs both **simultaneously**, at one common radius, and
then needs the consequence that the two height-response vectors are linearly
independent in each sector.  That is exactly what this module supplies:

* `exists_radius_both_parity_minors_neg` : a single threshold `r₀ > 0` below
  which *both* minors are strictly negative;

* `parity_responses_linearly_independent` : at such a radius the two-height,
  two-radius response vectors
  `(A_a(r), A_a(2r))`, `(A_p(r), A_p(2r))` (even) and
  `(B_a(r), B_a(2r))`, `(B_p(r), B_p(2r))` (odd)
  are linearly independent pairs in `ℝ²`, i.e. the two heights `a` and `p` are
  genuinely discriminated by the symmetric sample in **both** parity channels.

The counterexample recorded in the ledger — even minor nonzero does not imply
odd minor nonzero — is respected: the two facts are proved independently and
then conjoined, never inferred from one another.

No `sorry`, no `axiom`, no numerical evidence.
-/

import Mathlib
import RiemannAnalytic.EvenTaylorDeterminant

open MeasureTheory Set

namespace RiemannAnalytic
namespace ParityMinorAssembly

open StrictKernelMomentRatio OddTaylorDeterminant EvenTaylorDeterminant

variable {L Cφ a p c d m : ℝ} {φ : ℝ → ℝ}

/-- **Simultaneous strict sign for both parity minors.**  For an admissible taper
(nonnegative, bounded, measurable, with a positive plateau on `(c,d) ⊆ (0,L]`)
and heights `0 < a < p`, there is a common radius threshold below which the even
*and* the odd finite-radius minors are both strictly negative. -/
theorem exists_radius_both_parity_minors_neg
    (hφmeas : Measurable φ) (hφ0 : ∀ u ∈ Ioc (0 : ℝ) L, 0 ≤ φ u)
    (hφb : ∀ u ∈ Ioc (0 : ℝ) L, |φ u| ≤ Cφ)
    (hL : 0 < L) (ha : 0 < a) (hap : a < p)
    (hc : 0 < c) (hcd : c < d) (hdL : d ≤ L) (hm : 0 < m)
    (hplateau : ∀ u ∈ Ioo c d, m ≤ φ u) :
    ∃ r₀ > 0, ∀ r, 0 < r → r < r₀ →
      evenFiniteRadiusDeterminant L φ a p r < 0 ∧
      oddFiniteRadiusDeterminant L φ a p r < 0 := by
  obtain ⟨re, hre, hE⟩ := exists_radius_evenFiniteRadiusDeterminant_neg
    hφmeas hφ0 hφb hL ha hap hc hcd hdL hm hplateau
  obtain ⟨ro, hro, hO⟩ := exists_radius_oddFiniteRadiusDeterminant_neg
    hφmeas hφ0 hφb hL ha hap hc hcd hdL hm hplateau
  refine ⟨min re ro, lt_min hre hro, fun r hr hlt => ⟨?_, ?_⟩⟩
  · exact hE r hr (lt_of_lt_of_le hlt (min_le_left _ _))
  · exact hO r hr (lt_of_lt_of_le hlt (min_le_right _ _))

/-- A `2 × 2` real system with nonzero determinant has linearly independent rows:
the only scalars annihilating both coordinates are zero. -/
theorem indep_of_det_ne_zero {x₁ x₂ y₁ y₂ : ℝ} (h : x₁ * y₂ - x₂ * y₁ ≠ 0)
    {s t : ℝ} (h1 : s * x₁ + t * y₁ = 0) (h2 : s * x₂ + t * y₂ = 0) : s = 0 ∧ t = 0 := by
  have hs : s * (x₁ * y₂ - x₂ * y₁) = 0 := by linear_combination y₂ * h1 - y₁ * h2
  have ht : t * (x₁ * y₂ - x₂ * y₁) = 0 := by linear_combination x₁ * h2 - x₂ * h1
  refine ⟨?_, ?_⟩
  · rcases mul_eq_zero.1 hs with h' | h'
    · exact h'
    · exact absurd h' h
  · rcases mul_eq_zero.1 ht with h' | h'
    · exact h'
    · exact absurd h' h

/-- **Two-height discrimination in both parity channels.**  At any sufficiently
small radius the symmetric two-radius sample separates the heights `a` and `p` in
the even channel *and* in the odd channel: in each sector the only linear
combination of the two height responses that vanishes at both radii is trivial. -/
theorem parity_responses_linearly_independent
    (hφmeas : Measurable φ) (hφ0 : ∀ u ∈ Ioc (0 : ℝ) L, 0 ≤ φ u)
    (hφb : ∀ u ∈ Ioc (0 : ℝ) L, |φ u| ≤ Cφ)
    (hL : 0 < L) (ha : 0 < a) (hap : a < p)
    (hc : 0 < c) (hcd : c < d) (hdL : d ≤ L) (hm : 0 < m)
    (hplateau : ∀ u ∈ Ioo c d, m ≤ φ u) :
    ∃ r₀ > 0, ∀ r, 0 < r → r < r₀ →
      (∀ s t : ℝ,
        s * evenResponse L φ a r + t * evenResponse L φ p r = 0 →
        s * evenResponse L φ a (2 * r) + t * evenResponse L φ p (2 * r) = 0 →
        s = 0 ∧ t = 0) ∧
      (∀ s t : ℝ,
        s * oddResponse L φ a r + t * oddResponse L φ p r = 0 →
        s * oddResponse L φ a (2 * r) + t * oddResponse L φ p (2 * r) = 0 →
        s = 0 ∧ t = 0) := by
  obtain ⟨r₀, hr₀, hboth⟩ := exists_radius_both_parity_minors_neg
    hφmeas hφ0 hφb hL ha hap hc hcd hdL hm hplateau
  refine ⟨r₀, hr₀, fun r hr hlt => ?_⟩
  obtain ⟨hE, hO⟩ := hboth r hr hlt
  constructor
  · intro s t h1 h2
    exact indep_of_det_ne_zero (ne_of_lt hE) h1 h2
  · intro s t h1 h2
    exact indep_of_det_ne_zero (ne_of_lt hO) h1 h2

end ParityMinorAssembly
end RiemannAnalytic
