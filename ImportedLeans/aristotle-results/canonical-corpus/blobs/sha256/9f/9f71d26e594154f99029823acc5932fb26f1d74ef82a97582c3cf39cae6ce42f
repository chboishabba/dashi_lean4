/-
# Strict height separation for an actual off-line zeta zero, and the capstone

The parity-minor chain is driven by two heights: the zero height

  `a = |Re ρ - 1/2|`

and the pole height `p = 1/2`.  The abstract closed-strip inequalities only give
`0 ≤ a ≤ 1/2`.  The *actual* zeta specialization is strictly better: a
nontrivial zero satisfies `0 < Re ρ < 1`, so an **off-line** zero has

  `0 < a < 1/2`,

which is precisely the strict separation the `TP₂` mechanism needs.

`offline_zero_strict_height_separation` records that, and
`offline_zero_parity_transversality` is the capstone: for an actual off-line
nontrivial zero of `riemannZeta` and any admissible taper, the four symmetric
samples discriminate the zero directions from the two pole directions at all
sufficiently small radii.

Strict height separation is *not* itself promoted to response-vector
independence — the independence comes from the proved TP₂/moment/Taylor chain,
with the strict inequality only supplying its hypothesis `a < p`.

No `sorry`, no `axiom`, no numerical evidence.
-/

import Mathlib
import RiemannAnalytic.PoleQuotientTransversality

open MeasureTheory Set

namespace RiemannAnalytic
namespace ActualZetaHeightSeparation

open StrictKernelMomentRatio OddTaylorDeterminant EvenTaylorDeterminant
open ParityMinorAssembly PoleQuotientTransversality

/-- The pure real-analytic content of the strict height separation. -/
theorem strict_height_separation_of_strip {x : ℝ} (h0 : 0 < x) (h1 : x < 1)
    (hoff : x ≠ 1 / 2) : 0 < |x - 1 / 2| ∧ |x - 1 / 2| < 1 / 2 := by
  refine ⟨abs_pos.2 (sub_ne_zero.2 hoff), ?_⟩
  rw [abs_lt]
  constructor <;> linarith

/-- **Strict height separation for an actual off-line nontrivial zero.**  The
hypothesis `riemannZeta ρ = 0` records the provenance of `ρ` as an actual zeta
zero; the inequality itself is driven by the open-strip bounds together with
off-line-ness. -/
theorem offline_zero_strict_height_separation {ρ : ℂ} (_hz : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hoff : ρ.re ≠ 1 / 2) :
    0 < |ρ.re - 1 / 2| ∧ |ρ.re - 1 / 2| < 1 / 2 :=
  strict_height_separation_of_strip h0 h1 hoff

variable {L Cφ c d m : ℝ} {φ : ℝ → ℝ}

/-- **Capstone.**  For an actual off-line nontrivial zero `ρ` of `riemannZeta`
and any admissible taper, at all sufficiently small observation radii the four
symmetric samples see the two zero-side directions (at height
`a = |Re ρ - 1/2|`) and the two pole directions (at height `p = 1/2`) as
linearly independent: the zero-side signal survives the two-dimensional pole
nuisance quotient. -/
theorem offline_zero_parity_transversality {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hoff : ρ.re ≠ 1 / 2)
    (hφmeas : Measurable φ) (hφ0 : ∀ u ∈ Ioc (0 : ℝ) L, 0 ≤ φ u)
    (hφb : ∀ u ∈ Ioc (0 : ℝ) L, |φ u| ≤ Cφ)
    (hL : 0 < L) (hc : 0 < c) (hcd : c < d) (hdL : d ≤ L) (hm : 0 < m)
    (hplateau : ∀ u ∈ Ioo c d, m ≤ φ u) :
    ∃ r₀ > 0, ∀ r, 0 < r → r < r₀ → ∀ s t s' t' : ℝ,
      s * evenResponse L φ |ρ.re - 1 / 2| r + t * oddResponse L φ |ρ.re - 1 / 2| r
          + (s' * evenResponse L φ (1 / 2) r + t' * oddResponse L φ (1 / 2) r) = 0 →
      s * evenResponse L φ |ρ.re - 1 / 2| r - t * oddResponse L φ |ρ.re - 1 / 2| r
          + (s' * evenResponse L φ (1 / 2) r - t' * oddResponse L φ (1 / 2) r) = 0 →
      s * evenResponse L φ |ρ.re - 1 / 2| (2 * r)
          + t * oddResponse L φ |ρ.re - 1 / 2| (2 * r)
          + (s' * evenResponse L φ (1 / 2) (2 * r)
            + t' * oddResponse L φ (1 / 2) (2 * r)) = 0 →
      s * evenResponse L φ |ρ.re - 1 / 2| (2 * r)
          - t * oddResponse L φ |ρ.re - 1 / 2| (2 * r)
          + (s' * evenResponse L φ (1 / 2) (2 * r)
            - t' * oddResponse L φ (1 / 2) (2 * r)) = 0 →
      s = 0 ∧ t = 0 ∧ s' = 0 ∧ t' = 0 := by
  obtain ⟨hapos, halt⟩ := offline_zero_strict_height_separation hz h0 h1 hoff
  exact pole_quotient_transversality hφmeas hφ0 hφb hL hapos halt hc hcd hdL hm hplateau

end ActualZetaHeightSeparation
end RiemannAnalytic
