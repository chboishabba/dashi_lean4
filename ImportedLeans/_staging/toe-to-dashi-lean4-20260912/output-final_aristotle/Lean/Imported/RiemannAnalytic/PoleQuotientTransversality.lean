/-
# Pole-quotient transversality from the two parity minors

This closes the last structural link of the parity-minor ledger at the level of
the symmetric four-sample observation.

Setting.  Observations are taken at the four symmetric radii

  `r, -r, 2r, -2r`.

For a real-even taper the height-`y` response splits into an even (cosine) part
and an odd (sine) part,

  `A_y(r) = ∫₀ᴸ φ(u) cosh (y u) cos (r u) du`   (even in `r`),
  `B_y(r) = ∫₀ᴸ φ(u) sinh (y u) sin (r u) du`   (odd in `r`),

so that the response at radius `-r` is `A_y(r) - B_y(r)`
(`evenResponse_neg`, `oddResponse_neg`).  A conjugate pair of heights therefore
contributes the *two* real directions `A_y` and `B_y`, which is exactly the
"conjugate pair, not a one-dimensional complex span" correction: the pole height
`p` supplies **two** nuisance directions, not one.

Result.  `pole_quotient_transversality` shows that at all sufficiently small
radii the four directions

  zero-even, zero-odd, pole-even, pole-odd

are linearly independent as functions on the four symmetric samples.  Hence the
two zero-side directions survive the quotient by the two-dimensional pole
nuisance space:

  `4 samples − 2 nuisance directions = 2 transverse dimensions`.

The proof uses **both** parity minors: the even samples isolate the even sector
and the odd samples the odd sector, and each sector needs its own nonvanishing
`2 × 2` minor.  One good channel is *not* enough, in accordance with the
recorded counterexample.

`zero_response_not_in_pole_span` is the direct corollary: the actual height-`a`
sampled response is not a linear combination of the two pole directions.

This is a discrimination/transversality statement about the sampling map.  It
does not assert a unique underlying "origin" for anything.

No `sorry`, no `axiom`, no numerical evidence.
-/

import Mathlib
import RiemannAnalytic.ParityMinorAssembly

open MeasureTheory Set

namespace RiemannAnalytic
namespace PoleQuotientTransversality

open StrictKernelMomentRatio OddTaylorDeterminant EvenTaylorDeterminant ParityMinorAssembly

/-! ## Parity of the two channels in the observation radius -/

/-- The even channel is even in the observation radius. -/
theorem evenResponse_neg (L : ℝ) (φ : ℝ → ℝ) (y r : ℝ) :
    evenResponse L φ y (-r) = evenResponse L φ y r := by
  simp only [evenResponse, neg_mul, Real.cos_neg]

/-- The odd channel is odd in the observation radius. -/
theorem oddResponse_neg (L : ℝ) (φ : ℝ → ℝ) (y r : ℝ) :
    oddResponse L φ y (-r) = -oddResponse L φ y r := by
  simp only [oddResponse, neg_mul, Real.sin_neg, mul_neg, integral_neg]

/-- The total height-`y` response at observation radius `r`. -/
noncomputable def fullResponse (L : ℝ) (φ : ℝ → ℝ) (y r : ℝ) : ℝ :=
  evenResponse L φ y r + oddResponse L φ y r

/-- At the reflected radius the two channels appear with opposite relative sign;
this is why a real-even taper turns one conjugate height pair into two
independent real directions. -/
theorem fullResponse_neg (L : ℝ) (φ : ℝ → ℝ) (y r : ℝ) :
    fullResponse L φ y (-r) = evenResponse L φ y r - oddResponse L φ y r := by
  rw [fullResponse, evenResponse_neg, oddResponse_neg]
  ring

/-! ## Transversality -/

variable {L Cφ a p c d m : ℝ} {φ : ℝ → ℝ}

/-- Abstract four-sample separation: symmetric sampling splits a combination into
its even and odd sectors, and each sector is then killed by its own nonvanishing
`2 × 2` minor. -/
theorem indep_of_both_minors {Aa1 Aa2 Ap1 Ap2 Ba1 Ba2 Bp1 Bp2 : ℝ}
    (hE : Aa1 * Ap2 - Aa2 * Ap1 ≠ 0) (hO : Ba1 * Bp2 - Ba2 * Bp1 ≠ 0)
    {s t s' t' : ℝ}
    (e1 : s * Aa1 + t * Ba1 + (s' * Ap1 + t' * Bp1) = 0)
    (e2 : s * Aa1 - t * Ba1 + (s' * Ap1 - t' * Bp1) = 0)
    (e3 : s * Aa2 + t * Ba2 + (s' * Ap2 + t' * Bp2) = 0)
    (e4 : s * Aa2 - t * Ba2 + (s' * Ap2 - t' * Bp2) = 0) :
    s = 0 ∧ t = 0 ∧ s' = 0 ∧ t' = 0 := by
  have hev1 : s * Aa1 + s' * Ap1 = 0 := by linarith
  have hev2 : s * Aa2 + s' * Ap2 = 0 := by linarith
  have hod1 : t * Ba1 + t' * Bp1 = 0 := by linarith
  have hod2 : t * Ba2 + t' * Bp2 = 0 := by linarith
  obtain ⟨hs, hs'⟩ := indep_of_det_ne_zero hE hev1 hev2
  obtain ⟨ht, ht'⟩ := indep_of_det_ne_zero hO hod1 hod2
  exact ⟨hs, ht, hs', ht'⟩

/-- **Pole-quotient transversality.**  For an admissible taper, a zero height
`0 < a` and the pole height `p > a`, at all sufficiently small radii the four
symmetric samples `r, -r, 2r, -2r` see the zero-even, zero-odd, pole-even and
pole-odd directions as linearly independent.  Consequently the two zero-side
directions are transverse to the two-dimensional pole nuisance space. -/
theorem pole_quotient_transversality
    (hφmeas : Measurable φ) (hφ0 : ∀ u ∈ Ioc (0 : ℝ) L, 0 ≤ φ u)
    (hφb : ∀ u ∈ Ioc (0 : ℝ) L, |φ u| ≤ Cφ)
    (hL : 0 < L) (ha : 0 < a) (hap : a < p)
    (hc : 0 < c) (hcd : c < d) (hdL : d ≤ L) (hm : 0 < m)
    (hplateau : ∀ u ∈ Ioo c d, m ≤ φ u) :
    ∃ r₀ > 0, ∀ r, 0 < r → r < r₀ → ∀ s t s' t' : ℝ,
      s * evenResponse L φ a r + t * oddResponse L φ a r
          + (s' * evenResponse L φ p r + t' * oddResponse L φ p r) = 0 →
      s * evenResponse L φ a r - t * oddResponse L φ a r
          + (s' * evenResponse L φ p r - t' * oddResponse L φ p r) = 0 →
      s * evenResponse L φ a (2 * r) + t * oddResponse L φ a (2 * r)
          + (s' * evenResponse L φ p (2 * r) + t' * oddResponse L φ p (2 * r)) = 0 →
      s * evenResponse L φ a (2 * r) - t * oddResponse L φ a (2 * r)
          + (s' * evenResponse L φ p (2 * r) - t' * oddResponse L φ p (2 * r)) = 0 →
      s = 0 ∧ t = 0 ∧ s' = 0 ∧ t' = 0 := by
  obtain ⟨r₀, hr₀, hboth⟩ := exists_radius_both_parity_minors_neg
    hφmeas hφ0 hφb hL ha hap hc hcd hdL hm hplateau
  refine ⟨r₀, hr₀, fun r hr hlt s t s' t' e1 e2 e3 e4 => ?_⟩
  obtain ⟨hE, hO⟩ := hboth r hr hlt
  exact indep_of_both_minors (ne_of_lt hE) (ne_of_lt hO) e1 e2 e3 e4

/-- **The zero-side response survives the pole quotient.**  At small radii the
actual sampled height-`a` response is not any linear combination of the two pole
directions, on the symmetric sample set. -/
theorem zero_response_not_in_pole_span
    (hφmeas : Measurable φ) (hφ0 : ∀ u ∈ Ioc (0 : ℝ) L, 0 ≤ φ u)
    (hφb : ∀ u ∈ Ioc (0 : ℝ) L, |φ u| ≤ Cφ)
    (hL : 0 < L) (ha : 0 < a) (hap : a < p)
    (hc : 0 < c) (hcd : c < d) (hdL : d ≤ L) (hm : 0 < m)
    (hplateau : ∀ u ∈ Ioo c d, m ≤ φ u) :
    ∃ r₀ > 0, ∀ r, 0 < r → r < r₀ → ∀ s' t' : ℝ,
      ¬ (fullResponse L φ a r
            = s' * evenResponse L φ p r + t' * oddResponse L φ p r
        ∧ fullResponse L φ a (-r)
            = s' * evenResponse L φ p r - t' * oddResponse L φ p r
        ∧ fullResponse L φ a (2 * r)
            = s' * evenResponse L φ p (2 * r) + t' * oddResponse L φ p (2 * r)
        ∧ fullResponse L φ a (-(2 * r))
            = s' * evenResponse L φ p (2 * r) - t' * oddResponse L φ p (2 * r)) := by
  obtain ⟨r₀, hr₀, hind⟩ := pole_quotient_transversality
    hφmeas hφ0 hφb hL ha hap hc hcd hdL hm hplateau
  refine ⟨r₀, hr₀, fun r hr hlt s' t' ⟨q1, q2, q3, q4⟩ => ?_⟩
  rw [fullResponse] at q1 q3
  rw [fullResponse_neg] at q2 q4
  have := hind r hr hlt 1 1 (-s') (-t') (by linarith) (by linarith) (by linarith) (by linarith)
  exact one_ne_zero this.1

end PoleQuotientTransversality
end RiemannAnalytic
