/-
# Four-sample transversality in the literal test-function language

`PoleQuotientTransversality.lean` proves that the four symmetric samples
`r, −r, 2r, −2r` see the two zero-side parity directions and the two pole
directions as linearly independent.  That theorem is phrased in terms of the
parity responses `evenResponse`, `oddResponse`.

`WeilParityResponseBridge.lean` identifies those responses, with explicit
constants, with paired evaluations of the *literal* compactly supported test
function `h(z) = ∫₋ᴸᴸ g(u) e^{izu} du`:

  `zeroEvenSample = h_even(iα) + h_even(−iα) = 4 · evenResponse L φ α r`,
  `zeroOddSample  = h_odd(−iα) − h_odd(iα)  = 4 · oddResponse  L φ α r`.

This module transports the transversality statement into that language:
`literalWeilFourSampleTransversality` says that for an actual off-line
nontrivial zero `ρ` of `riemannZeta`, at all sufficiently small radii the four
literal paired evaluations — two at the zero height `|Re ρ − 1/2|` and two at
the pole height `1/2` — are linearly independent over `ℝ`.  Equivalently
(`literalWeilZeroNotInPoleSpan`) the literal zero-side pair is not in the span
of the literal pole pair.

The evaluations are those of the literal test family; the Weil explicit formula
itself is not used and not asserted here.

No `sorry`, no `axiom`, no numerical evidence.
-/

import Mathlib
import RiemannAnalytic.WeilParityResponseBridge
import RiemannAnalytic.ActualZetaHeightSeparation

open MeasureTheory Set

namespace RiemannAnalytic
namespace LiteralWeilFourSampleTransversality

open EvenTaylorDeterminant OddTaylorDeterminant PoleQuotientTransversality
open WeilParityResponseBridge ActualZetaHeightSeparation

/-- The literal *even* paired evaluation at height `α`: `h(iα) + h(−iα)` for the
even-channel test function. -/
noncomputable def evenSample (L : ℝ) (φ : ℝ → ℝ) (α r : ℝ) : ℂ :=
  weilTransform L (symEvenTaper φ r) (Complex.I * α)
    + weilTransform L (symEvenTaper φ r) (-(Complex.I * α))

/-- The literal *odd* paired evaluation at height `α`: `h(−iα) − h(iα)` for the
odd-channel test function. -/
noncomputable def oddSample (L : ℝ) (φ : ℝ → ℝ) (α r : ℝ) : ℂ :=
  weilTransform L (symOddTaper φ r) (-(Complex.I * α))
    - weilTransform L (symOddTaper φ r) (Complex.I * α)

variable {L Cφ : ℝ} {φ : ℝ → ℝ}

theorem evenSample_eq (hφmeas : Measurable φ) (hφb : ∀ u ∈ Icc (0 : ℝ) L, |φ u| ≤ Cφ)
    (hL : 0 < L) (α r : ℝ) :
    evenSample L φ α r = 4 * (evenResponse L φ α r : ℂ) :=
  weilZeroEven_eq hφmeas hφb hL r α

theorem oddSample_eq (hφmeas : Measurable φ) (hφb : ∀ u ∈ Icc (0 : ℝ) L, |φ u| ≤ Cφ)
    (hL : 0 < L) (α r : ℝ) :
    oddSample L φ α r = 4 * (oddResponse L φ α r : ℂ) :=
  weilZeroOdd_eq hφmeas hφb hL r α

/-- A linear relation among the literal samples is a linear relation among the
parity responses. -/
theorem real_relation_of_sample_relation
    (hφmeas : Measurable φ) (hφb : ∀ u ∈ Icc (0 : ℝ) L, |φ u| ≤ Cφ) (hL : 0 < L)
    {a p r : ℝ} {s t s' t' : ℝ} (ε ε' : ℝ)
    (h : (s : ℂ) * evenSample L φ a r + (ε : ℂ) * (t : ℂ) * oddSample L φ a r
        + ((s' : ℂ) * evenSample L φ p r + (ε' : ℂ) * (t' : ℂ) * oddSample L φ p r) = 0) :
    s * evenResponse L φ a r + ε * t * oddResponse L φ a r
      + (s' * evenResponse L φ p r + ε' * t' * oddResponse L φ p r) = 0 := by
  rw [evenSample_eq hφmeas hφb hL, oddSample_eq hφmeas hφb hL,
    evenSample_eq hφmeas hφb hL, oddSample_eq hφmeas hφb hL] at h
  have h4 : ((4 : ℂ) * ((s * evenResponse L φ a r + ε * t * oddResponse L φ a r
      + (s' * evenResponse L φ p r + ε' * t' * oddResponse L φ p r) : ℝ) : ℂ)) = 0 := by
    push_cast
    linear_combination h
  have hne : (4 : ℂ) ≠ 0 := by norm_num
  have := (mul_eq_zero.1 h4).resolve_left hne
  exact_mod_cast this

/-- **Literal four-sample transversality.**  For an actual off-line nontrivial
zero `ρ` of `riemannZeta` and an admissible taper, at all sufficiently small
radii the four literal paired test-function evaluations — the even and odd
samples at the zero height `|Re ρ − 1/2|` and at the pole height `1/2`, taken at
the symmetric radii `r, −r, 2r, −2r` — admit no nontrivial real linear
relation. -/
theorem literalWeilFourSampleTransversality {ρ : ℂ} {c d m : ℝ} (hz : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hoff : ρ.re ≠ 1 / 2)
    (hφmeas : Measurable φ) (hφ0 : ∀ u ∈ Ioc (0 : ℝ) L, 0 ≤ φ u)
    (hφb : ∀ u ∈ Icc (0 : ℝ) L, |φ u| ≤ Cφ)
    (hL : 0 < L) (hc : 0 < c) (hcd : c < d) (hdL : d ≤ L) (hm : 0 < m)
    (hplateau : ∀ u ∈ Ioo c d, m ≤ φ u) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ s t s' t' : ℝ,
      (s : ℂ) * evenSample L φ |ρ.re - 1 / 2| r + (t : ℂ) * oddSample L φ |ρ.re - 1 / 2| r
          + ((s' : ℂ) * evenSample L φ (1 / 2) r
            + (t' : ℂ) * oddSample L φ (1 / 2) r) = 0 →
      (s : ℂ) * evenSample L φ |ρ.re - 1 / 2| r - (t : ℂ) * oddSample L φ |ρ.re - 1 / 2| r
          + ((s' : ℂ) * evenSample L φ (1 / 2) r
            - (t' : ℂ) * oddSample L φ (1 / 2) r) = 0 →
      (s : ℂ) * evenSample L φ |ρ.re - 1 / 2| (2 * r)
          + (t : ℂ) * oddSample L φ |ρ.re - 1 / 2| (2 * r)
          + ((s' : ℂ) * evenSample L φ (1 / 2) (2 * r)
            + (t' : ℂ) * oddSample L φ (1 / 2) (2 * r)) = 0 →
      (s : ℂ) * evenSample L φ |ρ.re - 1 / 2| (2 * r)
          - (t : ℂ) * oddSample L φ |ρ.re - 1 / 2| (2 * r)
          + ((s' : ℂ) * evenSample L φ (1 / 2) (2 * r)
            - (t' : ℂ) * oddSample L φ (1 / 2) (2 * r)) = 0 →
      s = 0 ∧ t = 0 ∧ s' = 0 ∧ t' = 0 := by
  have hφbIoc : ∀ u ∈ Ioc (0 : ℝ) L, |φ u| ≤ Cφ := fun u hu => hφb u ⟨hu.1.le, hu.2⟩
  obtain ⟨r₀, hr₀, hind⟩ := offline_zero_parity_transversality hz h0 h1 hoff
    hφmeas hφ0 hφbIoc hL hc hcd hdL hm hplateau
  refine ⟨r₀, hr₀, fun r hr hlt s t s' t' e1 e2 e3 e4 => ?_⟩
  refine hind r hr hlt s t s' t' ?_ ?_ ?_ ?_
  · have := real_relation_of_sample_relation hφmeas hφb hL (a := |ρ.re - 1 / 2|)
      (p := 1 / 2) (r := r) (s := s) (t := t) (s' := s') (t' := t') 1 1 (by push_cast; linear_combination e1)
    linarith [this]
  · have := real_relation_of_sample_relation hφmeas hφb hL (a := |ρ.re - 1 / 2|)
      (p := 1 / 2) (r := r) (s := s) (t := t) (s' := s') (t' := t') (-1) (-1)
      (by push_cast; linear_combination e2)
    linarith [this]
  · have := real_relation_of_sample_relation hφmeas hφb hL (a := |ρ.re - 1 / 2|)
      (p := 1 / 2) (r := 2 * r) (s := s) (t := t) (s' := s') (t' := t') 1 1
      (by push_cast; linear_combination e3)
    linarith [this]
  · have := real_relation_of_sample_relation hφmeas hφb hL (a := |ρ.re - 1 / 2|)
      (p := 1 / 2) (r := 2 * r) (s := s) (t := t) (s' := s') (t' := t') (-1) (-1)
      (by push_cast; linear_combination e4)
    linarith [this]

/-- **The literal zero-side pair survives the pole quotient.**  At small radii
the literal even/odd paired evaluations at the zero height are not a linear
combination of the two literal pole-height evaluations, on the symmetric sample
set. -/
theorem literalWeilZeroNotInPoleSpan {ρ : ℂ} {c d m : ℝ} (hz : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hoff : ρ.re ≠ 1 / 2)
    (hφmeas : Measurable φ) (hφ0 : ∀ u ∈ Ioc (0 : ℝ) L, 0 ≤ φ u)
    (hφb : ∀ u ∈ Icc (0 : ℝ) L, |φ u| ≤ Cφ)
    (hL : 0 < L) (hc : 0 < c) (hcd : c < d) (hdL : d ≤ L) (hm : 0 < m)
    (hplateau : ∀ u ∈ Ioo c d, m ≤ φ u) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ s' t' : ℝ,
      ¬ (evenSample L φ |ρ.re - 1 / 2| r + oddSample L φ |ρ.re - 1 / 2| r
            = (s' : ℂ) * evenSample L φ (1 / 2) r + (t' : ℂ) * oddSample L φ (1 / 2) r
        ∧ evenSample L φ |ρ.re - 1 / 2| r - oddSample L φ |ρ.re - 1 / 2| r
            = (s' : ℂ) * evenSample L φ (1 / 2) r - (t' : ℂ) * oddSample L φ (1 / 2) r
        ∧ evenSample L φ |ρ.re - 1 / 2| (2 * r) + oddSample L φ |ρ.re - 1 / 2| (2 * r)
            = (s' : ℂ) * evenSample L φ (1 / 2) (2 * r)
              + (t' : ℂ) * oddSample L φ (1 / 2) (2 * r)
        ∧ evenSample L φ |ρ.re - 1 / 2| (2 * r) - oddSample L φ |ρ.re - 1 / 2| (2 * r)
            = (s' : ℂ) * evenSample L φ (1 / 2) (2 * r)
              - (t' : ℂ) * oddSample L φ (1 / 2) (2 * r)) := by
  obtain ⟨r₀, hr₀, hind⟩ := literalWeilFourSampleTransversality hz h0 h1 hoff hφmeas hφ0 hφb
    hL hc hcd hdL hm hplateau
  refine ⟨r₀, hr₀, fun r hr hlt s' t' ⟨q1, q2, q3, q4⟩ => ?_⟩
  have := hind r hr hlt 1 1 (-s') (-t')
    (by push_cast; linear_combination q1)
    (by push_cast; linear_combination q2)
    (by push_cast; linear_combination q3)
    (by push_cast; linear_combination q4)
  exact one_ne_zero this.1

end LiteralWeilFourSampleTransversality
end RiemannAnalytic
