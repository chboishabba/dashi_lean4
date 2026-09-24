/-
The literal terminal surface of the Hermitian route.

The point of this file is to make completely explicit *what remains* to be
proved.  The final statement of the route is Mathlib's literal
`RiemannHypothesis`, and the only input is the single analytic obligation

  `OffLineDetectabilityContradiction`:
    a zero of the completed zeta function with `Re s > 1/2` is impossible.

That obligation is **not proved here** and is not assumed anywhere else in this
development: every theorem below takes it (or a quantitative refinement of it)
as an explicit hypothesis.  In particular nothing in this file, or in anything
it imports, proves the Riemann Hypothesis.

The quantitative refinement `riemannHypothesis_of_defect_exceeds_error` records
the exact shape the analytic argument has to take: a transverse defect obeying a
quadratic floor in the offset, an upper bound for that defect coming from the
accumulated error terms, and a comparison showing the floor beats the error for
every hypothetical off-line zero.
-/
import RiemannAnalytic.Detectability

namespace RiemannAnalytic

open Complex

/-- **The remaining analytic obligation of the Hermitian route**: no zero of the
completed zeta function lies strictly to the right of the critical line.  This
is a genuine (unproved) statement, equivalent to the Riemann Hypothesis by
`riemannHypothesis_iff_no_completed_zero_right`. -/
def OffLineDetectabilityContradiction : Prop :=
  ∀ s : ℂ, completedRiemannZeta s = 0 → 1 / 2 < s.re → False

/-- **The literal terminal step.**  The obligation above yields Mathlib's
literal `RiemannHypothesis`. -/
theorem hermitianRoute_riemannHypothesis (h : OffLineDetectabilityContradiction) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_no_completed_zero_right]
  intro s hs
  by_contra hcon
  exact h s hs (lt_of_not_ge hcon)

/-- **The quantitative shape of the remaining obligation.**

Suppose that to every zero `s` of the completed zeta function the route
attaches a transverse defect `D s` and an error budget `E s` at scale `L s`,
such that

* the defect obeys the quadratic floor `c (L s)⁴ α² ≤ D s` in the offset
  `α = Re s - 1/2` (this is the coercivity half of the route),
* the defect is bounded by the error budget, `D s ≤ E s` (this is the
  transport half: zero side into the prime side), and
* for a hypothetical off-line zero the floor strictly beats the budget.

Then the literal Riemann Hypothesis follows.  All three hypotheses are inputs;
none of them is proved here. -/
theorem riemannHypothesis_of_defect_exceeds_error {c : ℝ} (L D E : ℂ → ℝ)
    (hfloor : ∀ s : ℂ, completedRiemannZeta s = 0 →
      c * L s ^ 4 * zeroOffset s ^ 2 ≤ D s)
    (hbound : ∀ s : ℂ, completedRiemannZeta s = 0 → D s ≤ E s)
    (hstrict : ∀ s : ℂ, completedRiemannZeta s = 0 → 1 / 2 < s.re →
      E s < c * L s ^ 4 * zeroOffset s ^ 2) :
    RiemannHypothesis := by
  refine hermitianRoute_riemannHypothesis fun s hs hre => ?_
  have h1 := hfloor s hs
  have h2 := hbound s hs
  have h3 := hstrict s hs hre
  linarith

end RiemannAnalytic
