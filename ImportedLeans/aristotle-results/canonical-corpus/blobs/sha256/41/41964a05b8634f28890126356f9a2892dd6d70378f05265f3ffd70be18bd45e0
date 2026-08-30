/-
# The exact scope of the support-radius-free rigidity class

`GaussianMomentRigidity.lean` proves that a compactly supported, divergence-free
`C²` stationary Gaussian similarity profile with Bernoulli head dominated by
`K|V|` is trivial as soon as `4K² < ν`, and `FiniteExpenditureMomentRigidity.lean`
feeds that into the C lane through the membership predicate
`ClayNS.HeadBoundedStationary`.

This file records, with proof, what that membership actually demands, so that
the C lane cannot silently treat it as a soft or automatically inherited
property.

* `ClayNS.head_pressure_eq_zero_of_velocity_eq_zero` — the head domination
  `|‖V‖² + 2p| ≤ K‖V‖` forces the pressure to **vanish pointwise on the zero set
  of the velocity**.  It is therefore a gauge-coupled pointwise condition, not a
  norm bound: a limit of blow-up rescalings inherits it only if the pressure
  normalization is pinned on the zero set of the limit profile as well.
* `ClayNS.headBoundedStationary_pressure_eq_zero_outside` — in particular, for a
  member of the rigidity class the pressure vanishes identically outside the
  support of the velocity.
* `ClayNS.head_nonneg_of_nonzero` — the head constant is necessarily
  nonnegative once the profile is not identically zero, so the threshold
  `4K² < ν` is a genuine smallness (`K < √ν/2`) restriction and not an empty
  side condition.

These are the precise obligations Worker C's compactness/inheritance package
must discharge if the C lane is to consume the support-radius-free rigidity
theorem for the *actual* blow-up cluster point.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.FiniteExpenditureMomentRigidity

open RealInnerProductSpace

noncomputable section

namespace ClayNS

/-- **The head domination pins the pressure on the zero set of the velocity.**
If `|‖V y‖² + 2p y| ≤ K‖V y‖` and `V y = 0`, then `p y = 0`. -/
theorem head_pressure_eq_zero_of_velocity_eq_zero {K : ℝ} {V : E3 → E3} {p : E3 → ℝ}
    (hhead : ∀ y : E3, |‖V y‖ ^ 2 + 2 * p y| ≤ K * ‖V y‖) {y : E3} (hy : V y = 0) :
    p y = 0 := by
  have h := hhead y
  rw [hy] at h
  simp only [norm_zero, mul_zero] at h
  have h2 : |2 * p y| ≤ 0 := by simpa using h
  have : 2 * p y = 0 := abs_nonpos_iff.mp h2
  linarith

/-- For a member of the rigidity class the pressure vanishes identically off the
support of the velocity: the class carries its own pressure gauge. -/
theorem headBoundedStationary_pressure_eq_zero_outside {nu K : ℝ} {V : E3 → E3}
    (hV : HeadBoundedStationary nu K V) :
    ∃ (L : ℝ) (p : E3 → ℝ), 0 < L ∧ IsStationarySimilarity nu V p ∧
      ∀ y : E3, L ≤ ‖y‖ → p y = 0 := by
  obtain ⟨L, p, hL, _, _, _, hsupp, hhead, heq⟩ := hV
  refine ⟨L, p, hL, heq, fun y hy => ?_⟩
  exact head_pressure_eq_zero_of_velocity_eq_zero hhead (hsupp y hy)

/-- The head constant of a nontrivial profile is nonnegative, so `4K² < ν` is a
genuine smallness restriction. -/
theorem head_nonneg_of_nonzero {K : ℝ} {V : E3 → E3} {p : E3 → ℝ}
    (hhead : ∀ y : E3, |‖V y‖ ^ 2 + 2 * p y| ≤ K * ‖V y‖) {y : E3} (hy : V y ≠ 0) :
    0 ≤ K := by
  have h := hhead y
  have hpos : 0 < ‖V y‖ := norm_pos_iff.mpr hy
  nlinarith [abs_nonneg (‖V y‖ ^ 2 + 2 * p y)]

end ClayNS
