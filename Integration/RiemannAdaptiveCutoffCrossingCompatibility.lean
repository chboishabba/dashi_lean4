import Mathlib

/-!
# Adaptive cutoff: crossing and tail accuracy are compatible (Lemma 5.1)

`Riemann_Pole_Quotient_Reduction_2026.pdf` §5 records the following elementary
but structurally important fact.  If `Λ > 0` is the phase scale attached to a
hypothetical off-line zero and a taper, and `F : ℕ → ℝ` is the far-tail
majorant, which tends to `0`, then the quarter-period crossing requirement
`π/2 < J Λ` and the far-tail accuracy requirement `F J < ε` can be met by one
and the same cutoff `J`.

Two forms are proved:

* `adaptive_cutoff_compatible` — the concrete statement of Lemma 5.1;
* `adaptive_cutoff_eventually` — the filter form referred to in Remark 5.2:
  crossing holds eventually, small far error holds eventually, and the
  intersection of two eventual sets is eventual.

Nothing here is specific to the zeta function; `Λ`, `F` and `ε` are arbitrary.
-/

namespace Integration.RiemannPoleQuotient

open Filter Topology

/-- Quarter-period crossing holds for all large cutoffs. -/
theorem eventually_quarter_period_crossing {L : ℝ} (hL : 0 < L) :
    ∀ᶠ J : ℕ in atTop, Real.pi / 2 < J * L := by
  have h : Tendsto (fun J : ℕ => (J : ℝ) * L) atTop atTop :=
    Filter.Tendsto.atTop_mul_const hL tendsto_natCast_atTop_atTop
  exact h.eventually_gt_atTop _

/-- An arbitrarily small far tail holds for all large cutoffs. -/
theorem eventually_far_tail_small {F : ℕ → ℝ} (hF : Tendsto F atTop (𝓝 0)) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ J : ℕ in atTop, F J < ε :=
  hF.eventually (eventually_lt_nhds hε)

/-- **Remark 5.2 (filter form).**  For all sufficiently large cutoffs, the
quarter-period crossing condition and the far-tail accuracy condition hold
simultaneously. -/
theorem adaptive_cutoff_eventually {L : ℝ} (hL : 0 < L) {F : ℕ → ℝ}
    (hF : Tendsto F atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ J : ℕ in atTop, 1 ≤ J ∧ Real.pi / 2 < J * L ∧ F J < ε :=
  (eventually_ge_atTop 1).and
    ((eventually_quarter_period_crossing hL).and (eventually_far_tail_small hF hε))

/-- **Lemma 5.1 (adaptive cutoff compatibility).**  Let `L > 0`, `ε > 0`, and
let `F : ℕ → ℝ` tend to `0`.  Then there is a cutoff `J ≥ 1` which crosses the
quarter-period threshold and makes the far tail smaller than `ε`. -/
theorem adaptive_cutoff_compatible {L : ℝ} (hL : 0 < L) {F : ℕ → ℝ}
    (hF : Tendsto F atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, 1 ≤ J ∧ Real.pi / 2 < J * L ∧ F J < ε :=
  (adaptive_cutoff_eventually hL hF hε).exists

end Integration.RiemannPoleQuotient
