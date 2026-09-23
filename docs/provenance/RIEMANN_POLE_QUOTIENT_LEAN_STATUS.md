# `Riemann_Pole_Quotient_Reduction_2026.pdf` — Lean status map

This note records exactly which parts of the manuscript
`Riemann_Pole_Quotient_Reduction_2026.pdf` are now carried by checked Lean 4
proof terms in this repository, and which parts remain hypotheses.

**No unconditional proof of the Riemann hypothesis is claimed or obtained.**
The remaining analytic content of the manuscript (Hypothesis 10.1) appears in
Lean only as an explicit *hypothesis* of the reduction theorems. It is never
introduced as an axiom, a postulate or a `sorry`.

## New modules

| Module | Manuscript item |
| --- | --- |
| `Lean/Integration/RiemannSmoothNormalizedWindow.lean` | §3, Lemma 3.1 |
| `Lean/Integration/RiemannAdaptiveCutoffCrossingCompatibility.lean` | §5, Lemma 5.1 and Remark 5.2 |
| `Lean/Integration/RiemannPoleQuotientTerminal.lean` | §4 (1)–(3), §6 Prop. 6.3, §8 Thm 8.1 |
| `Lean/Integration/RiemannPoleQuotientAdaptiveSelection.lean` | §7, the composition of Lemma 5.1 with Thm 8.1 |
| `Lean/Integration/RiemannPoleQuotientReduction.lean` | §2, §9 Thm 9.1, §10 |
| `Lean/Integration/AxiomAuditPoleQuotient.lean` | axiom audit of the lane |

All six are imported by the `Integration` root aggregate and build under the
project's pinned toolchain (Lean 4.28.0 / Mathlib `v4.28.0`). Every declaration
of the lane reports only `{propext, Classical.choice, Quot.sound}`.

## What is proved

Namespace `Integration.RiemannPoleQuotient`.

### Lemma 3.1 — the smooth normalized logarithmic window

`BumpProfile` packages the manuscript's fixed profile `ψ`: `C²`, nonnegative,
supported in `[-1,1]`, positive at the origin. `stdBumpProfile` exhibits one,
built from Mathlib's `ContDiffBump`, so the theory is not vacuous. For
`0 < e < c`,

```
rawWindow ψ c e u = ψ ((u - c)/e) + ψ ((-u - c)/e)
windowMass ψ c e  = ∫ rawWindow ψ c e
window ψ c e      = (windowMass ψ c e)⁻¹ • rawWindow ψ c e
```

Proved: `windowMass_pos`, `window_even`, `window_nonneg`, `window_contDiff`
(`ContDiff ℝ 2`), `window_hasCompactSupport`, `window_integral_eq_one`,
`window_support` (support inside `c - e ≤ |u| ≤ c + e`), `window_pos_at_centre`,
`window_integrable`, and the bundled `smooth_normalized_window`. The
short-window regime of §3 is `window_support_lt_log_two`.

### Lemma 5.1 — adaptive cutoff compatibility

`adaptive_cutoff_compatible`: for `L > 0`, `ε > 0` and `F : ℕ → ℝ` with
`F J → 0`, there is `J ≥ 1` with `π/2 < J·L` and `F J < ε`. The filter form of
Remark 5.2 is `adaptive_cutoff_eventually`, assembled from
`eventually_quarter_period_crossing` and `eventually_far_tail_small`.

### §4, §6, §8 — the terminal algebra

`PoleQuotientResponse` is a record of the five scalars
`Ccluster, Doff, DΓ, Dnear, Bfar`, with the three manuscript predicates
`Balance` (1), `NearFarSplit` (2), `StrictHigh` (3).

* `terminal_contradiction` — Theorem 8.1: (1), (2), (3) are jointly
  contradictory.
* `strictHigh_of_certificate` — Proposition 6.3: near representation
  `Dnear = Snear` plus a certificate `Snear ≤ U` plus
  `U + Bfar + DΓ < Ccluster` gives (3); `terminal_contradiction_of_certificate`
  runs it to the contradiction.
* `balance_and_split_consistent` — a sharpness check: (1) and (2) alone are
  satisfiable with (3) false, so Theorem 8.1 is not vacuous and the strict
  inequality carries the whole analytic payment.

### §7 — adaptive selection

`exists_cutoff_strictHigh`: if the far majorant of a cutoff-indexed family of
responses tends to `0` and the near core plus Gamma term sit below the cluster
response by a *fixed* margin `δ > 0`, then some cutoff both crosses the
quarter-period threshold and satisfies (3). `no_response_family_with_margin`
runs that into Theorem 8.1.

### §2 and §9 — the low/high compilation, on Mathlib's actual zeta function

These theorems are about `riemannZeta` as defined in Mathlib, not about an
abstract carrier.

* `zeta_eq_zero_iff_completed` — on `Re s > 0`, zeros of `ζ` are zeros of the
  completed `Λ` (via `Gammaℝ ≠ 0`).
* `zeta_zero_one_sub` — functional-equation symmetry of the zero set inside the
  open critical strip, from `completedRiemannZeta_one_sub`.
* `re_lt_one_of_zeta_eq_zero` and `re_pos_of_zeta_eq_zero` — every zero of `ζ`
  other than the trivial zeros `-2(n+1)` lies in the open strip `0 < Re s < 1`.
  The second uses the functional equation `ζ(1-w) = 2(2π)^{-w} Γ(w) cos(πw/2) ζ(w)`,
  non-vanishing of `Γ` and of `ζ` on `Re w ≥ 1`, the zero set of `cos`, and
  `ζ(0) = -1/2`. This discharges item (iv) of Theorem 9.1 (the critical
  predicate is literally `Re ρ = 1/2`) and the strip reduction of item (ii).
* `riemannHypothesis_of_low_and_high` — **Theorem 9.1**:
  `LowRegionVerified → HighOrdinateContradiction → RiemannHypothesis`, where
  `RiemannHypothesis` is Mathlib's own statement.
* `riemannHypothesis_of_low_and_poleQuotient` — the same with the high side
  supplied in pole–quotient form via `PoleQuotientRealization` and Theorem 8.1.

## Exact remaining obligations

The following are Lean *hypotheses*, corresponding one-to-one with the
manuscript's own open items. None is proved here.

| Lean predicate | Manuscript item | Nature |
| --- | --- | --- |
| `LowRegionVerified` | §2, Prop. 2.2 | published Platt–Trudgian verified computation, not formalized |
| `HighOrdinateContradiction` | §8/§10, Hypothesis 10.1 | the main analytic wall |
| `PoleQuotientRealization` | §4/§10 | attach explicit-formula response data satisfying (1), (2), (3) at every high off-line zero |
| margin hypothesis `hnear` of `exists_cutoff_strictHigh` | §7 | uniform finite-near-core margin |
| `hrep : R.near = Snear` of `strictHigh_of_certificate` | §6, Hypothesis 6.1 | the near representation theorem |
| `hcert : Snear ≤ U` | §6, Hypothesis 6.2 | optional finite certificate producer |

In particular the manuscript's `rhDerived = false` frontier is preserved: the
Lean development contains a complete, checked *reduction*, and no proof of the
high-ordinate inequality.

## Relation to the existing corpus

The pre-existing Lean analytic lane (`Integration.RiemannStrip`,
`Integration.RiemannXiSymmetry`, `Integration.RiemannSubstrate`,
`Integration.RiemannReflection`, `Integration.RiemannDomain`) works with the
reflection geometry `s ↦ 1 - s`, `s ↦ conj s` on `ℂ` and with abstract
zero-predicate records; it makes no statement about `riemannZeta`. The modules
added here are the first in this repository to state and prove theorems about
Mathlib's `riemannZeta` itself, and they reuse the same critical-line predicate
`Re s = 1/2` that `Integration.RiemannStrip.critReflect_fixed_iff` characterises
as the fixed locus of the composed involution.
