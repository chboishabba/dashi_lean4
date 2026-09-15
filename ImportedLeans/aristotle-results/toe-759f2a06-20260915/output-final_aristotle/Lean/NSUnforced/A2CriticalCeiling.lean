/-
# A2: the phase-sensitive critical-production ceiling, kept separate from A1

## The payment

The literal R406 critical half, in the shape frozen by
`NSTriadKNR353ToUniformSignedCriticalProductionRound372Exact` and consumed as
the *critical* field of the R414 dual consumer
(`NSTriadKNSignedCancellationDualConsumerRound414Exact`):

```agda
criticalSize : Nat → Time → ℚ
cutoffIndependentCriticalBound : Time → ℚ
criticalBound : (cutoff : Nat) (terminal : Time) →
  criticalSize cutoff terminal ≤ cutoffIndependentCriticalBound terminal
```

`UniformSignedCriticalCeiling` below is that record over `ℝ`.

## Deliberate independence from A1

This module imports **no** A1 module.  `NSUnforced.SignedFullSquare`,
`NSUnforced.CutoffUniformBudget` and `NSUnforced.A1Budget568` are not in its
import closure, so no A1 receipt can silently discharge A2, and conversely.
The only imports are Mathlib and the preserved donor Waleffe payment lane.

## What is proved

`a2_uniform_critical_ceiling` — the A2 reduction.  For a cutoff-indexed family
of adverse triad cells whose amplitudes solve the damped–forced scalar equation
`Ȧ = −γ A + F` and whose production obeys the *phase-sensitive* pointwise
comparison `ν P ≤ 2 γ A₊`, the time-integrated signed critical production is
bounded by

```
criticalSize N T ≤ (2 M₀ + 2 M₁ T) / ν
```

whenever the initial positive amplitudes and the positive network forcing are
controlled uniformly in the cutoff.  The two cell-level ingredients are the
preserved donor theorems `ClayNS.Waleffe.kato_integrated_payment` (Duhamel /
Kato positive-part balance) and `ClayNS.Waleffe.cell_integrated_production_payment`;
the summation step is `ClayNS.Waleffe.finite_production_payment`.

`critical_cell_pointwise_payment` records that the pointwise comparison is not
an assumption about the flow but a consequence of the triad geometry
(`ClayNS.Waleffe.phase_damping_payment`, via the reverse triangle inequality on
`k + p + q = 0`).

## What remains open

`M₁`, the cutoff-uniform positive network-forcing expenditure
(`ClayNS.Waleffe.PhysicalWeightedPositiveWaleffeNetworkForcingBudget`).  That is
the genuine A2 wall and it is *not* paid here.

## Status

A2 reduction.  Independent of A1 by construction.
-/
import Mathlib
import RequestProject.NavierStokes.WaleffeIntegratedPayment

open MeasureTheory

noncomputable section

namespace DASHI.NS.Unforced

/-- **A2, the R406/R372 critical payment.**  As in the Agda original the
ceiling is a function of the terminal time only. -/
structure UniformSignedCriticalCeiling (criticalSize : ℕ → ℝ → ℝ) where
  /-- `cutoffIndependentCriticalBound`. -/
  ceiling : ℝ → ℝ
  /-- `criticalBound`. -/
  bound : ∀ (N : ℕ) (T : ℝ), 0 ≤ T → criticalSize N T ≤ ceiling T

/-- **The pointwise phase-sensitive comparison is geometric.**  On an adverse
mixed-helicity cell of a triad `k + p + q = 0` with production
`P = 2 r_k (r_q − r_p) A`, the comparison `ν P ≤ 2 γ A₊`, `γ = ν(r_k²+r_p²+r_q²)`,
follows from the reverse triangle inequality alone.  No dynamical input. -/
theorem critical_cell_pointwise_payment {E : Type*} [SeminormedAddCommGroup E]
    {k p q : E} (h : k + p + q = 0) {nu amp : ℝ} (hnu : 0 ≤ nu) (hamp : 0 ≤ amp) :
    nu * (2 * ‖k‖ * (‖q‖ - ‖p‖) * amp)
      ≤ 2 * (nu * (‖k‖ ^ 2 + ‖p‖ ^ 2 + ‖q‖ ^ 2)) * amp :=
  ClayNS.Waleffe.phase_damping_payment hnu hamp (norm_nonneg k)
    (ClayNS.Waleffe.triad_reverse_triangle h)

/-- **The A2 reduction.**  Cell-level Kato/Duhamel payment, summed over a finite
adverse family, with cutoff-uniform control of the initial positive amplitudes
and of the positive network forcing, produces the cutoff-independent critical
ceiling. -/
def a2_uniform_critical_ceiling
    {ι : Type*} (S : ℕ → Finset ι)
    (amp forc prod : ℕ → ι → ℝ → ℝ) (gam : ℕ → ι → ℝ)
    (criticalSize : ℕ → ℝ → ℝ)
    {nu M0 : ℝ} (M1 : ℝ → ℝ) (hnu : 0 < nu)
    (hgam : ∀ N i, 0 ≤ gam N i)
    (hFc : ∀ N i, Continuous (forc N i))
    (hPc : ∀ N i, Continuous (prod N i))
    (hode : ∀ N i t, HasDerivAt (amp N i) (-gam N i * amp N i t + forc N i t) t)
    (hpay : ∀ N i t, nu * prod N i t ≤ 2 * gam N i * max (amp N i t) 0)
    (hsize : ∀ N T, criticalSize N T = ∑ i ∈ S N, ∫ t in (0 : ℝ)..T, prod N i t)
    (hinit : ∀ N, ∑ i ∈ S N, max (amp N i 0) 0 ≤ M0)
    (hforc : ∀ N T, 0 ≤ T → ∑ i ∈ S N, ∫ t in (0 : ℝ)..T, max (forc N i t) 0 ≤ M1 T) :
    UniformSignedCriticalCeiling criticalSize where
  ceiling := fun T => (2 * M0 + 2 * M1 T) / nu
  bound := by
    intro N T hT
    have hcell : ∀ i ∈ S N,
        nu * (∫ t in (0 : ℝ)..T, prod N i t)
          ≤ 2 * max (amp N i 0) 0 + 2 * ∫ t in (0 : ℝ)..T, max (forc N i t) 0 := by
      intro i _
      exact ClayNS.Waleffe.cell_integrated_production_payment (hgam N i) hT
        (hFc N i) (hPc N i) (hode N i) (hpay N i)
    have hsum := ClayNS.Waleffe.finite_production_payment (S N) nu
      (fun i => ∫ t in (0 : ℝ)..T, prod N i t)
      (fun i => max (amp N i 0) 0)
      (fun i => ∫ t in (0 : ℝ)..T, max (forc N i t) 0) hcell
    rw [hsize N T, le_div_iff₀ hnu]
    have h1 := hinit N
    have h2 := hforc N T hT
    calc (∑ i ∈ S N, ∫ t in (0 : ℝ)..T, prod N i t) * nu
        = nu * ∑ i ∈ S N, ∫ t in (0 : ℝ)..T, prod N i t := by ring
      _ ≤ 2 * (∑ i ∈ S N, max (amp N i 0) 0)
            + 2 * ∑ i ∈ S N, ∫ t in (0 : ℝ)..T, max (forc N i t) 0 := hsum
      _ ≤ 2 * M0 + 2 * M1 T := by linarith

end DASHI.NS.Unforced
