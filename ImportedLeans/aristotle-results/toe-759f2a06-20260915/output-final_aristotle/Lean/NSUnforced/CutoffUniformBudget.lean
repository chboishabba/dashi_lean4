/-
# The cutoff-uniform spacetime budget engine for the unforced A1 route

## Endpoint

`CommutatorOnlySpacetimeBudget568` (Agda:
`NSTriadKNLiveCommutatorOnlyLeafABoundaryRound568Exact`) asks for a function
`B : Time → ℚ` *independent of the cutoff* with

```
4 * ∫_0^T globalForcingFull N t dt ≤ B T      for every cutoff N and terminal T.
```

This file supplies the analytic engine that produces such a `B` from data that
is *local in time and pointwise in `t`*: an energy balance in which the literal
factor-four commutator square appears as the forcing term, and a pointwise
absorption receipt

```
4 * G t ≤ ε * D t + K * E t ,   0 ≤ ε < 2ν ,
```

in which the commutator square is split between the viscous dissipation `D`
(strictly sub-critically, `ε < 2ν`) and the energy `E`.  The output constant

`commutatorBudget ν ε K E₀ T = (2ν/(2ν−ε)) * (ε E₀/(2ν) + K E₀ T exp (K T))`

depends only on `ν, ε, K`, the initial-energy ceiling `E₀` and the terminal time
— **not** on the cutoff.  That is exactly the cutoff-independence the R568
record demands.

## What is and is not paid here

Proved: the reduction.  Given a pointwise absorption receipt with constants
uniform in the cutoff, the R568 endpoint holds with an explicit `B`.
Not proved here, and not claimed: the absorption receipt itself
(`4 G ≤ ε D + K E` with `ε < 2ν`), which is the genuine remaining PDE estimate
— see `NSUnforced/Frontier.lean` for its exact statement and the ranked seams.

## Lineage

R567 (the factor `4`), R557/R565/R553 (the reduction of the literal live R406
trajectory to this single spacetime debt), R495 (integration transport
authority), R500/R503 (the integrated direct/resolvent consumers that read the
budget), R572 (the direct leaf-A compiler).  The Grönwall step is done here by
the integrating-factor argument rather than by Mathlib's `gronwallBound`, to
keep the hypotheses in the `HasDerivAt` form the energy balance supplies.

## Status

A1 infrastructure + A1 reduction.  Unconditional Lean theorems; the PDE content
is isolated in the hypotheses.
-/
import Mathlib

open MeasureTheory

noncomputable section

namespace DASHI.NS.Unforced

/-- **Integrating-factor Grönwall.**  If `E' ≤ K E` everywhere then
`E t ≤ E 0 exp (K t)` for `t ≥ 0`.  No sign hypothesis on `E` or `K`. -/
theorem energy_le_exp_of_deriv_le {Efun Ed : ℝ → ℝ} {K : ℝ}
    (hE : ∀ t, HasDerivAt Efun (Ed t) t) (hbd : ∀ t, Ed t ≤ K * Efun t) :
    ∀ t, 0 ≤ t → Efun t ≤ Efun 0 * Real.exp (K * t) := by
  set h : ℝ → ℝ := fun t => Efun t * Real.exp (-(K * t)) with hh
  have hd : ∀ t, HasDerivAt h ((Ed t - K * Efun t) * Real.exp (-(K * t))) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (-(K * s))) (-K * Real.exp (-(K * t))) t := by
      have h0 : HasDerivAt (fun s : ℝ => -(K * s)) (-K) t := by
        simpa using (((hasDerivAt_id t).const_mul K).neg)
      have h1 := h0.exp
      refine h1.congr_deriv ?_
      ring
    have h2 := (hE t).mul h1
    refine h2.congr_deriv ?_
    ring
  have hdiff : Differentiable ℝ h := fun t => (hd t).differentiableAt
  have hanti : Antitone h := by
    refine antitone_of_deriv_nonpos hdiff fun t => ?_
    rw [(hd t).deriv]
    have hexp : (0 : ℝ) < Real.exp (-(K * t)) := Real.exp_pos _
    have := hbd t
    nlinarith
  intro t ht
  have hle : h t ≤ h 0 := hanti ht
  have h0 : h 0 = Efun 0 := by simp [hh]
  rw [h0] at hle
  have hpos : (0 : ℝ) < Real.exp (K * t) := Real.exp_pos _
  have := mul_le_mul_of_nonneg_right hle hpos.le
  calc Efun t = Efun t * Real.exp (-(K * t)) * Real.exp (K * t) := by
        rw [mul_assoc, ← Real.exp_add]; simp
    _ ≤ Efun 0 * Real.exp (K * t) := this

/-- The cutoff-independent spacetime budget produced by the absorption engine. -/
def commutatorBudget (nu eps K E0 T : ℝ) : ℝ :=
  (2 * nu / (2 * nu - eps)) * (eps / (2 * nu) * E0 + K * E0 * T * Real.exp (K * T))

/-- **Cutoff-uniform spacetime budget from a pointwise absorption receipt.**

Hypotheses, all of them local in time:

* `hE` — the energy balance `E' = −2ν D + 4 G`, with `4 G` the literal R567
  factor-four commutator-only square;
* `habs` — the absorption receipt `4 G ≤ ε D + K E` with `0 ≤ ε < 2ν`;
* `hEnn`, `hDnn` — nonnegativity of energy and dissipation;
* `hE0` — an initial-energy ceiling.

Conclusion: `4 ∫_0^T G ≤ commutatorBudget ν ε K E₀ T`, a bound built only from
`ν, ε, K, E₀, T`.  Nothing in the conclusion mentions the cutoff, so if the five
constants can be chosen uniformly in the cutoff, so can the bound. -/
theorem four_integral_forcing_le
    {Efun D G : ℝ → ℝ} {nu eps K E0 T : ℝ}
    (hnu : 0 < nu) (heps0 : 0 ≤ eps) (hepsnu : eps < 2 * nu) (hK : 0 ≤ K)
    (hT : 0 ≤ T) (hDc : Continuous D) (hGc : Continuous G)
    (hEnn : ∀ t, 0 ≤ Efun t) (hDnn : ∀ t, 0 ≤ D t)
    (hE : ∀ t, HasDerivAt Efun (-(2 * nu) * D t + 4 * G t) t)
    (habs : ∀ t, 4 * G t ≤ eps * D t + K * Efun t)
    (hE0 : Efun 0 ≤ E0) :
    4 * (∫ t in (0 : ℝ)..T, G t) ≤ commutatorBudget nu eps K E0 T := by
  have hEdiff : Differentiable ℝ Efun := fun t => (hE t).differentiableAt
  have hEc : Continuous Efun := hEdiff.continuous
  have hE0nn : 0 ≤ E0 := le_trans (hEnn 0) hE0
  -- (1) Grönwall ceiling on the energy.
  have hderiv_le : ∀ t, -(2 * nu) * D t + 4 * G t ≤ K * Efun t := by
    intro t
    have h1 := habs t
    have h2 : 0 ≤ (2 * nu - eps) * D t := mul_nonneg (by linarith) (hDnn t)
    linarith
  have hgron := energy_le_exp_of_deriv_le hE hderiv_le
  have hEceil : ∀ t ∈ Set.Icc (0 : ℝ) T, Efun t ≤ E0 * Real.exp (K * T) := by
    intro t ht
    have h1 := hgron t ht.1
    have h2 : Real.exp (K * t) ≤ Real.exp (K * T) :=
      Real.exp_le_exp.mpr (by nlinarith [ht.2])
    calc Efun t ≤ Efun 0 * Real.exp (K * t) := h1
      _ ≤ E0 * Real.exp (K * T) := by
          have := Real.exp_pos (K * t)
          nlinarith [Real.exp_pos (K * T), hEnn 0]
  -- (2) the time integral of the energy.
  have hconst : (∫ _t in (0 : ℝ)..T, E0 * Real.exp (K * T)) = E0 * Real.exp (K * T) * T := by
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    ring
  have hEint : (∫ t in (0 : ℝ)..T, Efun t) ≤ E0 * Real.exp (K * T) * T := by
    rw [← hconst]
    refine intervalIntegral.integral_mono_on hT (hEc.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _) ?_
    intro s hs
    exact hEceil s hs
  -- (3) the fundamental theorem of calculus on the energy balance.
  have hbalc : Continuous (fun t => -(2 * nu) * D t + 4 * G t) := by fun_prop
  have hFTC : (∫ t in (0 : ℝ)..T, (-(2 * nu) * D t + 4 * G t)) = Efun T - Efun 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hE x)
      (hbalc.intervalIntegrable _ _)
  have hsplit : (∫ t in (0 : ℝ)..T, (-(2 * nu) * D t + 4 * G t))
      = -(2 * nu) * (∫ t in (0 : ℝ)..T, D t) + 4 * ∫ t in (0 : ℝ)..T, G t := by
    have hadd := intervalIntegral.integral_add (μ := volume) (a := (0 : ℝ)) (b := T)
      (f := fun t => -(2 * nu) * D t) (g := fun t => 4 * G t)
      ((continuous_const.mul hDc).intervalIntegrable _ _)
      ((continuous_const.mul hGc).intervalIntegrable _ _)
    rw [hadd, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  set Y : ℝ := ∫ t in (0 : ℝ)..T, D t with hY
  set X : ℝ := 4 * ∫ t in (0 : ℝ)..T, G t with hX
  have hbal : -(2 * nu) * Y + X = Efun T - Efun 0 := by rw [← hsplit, hFTC]
  have hYbound : 2 * nu * Y ≤ X + E0 := by
    have h1 : 0 ≤ Efun T := hEnn T
    linarith [hbal, hE0]
  -- (4) the integrated absorption receipt.
  have habsint : X ≤ eps * Y + K * ∫ t in (0 : ℝ)..T, Efun t := by
    have hmono : (∫ t in (0 : ℝ)..T, 4 * G t)
        ≤ ∫ t in (0 : ℝ)..T, (eps * D t + K * Efun t) := by
      refine intervalIntegral.integral_mono_on hT
        ((continuous_const.mul hGc).intervalIntegrable _ _)
        (((continuous_const.mul hDc).add (continuous_const.mul hEc)).intervalIntegrable _ _)
        ?_
      intro s _
      exact habs s
    rw [intervalIntegral.integral_const_mul] at hmono
    have hadd := intervalIntegral.integral_add (μ := volume) (a := (0 : ℝ)) (b := T)
      (f := fun t => eps * D t) (g := fun t => K * Efun t)
      ((continuous_const.mul hDc).intervalIntegrable _ _)
      ((continuous_const.mul hEc).intervalIntegrable _ _)
    rw [hadd, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
    exact hmono
  -- (5) close the loop.
  have hKZ : K * (∫ t in (0 : ℝ)..T, Efun t) ≤ K * (E0 * Real.exp (K * T) * T) :=
    mul_le_mul_of_nonneg_left hEint hK
  have hYle : eps * Y ≤ eps * ((X + E0) / (2 * nu)) := by
    refine mul_le_mul_of_nonneg_left ?_ heps0
    rw [le_div_iff₀ (by linarith)]
    linarith [hYbound]
  have hc : 0 < 2 * nu - eps := by linarith
  have hkey : X * (2 * nu - eps)
      ≤ 2 * nu * (eps / (2 * nu) * E0 + K * E0 * T * Real.exp (K * T)) := by
    have h1 : X ≤ eps * ((X + E0) / (2 * nu)) + K * (E0 * Real.exp (K * T) * T) := by
      linarith [habsint, hYle, hKZ]
    have h2 : eps * ((X + E0) / (2 * nu)) = eps * (X + E0) / (2 * nu) := by ring
    rw [h2] at h1
    have h3 : X * (2 * nu) ≤ eps * (X + E0) + 2 * nu * (K * (E0 * Real.exp (K * T) * T)) := by
      have := mul_le_mul_of_nonneg_right h1 (le_of_lt (by linarith : (0:ℝ) < 2 * nu))
      field_simp at this
      linarith
    have h4 : eps / (2 * nu) * E0 * (2 * nu) = eps * E0 := by
      field_simp
    nlinarith [h3]
  rw [commutatorBudget, div_mul_eq_mul_div, le_div_iff₀ hc]
  linarith [hkey]

end DASHI.NS.Unforced
