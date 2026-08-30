# The carrier bridge, the expenditure ledger and the scale probe

This note records the tranche added on top of the C53–C55 Gaussian material and
the anchor inequality.  Everything below is a Lean theorem that compiles with no
`sorry`, no postulates, and no axioms beyond Lean/Mathlib's standard three.

## C lane: the compact-support carrier bridge (the first previously unresolved item)

`RequestProject/NavierStokes/CompactCarrierBridge.lean`

The weight-aware Caccioppoli budget lives on the periodic cell against a
strictly positive Gaussian; the parabolic `L^{10/3}` embedding
(`ClayNS.parabolic_gain_of_caccioppoli`) consumes compactly supported
truncations on `ℝ³`.  The bridge is now proved.

* `ClayNS.BallCutoff` — cut-off data on the concentration ball
  `∑_j (x_j − x₀_j)² ≤ R²` (smooth, `[0,1]`-valued, vanishing off the ball, with
  a gradient bound `L`), and `ClayNS.exists_ballCutoff` — such data exists and
  can be taken equal to `1` on the half ball, so nothing here is vacuous.
* `ClayNS.cutoff_mass_le_weighted` — first Caccioppoli slot:
  `∫|ψq|² ≤ e^{1/(4κ)}·∫_{B_R}Φ_{κR²}q²`.
* `ClayNS.cutoff_dissipation_le_weighted` — second slot:
  `∫‖∇(ψq)‖² ≤ 2e^{1/(4κ)}(∫_{B_R}Φ‖∇q‖² + L²∫_{B_R}Φq²)`; the cut-off loss
  multiplies the mass term only.
* `ClayNS.compactCarrier_parabolic_gain` — the two combined and fed to the
  embedding:

      ∫∫|ψq|^{10/3} ≤ C_S·K^{5/3},  K = 2e^{1/(4κ)}(Mw + Dw + L²(b−a)Mw).

  All constants depend only on `(κ, R, L, b−a)`; the truncation level enters
  only through the budgets `Mw`, `Dw`.  That level-independence is exactly what
  the De Giorgi recurrence requires.

## Charging the modulus active set to the budget

`RequestProject/NavierStokes/ModulusOccupation.lean`

Rather than controlling every bad level separately, the occupation of the bad
set is charged to the finite budget:

* `ClayNS.level_measure_le_setIntegral_rpow` — Chebyshev: `kᵖμ(A_k) ≤ ∫|q|ᵖ`.
* `ClayNS.modulus_occupation_bridge` — space-time: `∫μ(A_k(t))dt ≤ B/kᵖ`.
* `ClayNS.halfBall_occupation_le_of_weighted_budget` — end to end: starting from
  the Gaussian-weighted budget on the concentration ball, the modulus bad set at
  level `k` inside the half ball occupies at most `C_S·K^{5/3}/k^{10/3}` of
  space-time.
* `ClayNS.exists_level_occupation_lt` — hence less than any prescribed amount
  beyond an explicit level.

This is the modulus (spatial level-set) counterpart of a shell residence charge:
the carrier is `|δ_h u|` rather than a Fourier-shell amplitude, and the charge is
against the Caccioppoli budget produced above.

## The expenditure ledger, the geometric tail and the residence charge

`RequestProject/NavierStokes/ExpenditureLedger.lean` (abstract) and
`RequestProject/NavierStokes/ExpenditureInstantiation.lean` (instantiated)

* `ClayNS.coercive_expenditure_le` / `ClayNS.shell_expenditure_le` — the
  post-Caccioppoli algebra `E_total = E_coercive + E_absorbed` ⇒
  `E_coercive ≤ Φ(0) + E_remainder`, inherited by sub-expenditures.
* `ClayNS.geoTail_tsum_eq`, `ClayNS.exists_scale_geoTail_tsum_le` — the dyadic
  tail `ε(R) = C·2^{−αR}` assembles to a geometric series and can be pushed below
  any absorption budget: the quantitative form of "positive-dimension residual ⇒
  arbitrarily small absorbable budget".
* `ClayNS.residence_charge_sum`, `ClayNS.residence_time_le_of_charge` —
  `∑Δt·λA² ≤ C_B∑Δt·D`, and hence `∑Δt ≤ C_B·D_total/(λA₀²)` for a family of
  bad cells: finite occupation.
* `ClayNS.coercive_expenditure_scaleInvariant` — the ledger instantiated on the
  actual Navier–Stokes weight-aware space-time budget at `a = κR²`:

      ∫[(1−η)νJ₂ + (ν/2)J₁] ≤ M(t₀) + ∫(27A²B⁴/4ην)K₂ + (t₁−t₀)·R·gwScaleConst.

  The remainder carries a strictly positive power of the concentration scale.

## A lane: the scale probe

`RequestProject/NavierStokes/ApproximateScaleAnchor.lean` and
`RequestProject/NavierStokes/ScaleProbeRadial.lean`

The exact anchor hypothesis `⟨e,ΛU⟩_Γ = 0` is not free for Navier–Stokes: the
linearisation around a self-similar profile carries advection and pressure
terms, so it cannot be obtained from self-adjointness in the Gaussian metric.
The following replace that route.

* `ClayNS.gram_anchor_lower_bound_approx` — the **approximate anchor**: with
  `|⟨e,Λu⟩| ≤ δ`, `⟨e,u⟩ = a₀`, `‖e‖²_Γ ≤ 1` and a bound `Mc` for the
  collinearity coefficient `|C|/B`,

      (|a₀| − Mc·δ)²·‖Λu‖²_Γ ≤ Δ.

  At `δ = 0` this is the exact anchor inequality; it degrades continuously in
  `δ`, so an approximately blind probe suffices.
* `ClayNS.gramC_riesz`, `ClayNS.gramA_riesz`, `ClayNS.probe_scale_coercivity` —
  the Riesz step: a probe weight `w` becomes the anchor mode `e = w/Γ`, with
  `⟨e,V⟩_Γ = ∫⟨w,V⟩` and `‖e‖²_Γ = ∫|w|²/Γ`.  So *one separating probe* forces a
  quantitative scale-Gram defect.
* `ClayNS.radial_probe_adjoint` — the exact adjoint identity for a radial probe,
  `∫φ(V+rV')r² = [φVr³] − ∫(2φr²+φ'r³)V`: the cancellation is done before
  absolute values, and the scale residual `2φr² + φ'r³` is isolated.
* `ClayNS.scaleNeutral_no_go` — a scale-neutral weight that is differentiable up
  to the origin vanishes identically.  An exactly invariant probe is therefore
  never regular at the concentration point: it must be cut off.
* `ClayNS.radial_cutoff_probe_residual` — for the cut-off homogeneous weight
  `φ = χ(r)/r²` with `χ` vanishing at both ends, the residual is *exactly*
  `−∫χ'(r)·r·V(r)dr`: supported in the transition annuli, with one extra
  positive power of `r`.
* `ClayNS.radial_probe_separates` — the separation criterion: if the profile
  keeps a definite sign and size `m` across the range while the transition cost
  `(∫|χ'|r)·sup|V|` is smaller than the accumulated bulk `m∫χ`, then
  `|L(ΛV)| < L(V)` — precisely the input `δ < |a₀|` of the approximate anchor.

## What is still open on the A lane

The separation criterion is a genuine criterion, not a construction: for the
actual Navier–Stokes rescaling one still has to exhibit a profile range on which
the bulk beats the transition cost, and to control the Gaussian normalisation
`∫|w|²/Γ ≤ 1` of the resulting weight in three dimensions (the file works with
the radial reduction, i.e. up to the angular factor).  Until that is supplied,
the anchor constant `a₀` for the actual Navier–Stokes profile remains an input,
and the literal Clay periodic target is not proved.
