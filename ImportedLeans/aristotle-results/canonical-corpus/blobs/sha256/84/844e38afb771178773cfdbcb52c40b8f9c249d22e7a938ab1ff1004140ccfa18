# The projected-cross → energy/dissipation weld, and the self/external split of the Waleffe network forcing

This note records the round that closes the weld flagged as the next
implementation step: start at

    ‖P_k(u_p × u_q)‖² ≤ ‖u_p‖² ‖u_q‖²

and compose it immediately with the selected-pair energy–dissipation summation.

Everything below is proved in Lean on the literal `ClayNS.Waleffe.GalerkinFlow`
carrier of this project (projected Galerkin system, integer Fourier lattice,
divergence-free and real Fourier data, the truncated Navier–Stokes ODE), with no
postulate, no added axiom, no `sorry`, and no bookkeeping flag. Every headline
theorem traces to `propext`, `Classical.choice`, `Quot.sound` only.

## New files

* `RequestProject/NavierStokes/WaleffeSelfPhaseEnergyPayment.lean`
* `RequestProject/NavierStokes/WaleffeExternalForcingSplit.lean`

## The chain

1. **Projected cross mass.** `nsq_leray_cross_le`:
   `‖P_k(u × v)‖² ≤ ‖u‖²‖v‖²`, from the Leray contraction (`nsq_leray_le`)
   composed with the complex Lagrange identity (`nsq_cross_le`).

2. **Helical eigenvalue ≤ frequency.** `abs_helical_le_wlen`: a Beltrami mode
   `p × u_p = −i λ_p u_p` with `u_p ≠ 0` has `|λ_p| ≤ |p|`.

3. **Integrality of the lattice.** `one_le_wsq`: a nonzero integer wavevector has
   `|k|² ≥ 1`, hence `|k| ≤ |k|²` (`wlen_le_wsq`). This is what lets a *single*
   frequency power (the helicity gap) be absorbed by *one of the two* frequency
   powers already present in the dissipation.

4. **The modal kernel bound.** `self_phase_ED_bound`:

       |λ_q − λ_p| ‖P_k(u_p × u_q)‖² ≤ D_p E_q + E_p D_q,
       E_p = ‖u_p‖²,  D_p = |p|² ‖u_p‖².

   Composed with the exact self-forcing law of
   `WaleffeSelfForcingSign.lean` this is `abs_pair_self_forcing_le_ED`:
   `|Re⟪f_k^{(p,q)}, u_p × u_q⟫| ≤ D_p E_q + E_p D_q`.

5. **Selected-pair summation.** `selected_pair_ED_sum`: for *any* Boolean
   selection `χ` of ordered pairs of retained modes,

       ∑_{(p,q)∈χ} (D_p E_q + E_p D_q) ≤ 2 (∑ E)(∑ D).

   No cardinality, resonance-count, shell or cutoff factor enters; resonance,
   helicity class and gap restrictions may all live inside `χ`.

6. **The network bound.** `GalerkinFlow.selected_self_phase_le` and
   `GalerkinFlow.selected_triad_self_forcing_le`: at every time,

       ∑_{(p,q)∈χ} |Re⟪f_{p+q}^{(p,q)}, u_p × u_q⟫| ≤ 2 E(t) 𝔇(t).

7. **The payment.** `GalerkinFlow.selected_self_phase_integrated_le` and
   `GalerkinFlow.selected_triad_self_forcing_integrated_le`, using the Galerkin
   energy identity of `WaleffeGalerkinEnergy.lean` (`energy_le_initial`,
   `integral_dissipation_le`):

       ∫_{t₀}^{t₁} ∑_{(p,q)∈χ} |Re⟪f_{p+q}^{(p,q)}, u_p × u_q⟫| dt ≤ E(t₀)² / ν.

   The right-hand side involves only the initial energy and the viscosity: it is
   uniform in the Galerkin cutoff, in the cardinality of the selection and in
   the frequency range. Nothing stronger than the classical energy expenditure
   is used.

## The self/external split

`WaleffeExternalForcingSplit.lean` makes the composition with the *literal*
forcing possible:

* `advection_self_external_split` — for distinct retained modes `p ≠ q` with
  `k = p + q`, the two convolution terms `p' = p` and `p' = q` of the advective
  sum are exactly `pairAdvection p q u_p u_q`, and the rest is the external
  convolution `externalAdvection`;
* `modalForcing_self_external_split`, `herm_force_pair_split` — hence
  `Re⟪f_k, u_p×u_q⟫ = (λ_q − λ_p)‖P_k(u_p×u_q)‖² + Re⟪f_k^{ext}, u_p×u_q⟫`;
* `GalerkinFlow.selected_pair_forcing_le` and
  `GalerkinFlow.selected_pair_forcing_integrated_le` — the whole first slot of
  the selected network forcing obeys

      ∫ ∑_{(p,q)∈χ} |Re⟪f_{p+q}, u_p × u_q⟫| dt
        ≤ E(t₀)²/ν + ∫ ∑_{(p,q)∈χ} |Re⟪f_{p+q}^{ext}, u_p × u_q⟫| dt.

## Hypotheses, stated plainly

The payment theorems assume the flow is helical on its retained modes: a
time-independent labelling `l : Wave → ℝ` with `p × u_p = −i l(p) u_p` at all
times. That is the Waleffe helical-mode setting in which the network forcing was
defined in the first place; it is the only structural assumption beyond the
`GalerkinFlow` axioms. The selection `χ`, the assignment of a forced mode to
each pair, the mode set and the time window are arbitrary.

## The remaining two slots, and the wall itself

`RequestProject/NavierStokes/WaleffeTriadInternalPayment.lean` extends the
payment from the first slot of the network forcing to all three:

* `slot_forcing_chain`, `slot_forcing_chain'` — the middle and last slots,
  `⟪u_k, f_p^{self} × u_q⟫` and `⟪u_k, u_p × f_q^{self}⟫`, are controlled by the
  same rotational normal form: the helicity gap times four modal norms;
* `abs_slot_forcing_le_ED`, `abs_slot_forcing_le_ED'` — hence by the same
  energy–dissipation kernel, using the reality condition
  `‖u_{−q}‖ = ‖u_q‖` (`GalerkinFlow.nsq_u_neg`);
* `GalerkinFlow.triadSelfForcing` — the triad-internal network forcing: `F_τ`
  with each modal forcing replaced by the two convolution terms the triad
  contributes to itself;
* `GalerkinFlow.selected_triad_internal_le` — `∑_{τ∈S} |F_τ^{int}| ≤ 6 E(t) 𝔇(t)`
  for an arbitrary selection `S` of resonant triads;
* `GalerkinFlow.selected_triad_internal_integrated_le` —
  `∫_{t₀}^{t₁} ∑_{τ∈S} |F_τ^{int}| dt ≤ 3 E(t₀)²/ν`;
* `GalerkinFlow.weightedPositiveForcing_le_external` — the Round 105 weighted
  positive network-forcing expenditure with bounded weights `0 ≤ w_τ ≤ W`
  satisfies

      ∑_τ w_τ ∫ (F_τ)₊ ≤ W (3 E(t₀)²/ν + ∫ ∑_τ |F_τ^{ext}|),

  with `F_τ^{ext} = F_τ − F_τ^{int}` (`GalerkinFlow.externalTriadForcing`).

So the open wall is now reduced, on the literal carrier, to the integrated
external cross-triad residue alone.

## What is *not* closed

The external cross-triad residue — the contribution of convolution pairs
outside the triad — is untouched by this round: it is exactly the term that
survives on the right-hand side of `selected_pair_forcing_integrated_le` and of
`weightedPositiveForcing_le_external`. The literal Clay periodic regularity
target remains open, and nothing in this round weakens it.
