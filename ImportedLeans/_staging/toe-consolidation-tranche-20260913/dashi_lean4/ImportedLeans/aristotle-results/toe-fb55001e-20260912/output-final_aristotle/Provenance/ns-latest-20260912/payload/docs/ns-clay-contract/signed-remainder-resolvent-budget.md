# The spacetime remainder energy `R_F`, paid — and what it now costs

*Files:* `RequestProject/NavierStokes/SignedRemainderResolventBudget.lean`,
`RequestProject/NavierStokes/SignedGramWienerAssembly.lean`.
Both build inside `lake build RequestProject`, contain no `sorry`, no
postulate and no added axiom; every headline theorem was checked with
`#print axioms` to depend only on `propext`, `Classical.choice`, `Quot.sound`.

## What was open

`ResolventGramFlux.ns_signed_gram_integral_bound` bounds the signed integrated
Gram debt by

```
2·resForm(A(t₀)) + ε·∫ resForm(A,A) + (4/ε)·∫ resForm(F,F),
```

leaving exactly one unpaid object: the spacetime remainder resolvent energy

```
R_F = ∫_t ∫_s ‖F_s(t)‖² ds dt.
```

`SignedRemainderTTStar.lean` had proved the exact signed `TT*` identity

```
∫_0^∞ ‖F_s(k)‖² ds = ∑_{p,p'} Re⟪G_p, G_{p'}⟫ / (λ_p + λ_{p'}),
```

paid its diagonal, and recorded the failure of the naive absolute-value route:
majorizing `‖F_s‖` *before* the `s`-integration leaves the scalar heat mass
`W_s = ∑_p e^{-sν|p|²}|p|`, which is not square-integrable at `s = 0`.

## The order that works

Integrate in `s` first — that step is an identity, so nothing is lost — and
majorize afterwards. The resolvent denominators then supply the two output
derivatives carried by the relocated inner kernel:

* `two_nu_wlen_mul_le_pairRate`: `λ_p + λ_{p'} ≥ 2ν|p||p'|` for the literal
  viscous pair rates `λ_p = ν(|p|² + |k−p|²)`;
* `resForm_le_sq`: hence the *whole* signed Gram form — diagonal **and**
  off-diagonal — obeys `resForm ≤ (∑_p ‖G_p‖/|p|)²/(2ν)`;
* `cell_ratio_le`: `‖G_p‖/|p| ≤ 3 B_p ‖u_{k−p}‖` whenever the inner forcing
  obeys the relocated cell bound `‖N_p‖ ≤ 3|p| B_p`, so the `|p|` gain of the
  inner kernel is exactly cancelled;
* `integral_nsq_Fs_le_profile`, `sum_integral_nsq_Fs_le_profile`: at one output
  and then summed over the outputs by discrete Young — no inner fibre count, no
  outer fibre count, no shell multiplicity, and no small-`s` divergence;
* `sum_conv_le_wienerA_sq`, `sum_integral_nsq_Fs_le_wiener`: on the literal
  physical carrier the profile is the leg-norm convolution, whose total mass is
  at most `‖u‖_A²`, giving

  ```
  ∑_k ∫_0^∞ ‖F_s(k)‖² ds ≤ 9 ‖u‖_A⁴ E / (2ν),
  ```

  with `‖u‖_A = ∑_k ‖u_k‖` the discrete Wiener-algebra norm and `E` the Galerkin
  energy; the constant is explicit and independent of the truncation;
* `spacetime_remainder_le`: the spacetime form `R_F ≤ 9M(t₁−t₀)/(2ν)` on a time
  interval where `‖u(t)‖_A⁴E(t) ≤ M`.

## The wiring into the existing consumer

`SignedGramWienerAssembly.lean` attaches this to the checked flux consumer
rather than restating it:

* `resForm_outCells_eq_integral` — the **same-object receipt**: the abstract
  resolvent energy `resForm(F,F)` of the outer cell family at output `k`, at the
  literal viscous pair rates, *is* `∫_0^∞ ‖F_s(k)‖² ds`. This is
  `PSDForm.resForm_eq_integral` composed with `Fs_eq_heatCombo`; no second
  representation of the remainder is introduced.
* `sum_resForm_outCells_le_wiener` — so the total remainder resolvent energy over
  all outputs is `≤ 9‖u‖_A⁴E/(2ν)`.
* `sum_gram_debt_le_wiener` — the assembled statement: with the damped tangent
  hypotheses of the existing consumer, summed over the outputs,

  ```
  ∑_k ∫_{t₀}^{t₁} D_Gram^{(k)}
    ≤ ∑_k 2·resForm(A_k(t₀)) + ε·∑_k ∫ resForm(A_k,A_k)
      + (4/ε)·9M(t₁−t₀)/(2ν).
  ```

  Every constant is explicit and none depends on the Galerkin truncation.

## Honest status

The remainder lane is now paid, but on a **supercritical input**. The bound is
not an energy-only bound and cannot be turned into one by rearranging this
argument: `wiener_energy_budget_not_controlled_by_energy` (a corollary of the
existing `WaleffeWienerSupercritical.wiener_norm_not_controlled_by_energy`)
exhibits, for every `M`, a transverse finitely-supported field of unit energy
whose Wiener–energy budget `‖u‖_A⁴E` exceeds `M`.

So the frontier moves from "estimate `∫_t∫_s‖F_s‖²`" — which is now a theorem,
with an explicit cutoff-uniform constant — to the truncation-uniform spacetime
Wiener quantity

```
∫_{t₀}^{t₁} ‖u(t)‖_A⁴ E(t) dt,
```

which is the *same* class of input already isolated for the Round 105
network-forcing wall, and is one power stronger than the critical Wiener
quantity `∫‖u‖_A² dt`. Recovering the critical exponent from this route would
require keeping the signed cancellation at the last step as well: the final
majorization `Re⟪G_p,G_{p'}⟫ ≤ ‖G_p‖‖G_{p'}‖` is now the only place in the chain
where phase information is discarded.

Package A and the literal periodic Clay regularity target remain **not** closed,
and nothing here claims otherwise.
