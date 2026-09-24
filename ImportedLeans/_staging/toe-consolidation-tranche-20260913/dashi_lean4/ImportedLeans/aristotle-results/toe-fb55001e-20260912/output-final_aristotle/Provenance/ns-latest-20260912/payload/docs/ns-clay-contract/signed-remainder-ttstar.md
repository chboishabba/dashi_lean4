# The signed remainder `F_s`: derivative relocation, the `TT*` resolvent expansion, and where the cardinality really sits

Source: `RequestProject/NavierStokes/SignedRemainderTTStar.lean` (machine-checked,
no `sorry`, no postulate, no added axiom; every headline theorem depends only on
`propext`, `Classical.choice`, `Quot.sound`).

The resolvent/flux route of `resolvent-gram-flux.md` reduces the signed
integrated Gram debt to a single unpaid object, the spacetime remainder energy

    R_F = ∫_t ∫_s ‖F_s(t)‖² ds dt.

This round works on `F_s` itself, and deliberately **before** taking absolute
values: the earlier rounds recorded that an ℓ¹/majorized reduction of a signed
fibre sum reintroduces a cardinality cost that is fatal at critical regularity.

## 1. Exact derivative relocation (physical, radical-free)

With the repository's curl convention `curl_p u = i (p × u)`, the rotational
pair kernel is `i·K_raw`, where

    K_raw(a,b;u,v) = (a × u) × v − u × (b × v).

On divergence-free legs (`a·u = 0`, `b·v = 0`), with `p = a + b`,

    K_raw(a,b;u,v) = −p (u·v) + u (p·v) + v (p·u)          (`rawKernel_relocate`)

— an identity: every derivative has been relocated onto the **output**
frequency, and no leg frequency survives. Consequences:

* `rawKernel_swap`: the kernel is symmetric under swapping the two legs, so the
  paired (swap-symmetrized) inner forcing is the same object;
* `nrm_rawKernel_le`: `‖K_raw‖ ≤ 3|p| ‖u‖‖v‖`;
* `nsq_rawKernel_le`: `‖K_raw‖² ≤ 9|p|² ‖u‖²‖v‖²`.

No high-leg derivative, no convolution-fibre cardinality, no square root of a
lattice norm and no helical-basis angular formula is used: the proof is the
triple-product identity plus Cauchy–Schwarz on `ℂ³`. A literal witness
(`wt_rawKernel`) shows the kernel is a nonzero object on divergence-free legs,
so these are not vacuous statements.

## 2. The inner fibre carries no multiplicity

Summing the Leray-projected cells over the literal inner fibre `a + b = p` and
using Cauchy–Schwarz **in the convolution variable** gives

    ‖N_p‖ ≤ 3 |p| · E,     E = ∑_a ‖u_a‖²        (`nrm_innerForcing_le_energy`)

with no count of the fibre anywhere (`conv_le_energy`, `sum_nsq_reflect_le`).
So on the nested carrier `a+b=p, p+q=k` the *inner* dependent-row multiplicity
is not a genuine obstruction: it is paid by ℓ²-convolution, uniformly in the
Galerkin cutoff.

## 3. `TT*`: the exact signed resolvent expansion

Let `G_p = P_k(N_p × u_{k−p})` be the outer cell, `λ_p = ν(|p|²+|k−p|²)` the
literal viscous pair rate, and

    F_s(k) = ∑_{p+q=k} e^{−sν|p|²} e^{−sν|q|²} G_p

the heat-weighted **signed** remainder (`Fs`). Then

* `nsq_Fs_eq_gram`: `‖F_s(k)‖²` is the full Gram sum of the weighted cells —
  the `TT*` expansion, with no absolute value taken;
* `Fs_eq_heatCombo`: `F_s` is exactly the heat superposition of the cells at the
  rate `λ`;
* `integral_nsq_Fs_eq_resForm`:

      ∫_0^∞ ‖F_s(k)‖² ds = ∑_{p,p'} Re⟪G_p, G_{p'}⟫ / (λ_p + λ_{p'}),

  an **identity**, not an estimate. The whole heat-parameter integral of the
  squared signed remainder is the signed resolvent Gram form of its cells, so
  the diagonal/off-diagonal machinery of `ResolventHeatFactorization.lean`
  (`resForm_eq_diag_add_off`, `neg_resOff_le_resDiag`) applies to it verbatim.

## 4. The diagonal is paid, cardinality-free

`resDiag_le_energy_cube`: for every output `k`,

    ∑_p ‖G_p‖² / (2λ_p) ≤ 9 E³ / (2ν).

The `|p|²` gain of the relocated inner kernel is exactly cancelled by the
viscous pair rate, and what survives is a reflected energy sum. No fibre
cardinality, no shell count, no cutoff dependence.

## 5. What the majorized route costs, precisely

For comparison — and to record the failure mode rather than lose it — the
absolute-value route is carried out in full:

* `sum_sq_conv_le`: discrete Young `‖f∗g‖_{ℓ²} ≤ ‖f‖_{ℓ¹}‖g‖_{ℓ²}` on the
  lattice, no cardinality;
* `sum_nsq_Fs_le_heatMass` / `sum_nsq_Fs_le_energy`:

      ∑_k ‖F_s(k)‖² ≤ 9 E³ · W_s²,        W_s = ∑_p e^{−sν|p|²} |p|,

  again with no inner or outer fibre count and no shell multiplicity: the whole
  cost of the majorized route is the single scalar heat mass `W_s`.

`W_s` blows up as `s ↓ 0`, so this bound is **not** `s`-integrable and does not
bound `R_F`. That is the precise sense in which the ℓ¹ route fails here: not by
a cardinality factor any more, but by the small-`s` (high-frequency) behaviour
of one explicit scalar lattice sum.

## Honest status

* Machine-checked: items 1–5 above, on the literal integer-lattice carrier.
* Open: the off-diagonal (phase-carrying) part of the exact `TT*` identity, and
  hence `R_F = ∫_t ∫_s ‖F_s‖²`.
* Package A and the literal Clay periodic regularity target are **not** closed;
  nothing is claimed for them. No target was weakened, and no axiom, postulate
  or conditional bridge was introduced.
