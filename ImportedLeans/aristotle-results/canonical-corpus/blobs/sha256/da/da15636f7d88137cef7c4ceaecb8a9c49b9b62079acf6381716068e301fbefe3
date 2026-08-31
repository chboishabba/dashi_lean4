# The external cross-triad residue as a frequency commutator, routed by Bony class

*Lean source:* `RequestProject/NavierStokes/WaleffeExternalBonyClasses.lean`
(builds with the rest of the tree; no `sorry`, no postulates, no added axioms;
headline theorems depend only on `propext`, `Classical.choice`, `Quot.sound`).

This note continues `external-cross-triad-cells.md`, which established the exact
same-object identity

```
2 R^{ext}_{p,q} = ∑_a (λ_{k−a} − λ_a) · Re⟪P_k(u_a × u_{k−a}), u_p × u_q⟫ ,   k = p + q,
```

with **no residual antisymmetry defect**: after the shared-output-fibre
reindexing `a ↦ k − a`, the external residue is a helicity-*gap*-weighted
quadratic form in projected cross products.  The present round does two things
to that object.

## 1. The gain is the output frequency

`abs_wlen_partner_sub_le_output`: for **every** lattice decomposition
`a + (k − a) = k`,

```
| |k − a| − |a| | ≤ |k| ,
```

and (`abs_wlen_partner_sub_le_min`) also `≤ |k − 2a|`, hence

```
|λ_{k−a} − λ_a| ≤ min ( |k| , |k − 2a| )      (co-helical field).
```

The multiplier difference weighting the external residue is therefore controlled
by the **output** frequency, never by the individual leg frequencies.  This is
strictly stronger than the earlier `|a| + |k−a|` bound exactly in the dangerous
high-high regime, where both legs are large and the output is small.

Consequences, all cutoff-uniform and with no cardinality, shell, matching or
Wiener factor:

* `abs_externalResidue_le_output_frequency_sum` — the residue is `½|k|` times the
  external convolution mass of the fibre;
* `abs_externalResidue_le_output_energy` and its Galerkin form
  `GalerkinFlow.abs_externalResidue_le_output_energy` —
  `|R^{ext}_{p,q}| ≤ ½ |p+q| · E(t) · ‖u_p‖‖u_q‖`;
* `GalerkinFlow.abs_externalResidue_absorption_le` — the Young/absorption shape
  `|R^{ext}_{p,q}| ≤ (ε 𝔇(t) + E(t)/(4ε)) ‖u_p‖‖u_q‖` for every `ε > 0`.

## 2. The exact signed Bony routing

`bonyClass θ k a` routes each incidence of the fibre `k` into exactly one of

```
0 = LH (first leg low),  1 = HL (partner leg low),
2 = HH→low (both legs high vs. the output),  3 = comparable,
```

and `sum_split_four` / `externalResidue_eq_bony_split` split the residue
accordingly.  The split is an **equality of signed sums in the ambient additive
monoid**, taken *before* any absolute value: it introduces no shell count, no
matching number and no triangle-inequality loss.

The partner map `a ↦ k − a` fixes classes `2` and `3` and exchanges `0 ↔ 1`
(`bonyClass_partner`, below the threshold `θ < 1/2`), so the gap-weighted pairing
identity holds classwise (`two_mul_sum_cells_filter_eq_pairing`) on each of the
three partner-invariant pieces `LH ∪ HL`, `HH→low`, `comparable`
(`externalResidue_eq_lowhigh_split`).

## 3. Classwise payment, and its limits

| class | theorem | bound (× `√(𝔇E)·‖u_p‖‖u_q‖`) |
|---|---|---|
| `LH ∪ HL` | `abs_bonyCellsLowHigh_le` | `1/(1−θ)` |
| `HH→low` | `abs_bonyCells_HHlow_le` | `θ/2` |
| `comparable` | `abs_bonyCells_comparable_le` | `1/(2θ)` |
| all | `abs_externalResidue_classwise_le`, `GalerkinFlow.abs_externalResidue_classwise_le` | `1/(1−θ) + θ/2 + 1/(2θ)` |

The near-diagonal class `HH→low` — where the raw convolution multiplicity is
worst — therefore carries a **free small parameter** `θ`: on that class the
output frequency is `θ`-small compared with the legs, and the commutator gain is
real.  The paraproduct classes have no such gain: there the multiplier
difference is only comparable to the high leg, which is the classical far-low
(Kato–Ponce/Bony) situation.

## What this does *not* close

The classwise bounds are still obtained by bounding each cell and summing
absolute values *inside* a class.  They are **enstrophy-level** (`√(𝔇E)`), not
critical (`H^{1/2}`).  Summing the output-frequency bound over a matched
selection reproduces the same `E·√(𝔇E)` scale as before, and the Young form
above pays `ε𝔇 + E/(4ε)` per pair, whose energy term is time-independent and so
still integrates to a `T`-growing budget.

So the open analytic package is unchanged in substance:

> **A2 (open).** A cutoff-independent *critical* payment of the complete
> **signed** classwise sum of the multiplier-difference form — i.e. an estimate
> of `|∑_{χ ∈ class} R_χ|` that exploits cancellation across cells rather than
> bounding them one at a time.

What this round supplies for A2 is the exact object it must act on: the signed,
loss-free Bony routing of the residue, the fact that every class is a
partner-invariant fibre on which the gap-weighted pairing identity is available,
and the identification of the gain as the output frequency (with the extra
near-diagonal factor `|k − 2a|`).  Package **B** (critical Sobolev/Simon upgrade
and continuation weld) is untouched.

Nothing here weakens the Clay periodic target, and the literal target is neither
proved nor claimed.  This round is Lean-side only; no Agda kernel run is claimed.
