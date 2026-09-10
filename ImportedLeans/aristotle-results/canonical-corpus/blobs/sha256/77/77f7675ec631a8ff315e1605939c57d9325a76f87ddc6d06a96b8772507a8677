# The last lossy step, isolated and replaced: almost orthogonality (Schur) for the signed resolvent Gram form

File: `RequestProject/NavierStokes/AlmostOrthogonalGramSchur.lean` (Lean 4 / Mathlib,
`sorry`-free, no postulate, no added axiom; every headline theorem checked to depend only on
`propext`, `Classical.choice`, `Quot.sound`).

## Where this sits

`SignedRemainderTTStar.lean` proved the exact signed `TT*` identity

```
∫_0^∞ ‖F_s(k)‖² ds = ∑_{p,p'} Re⟪G_p, G_{p'}⟫ / (λ_p + λ_{p'}),
```

and `SignedRemainderResolventBudget.lean` paid the whole form — diagonal *and* off-diagonal — at
the price of exactly one Cauchy–Schwarz step per pair,

```
Re⟪G_p, G_{p'}⟫ ≤ ‖G_p‖ ‖G_{p'}‖,
```

which turns the Gram sum into the *square of an ℓ¹ sum* and produces the supercritical spacetime
input `∫ ‖u‖_A⁴ E dt`. That single step is the only place on this route where phase information is
discarded. This tranche operates exactly there.

## What is proved

**1. The loss, exactly.** `nsq_csDefect_eq` and `herm_re_eq_sub_defect`:

```
Re⟪x,y⟫ = ‖x‖‖y‖ − ‖ ‖y‖x − ‖x‖y ‖² / (2‖x‖‖y‖).
```

The Cauchy–Schwarz gap *is* the squared collinearity defect of the two cells; the estimate is an
equality precisely for perfectly coherent cells.

**2. The replacement.** `AlmostOrthogonal modes G A` says the pairwise coherence
`|Re⟪G_p,G_{p'}⟫|` is dominated by a symmetric nonnegative kernel with row sums `≤ A`.
`sum_sum_le_schur` is the Schur test, and `resForm_le_schur` converts the whole signed resolvent
Gram form from an ℓ¹ square into an **ℓ² sum**:

```
∑_{p,p'} Re⟪G_p,G_{p'}⟫/(λ_p+λ_{p'}) ≤ A · (∑_p ‖G_p‖²/|p|²) / (2ν).
```

The viscous pair rate `λ_p + λ_{p'} ≥ 2ν|p||p'|` still cancels the two output derivatives of the
relocated inner kernel, exactly as in the unconditional route.

**3. What it buys on the literal physical carrier.** With the physical inner forcing and the outer
Leray-projected commutator (`integral_nsq_Fs_le_schur`, `sum_integral_nsq_Fs_le_schur`,
`sum_integral_nsq_Fs_le_schur_wiener`):

```
∑_k ∫_0^∞ ‖F_s(k)‖² ds ≤ 9 A ‖u‖_A² E² / (2ν)
```

in place of the unconditional `9 ‖u‖_A⁴ E / (2ν)`: two powers of the Wiener norm traded for two
powers of the energy, still with no inner fibre count, no outer fibre count, no shell multiplicity
and no cutoff dependence. The `A = 1` instance (exactly orthogonal outer cells) is
`sum_integral_nsq_Fs_le_orthogonal_wiener`.

**4. The demand becomes critical.** `spacetime_remainder_le_critical`: on a time interval on which
the energy is bounded by `E₀`,

```
∫_{t₀}^{t₁} ∑_k ∫_0^∞ ‖F_s(k)‖² ds dt ≤ (9 A E₀²/(2ν)) ∫_{t₀}^{t₁} ‖u(t)‖_A² dt.
```

The remaining spacetime input is then the *critical* Wiener quantity `∫‖u‖_A² dt`, not the
supercritical `∫‖u‖_A⁴E dt` of the unconditional route. This is precisely the gain a
truncation-uniform Schur constant would buy, and it is now a theorem conditional on that constant
alone.

**5. The exact ledger.** `resForm_eq_cs_sub_defect`: the signed resolvent Gram form *equals* its
Cauchy–Schwarz majorant minus the resolvent-weighted total collinearity defect of the cells. Every
possible improvement over the unconditional route is therefore exactly a lower bound on that defect
sum — signed bookkeeping, with no estimate taken.

**6. Wired into the existing consumer.** `sum_resForm_outCells_le_schur` composes the same-object
receipt `resForm_outCells_eq_integral` with the Schur budget, and `sum_gram_debt_le_schur` is the
assembled signed Gram bound of `SignedGramWienerAssembly` with the spacetime budget `M` now
controlling `‖u‖_A²E²` rather than `‖u‖_A⁴E`. No other hypothesis of the consumer changes.

## Honest status

`AlmostOrthogonal modes G A` with `A` uniform in the truncation is an **input**, not a theorem:
nothing here proves that the physical outer cells are almost orthogonal. Two results delimit
exactly what is being asked.

- `almostOrthogonal_one`: the trivial kernel always works with `A = card modes` — which is exactly
  the old, cardinality-laden estimate. So the hypothesis is never vacuous, and never free.
- `card_le_of_almostOrthogonal_coherent`: a *perfectly coherent* cell family forces `A ≥ card modes`.
- `resForm_coherent_eq`: for cells that are nonnegative real multiples of a single vector, at
  constant pair rate, the signed resolvent Gram form *equals* the ℓ¹ square. No rearrangement of the
  estimate can beat it.

Two further results place the gain honestly:

- `schur_budget_le_wiener_budget`: `‖u‖_A²E² ≤ ‖u‖_A⁴E` always (because `E ≤ ‖u‖_A²`), so the
  conditional budget is never worse than the unconditional one, and is strictly better exactly for
  spread-out fields.
- `schur_budget_not_controlled_by_energy`: for every `M` there is a transverse, finitely supported
  field of unit energy with `‖u‖_A²E² > M`. So the improved input is critical, not free: it is not
  supplied by the energy inequality at a fixed time either.

Hence the improvement above is a statement about phase cancellation between the outer cells and
nothing else, and the first unresolved obligation on this route is now precisely:

> a truncation-uniform Schur (almost-orthogonality) constant for the physical outer cell family
> `G_p = P_k(N_p × u_{k−p})` at a retained output `k`.

Package A and the literal periodic Clay regularity target are **not** closed and nothing is claimed
for them. Nothing was weakened, axiomatized, or replaced by a placeholder. This tranche is
Lean-side only: no Agda kernel was run and no claim is made about the Agda rounds.
