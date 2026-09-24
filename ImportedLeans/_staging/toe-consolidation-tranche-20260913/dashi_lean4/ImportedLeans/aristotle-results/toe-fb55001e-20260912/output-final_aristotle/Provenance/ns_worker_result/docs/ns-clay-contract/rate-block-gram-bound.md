# Rate blocks: what the outer-cell Gram operator bound costs, and what it needs

Lean source: `RequestProject/NavierStokes/RateBlockGramBound.lean`
(namespace `ClayNS.RateBlocks`, imports `TransverseFrameSplit`).
No `sorry`, no postulate, no added axiom; every headline theorem was checked to
depend only on `propext`, `Classical.choice`, `Quot.sound`.

## The obligation being measured

The critical spacetime consumer
(`spacetime_remainder_le_critical_of_gramBound`) needs exactly one hypothesis at
each retained output `k`:

```
GramOperatorBound nu modes G k A :
  ∑_{p,q ∈ modes} Re⟪G_p,G_q⟫/(λ_p+λ_q) ≤ A · (∑_{p} ‖G_p‖²/|p|²)/(2ν),
  λ_p = viscousPairRate nu p (k−p) = ν(|p|² + |k−p|²)
```

with `A` uniform in the Galerkin truncation.  This file measures `A` against one
geometric quantity of the retained mode set: the multiplicity of its **dyadic
rate blocks**, `blk p = b` meaning `λ_p ∈ [4^b, 4^{b+1})`.

## 1.  Positive: `A = 32·m`, for free

`gramOperatorBound_of_rateBlockMultiplicity`.  If every dyadic rate block carries
at most `m` retained modes (`BlockMultiplicity`), the bound holds with
`A = 32·m`, for **every** cell family — no almost orthogonality, no signs, no
field structure.

The proof is a Schur test against the Cauchy kernel `1/(λ_p+λ_q)`:

* `amgm_block` — the elementary pair estimate, with no square roots: if
  `s ∈ [L,4L)` and `t ≥ 4^d·L`, then `uv/(s+t) ≤ 2·2^{-d}(u²/s + v²/t)`.
  So the kernel decays geometrically in the rate-block distance.
* `sum_half_pow_natAbs_le` — `∑ 2^{-|d|} ≤ 4` over *any* finite set of integers,
  hence uniformly in the truncation; `rowsum_le` turns this into Schur row sums
  `≤ 4m`.
* `sum_resForm_le_blockMultiplicity` — the abstract form of the bound for an
  arbitrary positive rate function.

## 2.  Negative, and sharp: `A ≥ N` on a comparable shell

`gramOperatorBound_fails_on_comparable_shells`.  For every `N` there are: a
retained output `k ≠ 0`; at least `N` nonzero modes with pairwise comparable
lengths (`|p|² ≤ 4|q|²`), hence inside boundedly many rate blocks; and a cell
family that is *transverse* at the output (as the Leray projection forces), such
that every admissible `A` is at least `N`.  The general mechanism is isolated in
`gramBound_const_cells_lower_bound`: with all pair rates `≤ Λ` and all lengths
`≥ √W`, a family of equal nonzero cells forces `A ≥ card·νW/Λ`.

This is strictly stronger than the corresponding statement for the absolute
Schur constant (`comparable_shell_localization_insufficient`): it defeats the
*weakest* hypothesis the critical consumer needs.  So no truncation-uniform `A`
can come from the kernel, transversality and dyadic shell localization alone,
and the linear dependence on the block multiplicity in §1 is the truth for a
general cell family.

## 3.  Inside one rate block: the obligation is square-root cancellation

`nsq_sum_eq_sum_sum_herm_re` — `‖∑_p G_p‖² = ∑_{p,q} Re⟪G_p,G_q⟫`: the signed
double sum *is* the mass of the aggregated cell.

At a degenerate cluster (all retained pair rates equal — the configuration the
lower bound exploits; non-vacuous by `viscousPairRate_reflect` and
`exists_two_mode_degenerate_cluster`), the two directions are exact:

* `gramOperatorBound_of_cluster_cancellation` — if
  `‖∑_{p} G_p‖² ≤ C·∑_p ‖G_p‖²`, then `GramOperatorBound … C`;
* `cluster_cancellation_of_gramOperatorBound` — conversely the bound forces
  `‖∑_p G_p‖² ≤ C·(λ/νW)·∑_p ‖G_p‖²`.

`sum_outerCellVec_eq` identifies the aggregate for the *literal* cells: it is
`P_k(∑_{p ∈ cluster} N_p × u_{k−p})`, the Leray projection of a single
convolution sum, and `gramOperatorBound_outerCells_of_cluster_cancellation`
states the obligation directly in those terms.

So the remaining physical obligation is no longer an abstract Schur estimate.
It is a concrete statement about the field: the aggregated cell
`∑_{p ∈ cluster} P_k(N_p × u_{k−p})` — a piece of the Leray-projected
nonlinearity — must exhibit square-root cancellation relative to its own cells,
with a constant independent of the truncation.

## Honest status

Nothing here supplies that cancellation for the physical outer cells.  The
positive theorem of §1 degrades exactly as the truncation grows (a dyadic shell
of the lattice contains many modes), the negative theorem of §2 shows that this
degradation is not an artifact of the method, and §3 says precisely which
physical quantity has to be estimated instead.  Package A and the literal
periodic Clay regularity target are **not** closed and nothing is claimed for
them; no target was weakened and no axiom, postulate, conditional bridge or
placeholder was introduced.  This tranche is Lean-side only: no Agda kernel was
run and no Agda receipt is claimed.
