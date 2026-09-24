# Operator Schur, block Schur, and what a physical producer must supply

File: `RequestProject/NavierStokes/OperatorSchurBlockCancellation.lean`
(builds clean, no `sorry`, no postulate, no added axiom; every headline theorem
was checked to depend only on `propext`, `Classical.choice`, `Quot.sound`).

The preceding tranche
([almost-orthogonality-schur.md](almost-orthogonality-schur.md)) closed the
exact Cauchy–Schwarz/collinearity-defect identity, a finite Schur compiler, and
the critical spacetime consumer, all conditionally on the realized-family
hypothesis `AlmostOrthogonal modes G A`.  This tranche sharpens the hypothesis
side of that statement in four ways.

## 1. Data-Schur versus operator-Schur

`AlmostOrthogonal modes G A` is a property of the *already realized* family
`G_p`.  That is not a cosmetic point:

* `dataSchur_snapshot_dependent` — for one fixed family of linear maps `T_p`
  (coordinate projections), one input realizes Schur constant `1` while another
  forces the trivial constant `card modes`.  A data-level constant may therefore
  depend on accidentally favourable phases in a single snapshot.

* `OperatorSchur modes T nX A` is the structural replacement: a `T_p^*T_q`-style
  kernel bound `|Re⟪T_p x, T_q x⟫| ≤ c(p,q)‖x‖²` valid for *every* input `x`,
  together with a uniform lower frame bound `b_p‖x‖ ≤ ‖T_p x‖`, and row sums of
  the normalized kernel `c(p,q)/(b_p b_q)` at most `A`.

* `almostOrthogonal_of_operatorSchur` is the realization seam
  `OperatorSchur T A ⟹ ∀ x, AlmostOrthogonal (p ↦ T_p x) A`, with `A`
  independent of `x`, and
  `spacetime_remainder_le_critical_of_operatorSchur` runs it straight into the
  existing critical consumer.

The physical outer-cell map is cubic in the field, so the `X` of `OperatorSchur`
is deliberately left as an arbitrary carrier: the abstraction is stated so that
a later choice of operator carrier (freezing legs, or lifting to a tensor
carrier) can instantiate it without changing the consumer.

## 2. The zero-safe defect ledger

`herm_re_eq_sub_defect'` and `resForm_eq_cs_sub_defect'` are the versions of the
Cauchy–Schwarz/collinearity ledger with the nonvanishing hypotheses removed —
the identity is true verbatim for zero cells, so the ledger can be applied to a
physical family without support surgery.  `two_nrm_mul_herm_re_eq` is the
division-free form
`2‖x‖‖y‖·Re⟪x,y⟫ = 2(‖x‖‖y‖)² − ‖‖y‖x − ‖x‖y‖²`.

## 3. Absolute row sums are a producer, not the phenomenon

* `exists_signed_family_resForm_zero_with_maximal_schur` — there is a cell family
  whose *signed* resolvent Gram form vanishes identically while every admissible
  absolute Schur constant is at least the cardinality of the fibre.  So a failure
  of uniform absolute row-summability does not kill the signed resolvent route;
  it refutes only that particular producer.  (`card_le_of_almostOrthogonal_unimodular`
  is the underlying no-go: absolute coherence does not see signs.)

* `sum_sum_le_block_schur` and `resForm_le_block_schur` compile the weaker
  *block* hypothesis `BlockAlmostOrthogonal` into the same conclusion:
  only aggregated block-to-block interaction is constrained, entries inside a
  block are free.  `blockAlmostOrthogonal_of_almostOrthogonal` shows the
  pointwise condition is the singleton-block case, and
  `blockSchur_strictly_weaker_than_absolute_schur` shows the inclusion is
  strict (two cells `±v` at equal viscous pair rates: one block certifies
  constant `1`, every absolute constant is at least `2`).

## 4. The weakest hypothesis the consumer actually needs

All three producers are used only through one scalar inequality,

```
GramOperatorBound nu modes G k A :
  ∑_{p,q} Re⟪G_p,G_q⟫ / (λ_p + λ_q) ≤ A · (∑_p ‖G_p‖²/|p|²) / (2ν)
```

— exactly a truncation-uniform `ℓ² → ℓ²` bound for the outer-cell Gram operator
at the output `k`.  `blockAlmostOrthogonal_single_iff` proves that single-block
Schur *is* this bound (for `A ≥ 0`), and the whole physical chain is rerun from
it: `integral_nsq_Fs_le_gramBound`, `sum_integral_nsq_Fs_le_gramBound`,
`sum_integral_nsq_Fs_le_gramBound_wiener` (`≤ 9A‖u‖_A²E²/(2ν)`) and
`spacetime_remainder_le_critical_of_gramBound`
(`≤ (9AE₀²/(2ν))∫‖u(t)‖_A²dt`).  Any future producer — angular, helical,
phase/Cotlar–Stein, block or signed — can therefore be plugged in without
touching the consumer.

## 5. What a physical producer must supply

* `comparable_shell_localization_insufficient` — for every `N` there is a family
  of at least `N` nonzero modes with pairwise comparable lengths
  (`|p|² ≤ 4|q|²`, one dyadic collar) whose cells are perfectly coherent, so
  every admissible Schur constant is at least `N`.  Finite overlap in the shell
  variable is not enough; decay in a further geometric coordinate is required.

* `almostOrthogonal_of_shiftInvariant_kernel` — the positive template: a
  symmetric nonnegative coherence kernel in the difference variable `p − q`,
  supported in a finite set of total mass `≤ A`, yields the Schur condition with
  constant `A` depending only on the kernel, hence uniform in the truncation.

## 6. The fixed-output bound in scalar coordinates

File: `RequestProject/NavierStokes/TransverseFrameSplit.lean`.

At a retained output `k ≠ 0` the cells are Leray-projected, so they live in the
two-complex-dimensional plane `k^⊥`.  `frame1 k e = k × e`, `frame2 k e = k × f₁`
is an explicit *real* orthogonal frame of that plane (`exists_frame_seed`
supplies a lattice seed `e` for every `k ≠ 0`, and `nsq_frame2` gives
`|f₂|² = |k|²|f₁|²`).  `transverse_decomp` decomposes every transverse vector
exactly in the frame, and the pairing and the masses then split with no cross
terms:

```
Re⟪v,w⟫ = ‖f₁‖²·Re(conj a_v · a_w) + ‖f₂‖²·Re(conj b_v · b_w)      (herm_re_split)
   ‖v‖² = ‖f₁‖²|a_v|²           + ‖f₂‖²|b_v|²                      (nsq_split)
```

Hence `gramOperatorBound_of_components` (and its literal-carrier instance
`gramOperatorBound_outerCells_of_components`): the truncation-uniform `ℓ² → ℓ²`
bound at one output follows from — and by exactness is equivalent in content to
— two *scalar* resolvent-form bounds, one per polarization, against the Cauchy
kernel `1/(λ_p + λ_q)`.  The vector-valued almost-orthogonality question at a
fixed output is therefore a question about two scalar coefficient sequences.
This supplies neither scalar bound.

## Honest status

Nothing here proves that the physical outer-cell family satisfies any of these
hypotheses.  The open analytic question is unchanged in substance and sharper in
form:

> Does the physical outer-cell Gram operator at each retained output admit a
> truncation-uniform `ℓ² → ℓ²` bound (`GramOperatorBound`)?

Uniform absolute row-summability, block Schur, and the operator-level condition
are three sufficient certificates for it, in strictly decreasing order of
strength.  Package A and the literal periodic Clay regularity target are **not**
closed and nothing is claimed for them.  This tranche is Lean-side only.
