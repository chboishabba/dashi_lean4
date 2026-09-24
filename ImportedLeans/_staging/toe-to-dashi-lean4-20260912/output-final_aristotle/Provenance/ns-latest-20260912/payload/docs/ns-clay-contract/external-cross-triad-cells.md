# The external cross-triad residue, cell by cell

Machine-checked source: `RequestProject/NavierStokes/WaleffeExternalCrossTriadCells.lean`
(builds inside the whole project, no `sorry`, no postulates, no added axioms;
all headline theorems trace to `propext`, `Classical.choice`, `Quot.sound`).

## What was asked

Expand the residual (external) Waleffe forcing from the output-fibre sums into
individual quartic incidence cells, construct the shared-mode partner map
`σ ↦ σ*` on those cells, and evaluate `T_{σ*} + T_σ` literally.

## What is now proved

Fix a resonant pair of distinct retained modes `p + q = k`. The external part of
the forcing of the fibre `k` is the convolution over the retained modes other
than `p` and `q`, and its pairing against `u_p × u_q` is the last open budget of
that slot (`WaleffeExternalForcingSplit.lean`).

1. **Cell expansion.** `externalResidue_eq_sum_cells`: that residue is exactly
   the sum of its quartic incidence cells
   `T_a = Re⟪ −P_k( i (u_a·(k−a)) u_{k−a} ), u_p × u_q ⟫`,
   one for each external input mode `a`.

2. **The partner map.** The shared-output-fibre reindexing is `a ↦ k − a`: it
   exchanges the two convolution orderings of one external pair `{a, k−a}`
   inside the *same* output fibre. `crossCellVec_partner` is the exact identity
   `cellVec(a) + cellVec(k−a) = pairAdvection a (k−a) u_a u_{k−a}`,
   with no transversality, helicity, support or resonance hypothesis.

3. **`T_σ + T_{σ*}` evaluated.** `crossCell_partner_sum`: on helical (Beltrami)
   modes,
   `T_a + T_{k−a} = (λ_{k−a} − λ_a) · Re⟪ P_k(u_a × u_{k−a}), u_p × u_q ⟫`.
   The helicity multipliers appear **only through their difference**. There is
   no `λ_a + λ_{k−a}` term and no unpaid remainder: in the Round-114 language,
   the antisymmetry defect of this partner map is identically zero and the
   multiplier-difference term is the whole answer. `crossCell_partner_cancel`
   records the degenerate case: helicity-degenerate partners cancel exactly.

4. **The residue as a gap-weighted quadratic form.**
   `two_mul_externalResidue_eq_pairing`: summing over the external index set
   symmetrised by the partner map (`extIdxSym`; the added indices are
   unoccupied, hence contribute zero),
   `2 · (external residue of (p,q)) = ∑_a (λ_{k−a} − λ_a) Re⟪P_k(u_a × u_{k−a}), u_p × u_q⟫`.
   This is an identity, not an estimate.

5. **Quantitative consequences.**
   * `abs_externalResidue_le_helicity_gap_sum` — Cauchy–Schwarz on the identity.
   * `abs_externalResidue_le_frequency_sum` and its Galerkin-carrier form
     `GalerkinFlow.abs_externalResidue_le_frequency_sum` — with the physical
     helical frequency bound `|λ_a| ≤ |a|`,
     `|residue| ≤ ½ ∑_a (|a| + |k−a|) ‖u_a‖‖u_{k−a}‖‖u_p‖‖u_q‖`.
   * `abs_externalResidue_le_cohelical_separation_sum` — if the field is
     co-helical (a single global helicity sign), the gap is the *difference* of
     the two frequencies, so
     `|residue| ≤ ½ ∑_a |k − 2a| ‖u_a‖‖u_{k−a}‖‖u_p‖‖u_q‖`.
     This is the multiplier-difference gain: the prefactor is the separation of
     the two partners, and it is smallest exactly on the high-high cells
     `a ≈ k/2` where the naive frequency count is worst. Its ingredients
     `wlen_triangle` and `abs_wlen_sub_le` (triangle and reverse-triangle
     inequalities for the lattice frequency) are proved here from scratch.

6. **Payment in the classical quantities.**
   * `abs_externalResidue_le_sqrt_energy_dissipation` (and its Galerkin form) —
     Cauchy–Schwarz over the symmetrised index set turns the frequency-weighted
     sum into the two classical quantities of the flow:
     `|residue of (p,q)| ≤ √(𝔇(t)·E(t))·‖u_p‖‖u_q‖`.
   * `GalerkinFlow.selected_external_residue_le` — for a *matched* selection of
     ordered pairs (no mode reused as a first component, none as a second),
     `∑_χ |residue| ≤ √(𝔇E)·E`, with no cardinality, shell or cutoff factor.
   * `GalerkinFlow.selected_external_residue_integrated_le` — hence, for every
     `c > 0`,
     `∫_{t₀}^{t₁} ∑_χ |residue| ≤ √E(t₀)·E(t₀)·( E(t₀)/(4νc) + c(t₁−t₀)/2 )`,
     uniformly in the Galerkin cutoff and in the number of pairs selected.

## What this does not close

The **algebraic** structure of the external cross-triad residue is now settled:
after the shared-mode reindexing it is a helicity-**gap**-weighted quadratic
form in projected cross products, i.e. exactly the multiplier-difference object
the far-low machinery is designed to act on, with no receipt-shuffling and no
hidden remainder.

What remains open is the **quantitative payment in the form the ladder needs**.
The estimates above are cutoff-uniform, but they are enstrophy-level: the
integrated bound for a matched selection is finite on every finite time interval
and grows like `√(T/ν)·E(t₀)²` after optimising `c`, whereas the internal
(self) payment is the `T`-independent `E(t₀)²/ν`. Nothing here supplies a
`T`-independent external payment, which is exactly the supercritical wall; the
co-helical bound improves the prefactor from `|a| + |k−a|` to `|k − 2a|`, a
genuine gain on the high-high cells but not by itself such a payment. The
selection hypotheses of the summed statements (each mode used at most once per
slot) are also a restriction: an unrestricted selection reintroduces a
Wiener-type factor. That payment — and, separately, the critical Sobolev/Simon
upgrade — are untouched by this note, and the literal Clay periodic target
remains unproved.
