# The RH analytic lane and the two-regime envelope: provenance map and frontier

This report covers one new Lean module, `Lean/Spine/RiemannBridge.lean`
(`Spine.RiemannBridge`), which connects the generic results of
`Spine.TwoRegime` and `Spine.AnchoredGram` to the RH analytic lane in
`Agda/DASHI/Analysis/Riemann*`.

**Headline answer to the question asked.** The source supports a *shared
estimate*, reused here as real Lean theorems, and **not** a type-level
transport. Two facts settle this, both proved in Lean:

* the analytic fields of the Agda producer sockets are abstract `Set`s with no
  defining equation, so a socket inhabitant can be built with every analytic
  field the unit type — `Spine.RiemannBridge.producer_socket_is_contentless`;
* every ledger in the lane is a conjunction of `ℕ`-equations `a + slack = b`,
  which is exactly `a ≤ b` (`nat_margin_iff_le`), and each ledger is inhabited
  with all fields zero (`ledgers_have_trivial_inhabitants`). Possessing a
  ledger therefore implies nothing analytic; the content has to be the
  real-valued inequality.

Nothing in the module asserts the Riemann hypothesis, and no statement about
zeta zeros is made, assumed or used. No Yang–Mills or Navier–Stokes material is
touched.

## 1. Sources inspected

Agda (read-only; Agda is not installed here, so all Agda-side statements are
source reading, not typechecking):

| Module | Kind | Analytic status as the source itself records it |
| --- | --- | --- |
| `RiemannAnalyticSubstrate` | four nested records + `RiemannHypothesisFor` predicate | Interfaces only; no inhabitant is constructed anywhere in the bundle |
| `RiemannPhiCoshCoercivityReductionExact` | `ℕ` ledger + abstract producer + Bool boundary | `coshInequalityFormalizedInDashiHere = false`, `sourceSecondMomentBoundInstantiatedHere = false` |
| `RiemannComplexPoissonFiniteRetentionExact` | `ℕ` ledgers, one derived theorem, Bool boundary | `analyticComplexPoissonContinuationProvedHere = false`, `analyticCoshCoercivityProvedHere = false`, `sourceFiniteWindowHermitianRetentionProvedHere = false`, `zetaFiniteRetentionInstantiatedHere = false` |
| `RiemannCenteredGridRetentionExact` | `ℕ` ledger + derived certificate + abstract producer | The lattice tail bound is a producer field, not proved |
| `RiemannComplexPoissonChannelSplitExact` | exact `ℤ` coordinate algebra (genuinely proved there) | Pure arithmetic; explicitly *not* the analytic continuation |
| `RiemannMixedKernelEnvelopeExact` | `ℕ` ledger + derived lemma + abstract producer | `complexSHToPhiIdentificationProvedHere = false`, `pairwiseComplexPhiDecayProvedHere = false`, `zeroPairEnvelopeSummedHere = false`, `montgomeryVaughanApplicabilityProvedHere = false` |

Lean (existing, reused): `Spine.TwoRegime` (two-regime Fourier envelope and the
local-count summation theorem) and `Spine.AnchoredGram` (the anchored Gram
surplus `‖f‖²·det Gram(t)`).

## 2. What the bridge proves

All statements below are sorry-free, use only `propext` / `Classical.choice` /
`Quot.sound`, and are printed by `Lean/Spine/AxiomAudit.lean` during the build.

**Taper coercivity** — the gap the Agda boundary marks unformalised:

* `sq_div_two_le_cosh_sub_one` : `x²/2 ≤ cosh x − 1`.
* `taper_cosh_excess_ge` : `2α² ∫ u²φ(u)² ≤ ∫ φ(u)²(cosh(2αu) − 1)`, with the
  two integrability hypotheses explicit.
* `plateau_second_moment_ge` : a taper equal to `1` on `|u| ≤ R` has second
  moment at least `2R³/3`.
* `taper_coercivity_of_plateau` : `(4R³/3)·α² ≤ ∫ φ(u)²(cosh(2αu) − 1)`, i.e.
  the Agda ledger's coercive weight `c_φ = 2M₂` may be taken to be `4R³/3`,
  strictly positive for `R > 0` (`coercive_weight_pos`).

**Retention ledgers, real content** (the `ℕ` margins become inequalities):

* `real_centered_grid_retention` : `full = 2(fin + tail)` and `tail ≤ fin` give
  `full/4 ≤ fin` — the finite one-sided grid retains at least a quarter of the
  full transverse energy.
* `real_finite_retention` : `defect + slack = fullExcess`, `slack ≥ 0`,
  `fullExcess = finiteExcess + tailLoss`, `tailLoss ≤ finiteExcess` give
  `defect ≤ 2·finiteExcess`, the real form of the doubled-finite certificate.
* The two Agda `ℕ` derivations are also re-proved in Lean on mirrored
  structures (`centered_grid_retention`,
  `kernel_envelope_gives_almost_orthogonality`).

**Kernel envelope, from `Spine.TwoRegime`:**

* `fourier_pair_sum_le` : for an integrable, differentiable taper with
  integrable derivative and a finite set `S` of nonzero frequencies with at most
  `N` per unit window and modulus `< M`,
  `∑_{ξ∈S} k ξ ≤ N‖f‖₁ + N(‖f′‖₁/2π)·∑_{m=1}^{M−1} 1/m`,
  **given** the identification `k ξ = ‖𝓕 f ξ‖` as the explicit hypothesis
  `hid`. This is exactly the field the Agda module marks
  `complexSHToPhiIdentificationProvedHere = false`; it is carried, not
  discharged. No minimum separation of frequencies is assumed.
* `envelope_zero` : the envelope vanishes at frequency `0`, so the restriction
  `0 ∉ S` is forced. By the channel-split algebra
  (`bilinear_diagonal_transverse_zero`, `diagonal_ordinate_zero`) that is
  precisely the diagonal, so the restriction *is* the off-diagonal restriction.

**Channel split** (re-proved over `ℤ`): `bilinear_diagonal_transverse_zero`,
`hermitian_diagonal_transverse_double`, `diagonal_ordinate_zero`,
`channels_recover_transverse`.

**Poisson extension:** `poisson_unit_lattice` — the real, unit-lattice Poisson
identity `∑_{n∈ℤ} f(n) = ∑_{n∈ℤ} 𝓕f(n)` under polynomial decay on both sides,
which is the honest real counterpart of the abstract
`continuedPoissonIdentity` field.

**Gram surplus:** `det_gram_surplus_of_coercive` — from a coercive lower bound
`c ≤ ‖f‖²` on the anchor (the shape the taper coercivity produces),
`c·det Gram(t) ≤ det Gram(f + t₀, t₁, …, t_r)`.

All of the above are bundled, as statements, in the record `BridgeLedger` with
the checked inhabitant `bridgeLedger`.

## 3. Honest negatives

* `producer_socket_is_contentless` — no type-level transport through the
  abstract Agda socket.
* `ledgers_have_trivial_inhabitants` — the `ℕ` ledgers admit all-zero
  inhabitants.
* `grid_envelope_not_summable` — along an arithmetic grid the two-regime
  envelope's own bound is harmonic, hence not summable. The envelope therefore
  does **not** supply the lane's `positiveLatticeTailBound`; a genuine decay rate
  or a zero-counting input is still required.

## 4. Exact remaining obligations in this lane

1. Identify the source's complex `S`/`H` kernels with a Fourier transform of a
   fixed taper (the hypothesis `hid` above; Agda:
   `complexSHToPhiIdentificationProvedHere`).
2. Supply a local-count bound `N` per unit window for the frequency set actually
   used, and a cutoff `M` (Agda: `zeroPairEnvelopeSummedHere`,
   `montgomeryVaughanApplicabilityProvedHere`).
3. Prove a summable — not merely harmonic — tail estimate for the lattice tail
   (Agda: `positiveLatticeTailBound`; the negative above says the envelope alone
   is insufficient).
4. Analytic continuation of the Poisson identity to complex arguments in a
   strip (Agda: `analyticComplexPoissonContinuationProvedHere`); only the real
   unit-lattice identity is available here.
5. Instantiate the taper of §2 from the source construction: verify the two
   integrability hypotheses and the plateau `φ = 1` on `|u| ≤ R` for the actual
   taper, and fix `R` in terms of `L`, `w` (Agda:
   `sourceSecondMomentBoundInstantiatedHere`).
6. Build any inhabitant at all of `AnalyticSubstrate`
   (`RiemannAnalyticSubstrate`); none exists in the bundle, so
   `RiemannHypothesisFor` is currently a predicate with no subject. Mathlib's
   `riemannZeta` would be the natural carrier, but that work is not attempted
   here.
7. The Agda side remains unchecked and unedited (no Agda toolchain in this
   environment).

## 5. Verification

`lake build` from the repo root builds `Synthesis`, `Cuisine`, `AgdaMirror` and
`Spine` (8198 jobs) with no `sorry`, no project `axiom`, and no `native_decide`;
`Lean/Spine/AxiomAudit.lean` prints the axiom dependencies of every headline
result of the bridge.
