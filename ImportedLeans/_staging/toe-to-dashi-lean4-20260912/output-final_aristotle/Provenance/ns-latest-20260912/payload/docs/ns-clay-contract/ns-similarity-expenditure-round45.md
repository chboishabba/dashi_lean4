# Round 45 — scale expenditure in similarity variables

Parent: [Navier–Stokes Clay contract README](README.md).
Diagram: [similarity-expenditure.puml](similarity-expenditure.puml).

This round works only on the Navier–Stokes lane. It follows the plan of
removing marginal directions before taking absolute values, measuring motion
with a Gram defect, paying cross terms quadratically, and telescoping a single
expenditure instead of paying a worst case at every scale.

## Plan for the round

| Lane | Aim | Result |
| --- | --- | --- |
| A1 | Write the exact energy identity in self-similar variables | done |
| A2 | Show the Gram defect is a projective speed | done |
| A3 | Turn the identity into a finite expenditure budget | done |
| A4 | Use that budget to remove the assumed telescopic payment on the A side | done |
| A5 | Split the nonlinear and pressure term into marginal and transverse parts | done |
| B | Weaken the blow-up compactness hypothesis | done, partially: equicontinuity replaces uniform Lipschitz; equation inheritance still open |
| C | Ancient rigidity | not attempted this round; kept as is |

Measure of progress used throughout: **the number of independent unproved
continuum estimates that enter the final contradiction.** A new file that
leaves the same estimates untouched counts as no progress.

## What is now proved

All statements below compile with the rest of the library, contain no `sorry`
and no postulates, and use only the three standard axioms.

New file [`SimilarityEnergy.lean`](../../RequestProject/NavierStokes/SimilarityEnergy.lean):

- `ClayNS.similarity_energy_identity` — the exact identity
  `H'(τ) = −‖V_τ‖² − ⟪N, V_τ⟫` for `H = ½a(V,V) + ¼‖V‖²`. The dissipated
  quantity is exactly the squared speed of the solution through scale space;
  the only enemy left is the pairing of the nonlinear and pressure terms with
  that same velocity.
- `ClayNS.projective_speed_sq`, `ClayNS.hasDerivAt_normalize`,
  `ClayNS.projective_gram_speed` — the Gram determinant `AB − C²` divided by
  `A²` is literally the squared speed of the normalised profile `V/‖V‖`. So the
  quantity the scale-Gram machinery measures is a distance travelled, after the
  pure amplitude direction has been divided out.
- `ClayNS.gram_projective_speed_weighted` — the same in the weighted integral
  language already used by `GaussianScaleGram.lean`.
- `ClayNS.transverse_quadratic_debt` — a cross term `2cpq` against a coercive
  direction `λq²` costs `c²/λ`, never `c`.
- `ClayNS.similarity_transverse_expenditure` — the telescope: if the energy
  falls at least at rate `(1−η)q` minus a remainder, the total expenditure over
  a window is at most one energy drop plus the total remainder.
- `ClayNS.scaleGram_payment_of_expenditure` and
  `ClayNS.scaleGram_payment_of_similarity_absorption` — the change of variable
  `τ = −log r` that converts that budget into the payment statement the A-side
  assembly consumes.

New file [`SimilarityScaleCharge.lean`](../../RequestProject/NavierStokes/SimilarityScaleCharge.lean):

- `ClayNS.clay_A_dyn_of_similarity_absorption` — the A-side gate, with the
  previously assumed telescopic payment (`hstar`) **derived** rather than
  assumed. What replaces it is an energy-drop bound, the absorption estimate,
  and the exact identity above.
- `ClayNS.clay_A_dyn_of_similarity_equation` — the same gate starting one step
  earlier, from the similarity equation itself: the energy, its derivative and
  the absorption are all produced internally, so the inputs left on this side
  are the energy drop, the size of the nonlinear and pressure term, the
  scale-Gram/speed comparison, and the unchanged flux splitting.

New file [`SimilarityAbsorption.lean`](../../RequestProject/NavierStokes/SimilarityAbsorption.lean):

- `ClayNS.pairing_marginal_split` — the exact split
  `⟪N,W⟫ = ⟪N,PW⟫ + ⟪N⊥,W⊥⟫`: the marginal channel is computed, not bounded.
- `ClayNS.pairing_young_absorption`, `ClayNS.marginal_transverse_absorption`,
  `ClayNS.similarity_energy_deriv_le`,
  `ClayNS.similarity_energy_deriv_le_transverse` — the pairing absorbed into a
  fraction of the transverse speed plus an explicit remainder, in exactly the
  shape the telescope consumes.

New file [`BlowupEquicontinuousCompactness.lean`](../../RequestProject/NavierStokes/BlowupEquicontinuousCompactness.lean):

- `ClayNS.UniformlyEquicontinuous` and
  `ClayNS.blowup_compactness_and_inheritance_of_equicontinuous` — the blow-up
  extraction now needs only a common modulus of continuity.
- `ClayNS.uniformlyEquicontinuous_of_equiLipschitz` — the old hypothesis is a
  special case, so the replacement is strictly weaker.
- `ClayNS.LocallyEquicontinuous` and
  `ClayNS.blowup_compactness_and_inheritance_of_locallyEquicontinuous` — weaker
  still: the modulus need only be shared on each bounded set, which is the
  shape interior parabolic estimates produce. Uniform equicontinuity is a
  special case of it.

## Effect on the ledger

Before this round the A side needed two independent analytic inputs: the flux
splitting and the telescopic payment. The payment is no longer an input. In its
place stand one physical estimate (absorption of the nonlinear and pressure
pairing) and one uniform bound (the similarity energy drop along the singular
sequence), both stated in the same variables as the identity that produces
them.

Count of independent unproved continuum estimates entering the contradiction:

| Item | Before | After |
| --- | --- | --- |
| Flux splitting | input | input |
| Telescopic payment of the scale expenditure | input | derived |
| Absorption of nonlinear and pressure pairing | not stated | one input, in the shape the telescope needs |
| Energy drop along the sequence | not stated | one uniform bound |
| Ancient rigidity (directional level drop) | input | input |
| Compactness | uniform Lipschitz assumed | modulus of continuity assumed; equation inheritance open |
| Local existence and continuation | open | open |

## Testing phase

Checks run after the work, not before:

1. Whole-library build after every change: successful (8137 targets).
2. Search of the new sources for `sorry`, `axiom`, `postulate`,
   `implemented_by`: none present.
3. Axiom trace of every new headline theorem: `propext`, `Classical.choice`,
   `Quot.sound` only.
4. Hidden-assumption review: the new statements assume no global integrability,
   no Lipschitz bound and no rate of convergence. The compactness statement was
   checked to be implied by, and strictly weaker than, the previous one.
5. Rescaling check: the bridge to the scale variable uses the exact change of
   variable `τ = −log r`, so no power of the scale range is introduced.
6. Pressure treatment: the pressure enters only inside the term `N` and is
   never estimated separately, so no gauge choice is hidden.

## What is still open

1. The physical absorption estimate for the nonlinear and pressure pairing on
   the actual blow-up carrier, with constants independent of the sequence
   index.
2. The uniform bound on the similarity energy drop along that sequence.
3. Ancient rigidity, still in the form `ClayNS.DirectionalLevelDrop`.
4. Equation, local-energy and pressure inheritance through the blow-up limit.
5. Classical periodic local existence and continuation.

The literal Clay periodic regularity target is **not** proved, and nothing here
weakens it.
