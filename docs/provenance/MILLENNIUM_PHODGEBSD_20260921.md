# Millennium pass, 2026-09-21 — P vs NP / Hodge / BSD

Scope of this pass, as requested: the in-repo literal Clay programmes **P vs NP**,
**Hodge** and **BSD** only.  No Navier–Stokes, Riemann-Hypothesis or Yang–Mills
material was read, edited, copied or built.

## 1. Archive intake and provenance

`toe-millennium-pnhodgebsd-handoff-20260921.tar.gz` (≈ 405 MB, 38 814 entries) was
extracted into the workspace at `handoff-millennium-20260921/`.  That directory is
a *reference/copy source only* and is excluded from version control (the source
tarball is retained, as for the earlier handoff tarballs); the two priority
documents were copied into the tracked tree:

| tracked copy | archive original |
| --- | --- |
| `Provenance/TOE_MILLENNIUM_HANDOFF_20260921.md` | `TOE_MILLENNIUM_HANDOFF.md` |
| `Provenance/PROGRAMME_FRONTIERS_20260921.md` | `PROGRAMME_FRONTIERS.md` |

Provenance recorded by the handoff itself:

* `dashi_agda/` — `eb87aeed9d7dee71ac9a65e270e94744da3ae369`
  (`origin/agent/pr1006-three-lane-continuation`), the #1006 continuation carrying
  the global SAT-tableau work;
* `dashi_lean4/` — Lean PR #10 head `b588384521bdaa73324ed0bf587c77d66730c8e4`
  (`origin/agent/millennium-three-lane-lean-assist`), with `ImportedLeans/` and
  `artifacts/` omitted from the archive.

Portions extracted for inspection in this pass: the full `dashi_lean4/` source
tree (144 MB, 119 `Synthesis/Millennium*.lean` files) and
`dashi_agda/DASHI/Mathematics/Complexity/` (60 `.agda` files).  Nothing else was
unpacked or used.

## 2. Target chosen and what is now proved

Of the four candidate targets the payable one in this environment was **(3) the
actual `E[2]` / Galois comparison** of the BSD arithmetic lane.  The archive's
`Synthesis/MillenniumBSDCMTwoTorsionGaloisModule.lean` leaves precisely this step
as a *record of obligations*
(`structure CMTwoTorsionEllipticComparison`, fields `carrierEquiv`, `infinity`,
`zeroTorsion`, …), i.e. the comparison is assumed, not proved; and the archive's
`MillenniumBSDActualAlgClosureTwoTorsionExact.lean` argues on a transported
inductive copy `CMAlgClosureProjectivePoint` of the point set rather than on
Mathlib's own point group.

New file, built and audited here:

* `Lean/Synthesis/MillenniumBSDTwoTorsionGalois.lean` (436 lines, Mathlib-only
  imports), wired into the `Synthesis` root aggregate (`Lean/Synthesis.lean`).

Exact carriers.  The curve is the handoff's own object
`cmWeierstrass : WeierstrassCurve ℚ := ⟨0, 0, 0, -1, 0⟩`, i.e. `y² = x³ - x`; the
point group is Mathlib's `(cmWeierstrass.baseChange F).toAffine.Point` for a field
`F` that is a `ℚ`-algebra (in particular `F = AlgebraicClosure ℚ`); the Galois
action is Mathlib's coordinatewise `WeierstrassCurve.Affine.Point.map` along a
`ℚ`-algebra automorphism.  No status Boolean, ledger flag, provenance record or
re-transported carrier occurs in any statement.

Proved (sorry-free; axioms `propext`, `Classical.choice`, `Quot.sound` only):

| result | statement |
| --- | --- |
| `cmWeierstrass_discriminant` | `Δ = 64`, hence `IsElliptic` after base change |
| `cmBC_equation_iff`, `cmBC_nonsingular_iff` | the base-changed affine equation is literally `y² = x³ - x`, and equation ⇔ nonsingular |
| `cmBC_twoTorsion_classification` | `2 • P = 0 ↔ P ∈ {0, (0,0), (1,0), (-1,0)}` for every `P` in the Mathlib point group over any `ℚ`-algebra field |
| `cmBC_add_of_y_zero`, `cmP0_add_cmP1`, `cmP0_add_cmPm1`, `cmP1_add_cmPm1` | the group law on the three nonzero 2-torsion points, computed from Mathlib's addition formulas (the line `y = 0`) |
| `cmTwoTorsionHom_bijective`, `cmTwoTorsionEquiv` | an explicit additive isomorphism `ZMod 2 × ZMod 2 ≃+ E[2]`, with the handoff's labelling `(1,0) ↦ (0,0)`, `(0,1) ↦ (1,0)`, `(1,1) ↦ (-1,0)` |
| `cmTwoTorsion_card` | `Nat.card E[2] = 4` |
| `cmBC_twoTorsion_galois_fixed`, `cmQbar_twoTorsion_galois_trivial` | every `σ : F ≃ₐ[ℚ] F` fixes every 2-torsion point: the `G_ℚ`-action on `E[2]` is trivial |
| `cmTwoTorsionEquiv_galois_equivariant` | the isomorphism above is equivariant for the *trivial* action on `(ℤ/2)²` |
| `cmBaseChangeMap_twoTorsion_bijOn` | `E[2](ℚ) → E[2](ℚ̄)` is a bijection: all geometric 2-torsion is already rational |

This discharges, on literal carriers, the frontier line
“actual elliptic `E[2]` same-object / trivial `(ℤ/2)²` Galois module”.

Build evidence: `lake build Synthesis.MillenniumBSDTwoTorsionGalois` and
`lake build Synthesis` both succeed with no errors and no warnings; the file
contains no `sorry`, `axiom`, `native_decide` or `admit`; `#print axioms` on each
headline theorem reports only the three standard axioms.

## 3. Remaining mathematical assumptions (honest frontier)

Nothing in this pass proves, or claims to prove, BSD or any part of it beyond the
table above.  The BSD arithmetic chain still requires, in order:

1. **`H¹(G_ℚ, E[2]) ≅ (ℚ*/(ℚ*)²)²`.**  Unpaid.  With the action now proved
   trivial, `H¹` of the profinite group with coefficients in `(ℤ/2)²` is the
   group of *continuous* homomorphisms `G_ℚ → (ℤ/2)²`; identifying that with
   square classes is Kummer theory for `μ₂`.  Mathlib's `groupCohomology` is
   abstract (non-continuous) cochain cohomology, so the correct object
   (continuous Galois cohomology) is not available off the shelf and would have
   to be built; using the abstract `H¹` instead would silently change the object.
2. **Local conditions.**  Comparison of the local `H¹` conditions at each place
   with the archive's explicit local Kummer-image conditions
   (`MillenniumBSDLocalKummer*`): unpaid, and dependent on (1).
3. **Explicit Sel² ≅ cohomological Sel²** and **Selmer cokernel ≅ Ш(E/ℚ)[2]**:
   unpaid; these are the archive's
   `MillenniumBSDExplicitSelmerCokernelExact` / `…ShaCohomologicalBoundary`
   targets, which at present connect abstract representation data by records.
4. Everything downstream (rank formula, analytic side) is untouched.

Assumptions carried by the new file itself: only `F` a field with a `ℚ`-algebra
structure (whence characteristic zero) and classical choice for `DecidableEq` on
`AlgebraicClosure ℚ`.  There are no postulates, no imported unproved lemmas, and
no dependence on any other module of this repository.

## 4. Status of the three other candidate targets (not attempted here)

* **(1) P vs NP — global Cook–Levin tableau.**  The archive's Agda lane
  `dashi_agda/DASHI/Mathematics/Complexity/` (60 modules, e.g.
  `ConcreteTapeGlobalCookLevinCNFExact`, `ConcreteTapeGlobalTransitionConjunctionExact`,
  `ConcreteTapeAcceptanceEndpointSoundExact`, `ConcreteTapeCookLevinSizeExact`,
  `CookLevinPolynomialSizeExact`) contains **no `postulate` declarations**.  It was
  not typechecked here: no Agda toolchain exists in this environment, so its
  kernel status is unverified by this pass.  A Lean re-implementation of the
  global tableau ⇄ accepting-run equivalence from scratch was out of reach
  alongside a completed target.
* **(2) Hodge — realization unit induces `H₂` iso.**  The archive's
  `Synthesis/MillenniumHodgeTetrahedralRealizationUnit.lean` genuinely builds the
  adjunction unit `∂Δ[3] ⟶ TopCat.toSSet.obj |∂Δ[3]|` and its face-level values,
  but the homology comparison is a record
  (`structure TetrahedralRealizationHomologyComparison` with field
  `unitInducedH2Equiv : Nonempty (… ≃ …)`), and the downstream
  `tetrahedral_realization_H2_equiv_Q` merely transports that assumed
  equivalence.  Closing it needs the simplicial-to-singular homology comparison
  theorem for geometric realization, which Mathlib does not provide; that is a
  substantial development in its own right, not a one-file gap.
* **(4) BSD analytic — `c_{4m+1}^η = a_{4m+1}(E)`.**  Genuinely the classical
  identity between the weight-2 level-32 eta product and the `L`-coefficients of
  this curve; there is no partial Lean infrastructure in the archive that reduces
  it to finite checks, so it was not a payable one-pass target.

## 5. Dependency map of the new work

```
Mathlib
  ├ AlgebraicGeometry.EllipticCurve.Affine.Point   (Point, neg_some, add_of_X_ne,
  │                                                  map, map_some, map_injective)
  ├ AlgebraicGeometry.EllipticCurve.Weierstrass    (baseChange, Δ, IsElliptic)
  ├ Data.ZMod.Basic / ZMod.lift, zmultiplesHom
  └ FieldTheory.IsAlgClosed.AlgebraicClosure
        ↓
Lean/Synthesis/MillenniumBSDTwoTorsionGalois.lean
        ↓
Lean/Synthesis.lean   (root aggregate; builds)
```

No edge runs from the new file to any other DASHI module, and no DASHI module is
required by it: the result is self-contained against Mathlib, which is what makes
its carriers checkable.
