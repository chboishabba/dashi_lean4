# Corrections to the integration pass: three boundaries rescoped, positive rows added

This pass revisits three negative rows of the global map that were stated more
broadly than the code supports, and adds the positive structure that the corpus
does contain in each place.  Everything below is machine-checked in
`Lean/Integration/` (`lake build Integration`, no `sorry`, no project axiom, no
`native_decide`); the Agda side is read-only in this environment, so every
statement about an Agda module is a source reading and is labelled as such.

---

## 1. Base369 XOR: additive natively, affine after moving to the polarity origin

**Previous wording.** "The `Base369` XOR is affine (`x+y+1`), not addition, so
the corpus's two ternary operations are not the same group law."

**What the code says.**  Both of the following are theorems, about the same
operation in two charts:

| chart | origin | law |
| --- | --- | --- |
| native index (`triIdx`, `Base369`'s own coordinate) | `tri-low` | `triIdx_xor` : `triIdx (triXor a b) = triIdx a + triIdx b` |
| balanced (`balTone`, the hub coordinate) | `tri-mid` | `balTone_triXor_affine` : `balTone (triXor a b) = balTone a + balTone b + 1` |

`balTone_eq_triIdx_sub_one` gives the translation between them, and the choice
is not free: `triReflect_fixed_point_unique` shows `tri-mid` is the unique fixed
point of the polarity involution, `triIdx_not_polarity_compatible` shows the
native chart is therefore *not* polarity-compatible, and
`bal_unique_up_to_sign` (earlier work) shows the balanced chart is the only
polarity-compatible one up to sign.  `triXor_chart_dichotomy` packages all five
facts.

**Corrected boundary (B2 in the map).** The refuted claim is additivity *in the
balanced chart*.  It is not a claim that `triXor` fails to be a group law — in
its native chart it is one.

---

## 2. The nonary layer: the address carrier does not determine the algebra

**Previous wording.** "`ℤ/9 ≇ (ℤ/3)²`, so the nonary layer is provably not two
ternary layers."

**What the code says.**  The negative is intact but is about *operations*:
`nonary_not_ternary_square` refutes any bijection carrying the cyclic
`nonaryXor` to componentwise `triXor`.  The corpus nonetheless builds a
nine-state carrier by symmetry reduction and charts it onto the same nine
labels, and this pass completes that picture in
`Lean/Integration/PhaseQuotient.lean`:

* `rotateOutputCode_ne` — the order-three output phase acting on the 27
  level-two ternary endomorphism codes is **free**;
* `phaseEquiv : LevelTwoCode ≃ Phase3 × PhaseQuotient9` — hence `27 = 3 × 9`;
* `quotient_eq_iff_orbit` — the nine-element coordinate is *exactly* the orbit
  space `T³/C₃`: invariant under the action and separating its orbits.  (The
  Agda proves the encode/decode round trips; the orbit characterisation is
  added here.)
* `nonaryChart` — the corpus's two-sided chart `PhaseQuotient9 ↔ NonaryTruth`;
* `nonaryPhaseAdd` — the quotient's componentwise addition **transported** onto
  the nonary labels.  The Agda has both halves and never composes them.
* `phaseZModEquiv_add` — that transported law is `ℤ/3 × ℤ/3`;
  `nonaryPhaseAdd_exponent_three` versus `nonaryXor_order_nine` separates it
  from the cyclic law, and `q9_nonary_group_iso_impossible` shows no relabelling
  identifies the two.

**Corrected boundary (B1).**  Nine labels, two algebras, one carrier chart: the
address carrier does not determine the algebra.  The no-go does not refute the
nine-state phase quotient, and the map now says so.

---

## 3. The Monster support map: an observer-loss boundary, not an SSP boundary

**Previous wording.** "The hyperfabric support map is non-expansive but not
injective, not an isometry and not an algebra map", filed as a boundary of the
15-prime layer.

**What the code says.** Those three theorems are about one Boolean observer, and
`support t = decide (t ≠ neg)` is the indicator of *not the `tritXor`
identity* — a native-chart observer, aligned with the additive origin rather
than the polarity-fixed one.  `Lean/Integration/ObserverQuotient.lean` separates
the layers:

* **What is preserved.**  `polarPresence t = decide (t ≠ zer)` is the
  polarity-invariant observer, and `polarPresence_orbit` proves it is *exactly*
  the quotient map of the polarity involution.  Along it the symmetry action
  descends, and the induced action is forced to be the identity
  (`polarPresence_equivariant`, `laneAction_descends`): the commuting square
  `π (g · x) = ḡ · π x` is a theorem.
* **What is lost.**  The sign, precisely: `no_equivariant_section` shows no
  section of the observer is polarity-equivariant, and `presence_lossy` mirrors
  the corpus's own point that Boolean presence forgets multiplicity.
* **The strengthened negative.**  `support_no_descent` and
  `polarPresence_no_descent`: *no* binary Boolean operation whatsoever makes
  either observer a homomorphism for the ternary XOR.  This is strictly stronger
  than the corpus's `support_not_hom`, which refutes boolean OR only.
* **The SSP layer is untouched by all of this.**
  `Lean/Integration/SSPWeave.lean` proves the orientation monoid associative,
  the sign map onto `ℤ/2` a monoid homomorphism, transport functorial
  (`transportSSP_comp` : `T_{q∘p} = T_q ∘ T_p`), and the lane-state carrier
  equal to the ternary hub with `inverse` acting as the hub polarity
  (`laneStateHub`).  It also proves the monoid is *not* a group (`not_a_group`).
* **The signed layer that keeps the algebra.**  `defectOrientationHub` and
  `defectToFibreOrientation_equiv` identify the signed relational defect's
  orientation with both the ternary hub and the SSP orientation carrier, with
  reversal matching on all three.

**Corrected boundaries (B4–B6, plus new B9–B11).**  B4–B6 are relabelled
observer-level; B6 is replaced by the stronger "no binary Boolean operation"
form; B9 records that support is not polarity-invariant; B10 that the
orientation monoid is not a group; B11 that no direct `9 → 6` retraction exists.

---

## 4. Also added: the residual-bearing 9 → 6 projection is exact

`Lean/Integration/PolarResidual.lean` mirrors
`DASHI/Physics/Closure/SSP369PolarResidualQuotient.agda` and makes its prose
warning a theorem: `polarEquiv` shows the projection is a **bijection**
`FullPhaseCell ≃ PolarPhaseCell ⊕ DepthWheelPhase`, i.e. `9 ≃ 6 + 3`, whose
inverse is the source's `reopen`; `project_preserves_phase` shows the phase
survives on both branches; and `no_retraction_to_polar` shows a genuine `9 → 6`
retraction is impossible.  `polarTransport` adds polarity-equivariance and
`kernelTritHub` adds the lane's `KernelTrit` to the ternary hub.

## 5. Also added: a mechanical provenance census of the Lean mirrors

`scripts/mirror_provenance.py` and `MIRROR_PROVENANCE.md` audit the
hand-transcribed `AgdaMirror` layer at *name* level: 123 (mirror, cited source)
pairs, 116 resolving to a file in this tree, one dangling citation, three
non-aggregate mirrors with no declared source, and 66.0 % of the 1 012 cited
Agda declarations having a same-named Lean counterpart, with per-module lists of
the rest.  This is provenance, not faithfulness — nothing here checks that a
mirrored theorem *states* its Agda original, which needs an Agda toolchain — but
the layer is now enumerable and its gaps visible.

`scripts/mirror_signature_compare.py` and `MIRROR_SIGNATURES.md` take the next
step available without an Agda toolchain: for each name-matched pair they
compare the **arity** (explicitly quantified arguments, ignoring implicit and
instance binders) and the **head connective** of the conclusion.  Of 515
comparable pairs, 495 (96.1 %) agree on both, and the 20 that do not are listed
individually as a review queue; the report also checks that no Agda `postulate`
in a cited source is mirrored under the same name (none is).  Spot checks of the
queue found binder-convention differences, three mirrors that genuinely take an
extra `fuel` argument, two that deliberately strengthen an assumed Agda record
into a constructed Lean object, and one parse artefact.  Shape agreement is
necessary but not sufficient for faithfulness — it rules out gross
mis-transcription of arity and conclusion form, and nothing more.

## 6. Also added: symmetry reduction as a typed obligation

The three corrections above all turn on the same distinction: *which map, at
which layer, preserving which structure*.  `Lean/Integration/SymmetryReduction.lean`
makes that distinction a type.  `EquivariantQuotient G Rich Coarse` bundles a
monoid action on each of two layers, a surjective projection, and the square

    π (g · x) = ḡ · π x ,

with the coarse action as a field, so an instance must exhibit the reduced
action.  It has three inhabitants here: the free C₃ output-phase reduction
`27 → 9` (`phaseReduction`), the polarity/magnitude observer
(`polarReduction`), and one instance with genuinely nontrivial induced action
(`laneReduction`), which rules out the structure being satisfied only by orbit
maps.

The same file states the `support` negative at the right level:
`support_no_equivariant_action` shows there is **no** map on the Boolean layer
at all making the native-chart support observer intertwine the polarity
involution, and `support_not_a_reduction` restates that as "no
`EquivariantQuotient` has `support` as its projection".  The failure is
therefore already at the *unary* symmetry, prior to any binary law — and it is a
property of that observer's choice of origin, since the same action does descend
along the polarity-invariant observer.

## 7. Also added: residual-bearing quotients as one structure

`Integration.Residual.ResidualQuotient` captures "coarse state + retained
residual reopens the rich state" once, with `polarQuotient` (the `9 → 6` polar
projection) and `signQuotient` (the magnitude observer, residual = the sign) as
instances, and `residual_not_subsingleton` as the generic reason the residual is
never removable bookkeeping.

## 8. What is still open

The frontier list in `TOE_GLOBAL_MAP.md` §4 is updated accordingly.  The two
items most relevant to the corrections above:

* **The SSP/Hecke intertwiner** (item 9).  The corpus asks for a commuting
  square `Φ ∘ R_p = T_p ∘ Φ` and records that it is unconstructed.  This pass
  supplies the SSP side of that square (a monoid with functorial transport); the
  representation side has no Lean carrier in this cutset, so the square remains
  open.  It is *not* claimed here in any form.
* **An intermediate descent** (item 3).  The binary law provably does not
  descend to either Boolean observer.  Whether some quotient strictly between
  the ternary algebra and the Boolean mask carries it is open.
