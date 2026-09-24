# AdK Exact CV Kernel Mirror Design

Date: 2026-09-17

## Status

Approved architecture. This document records the implementation contract for mirroring the theorem-bearing adenylate-kinase (AdK) geometry/CV spine from `dashi_agda` into `dashi_lean4` so Lean becomes the executable proof elaborator.

## Objective

Replace the current proof-critical Python -> manifest -> Agda witness chain with a minimal native Lean theorem spine:

```text
external/source evidence
  -> Agda attribution ontology
  <-> Lean faithful theorem mirror
  -> Lean kernel/elaboration receipt
```

Python remains optional acquisition tooling. It is not part of the theorem authority chain.

## Existing infrastructure reused

- `AgdaMirror` is the existing Lean mirror aggregation surface.
- `AgdaMirror.AuthorityBoundary` already distinguishes citation authority, artifact authority, and machine-readable evidence.
- Current `main` also contains JMD/meta-introspector's `AgdaCheck`, `AgdaVendor`, vendored `upstream/dashi_agda`, and provenance tooling. These are reused for traceability; the AdK mathematical proof remains native Lean rather than depending on parser/transliterator correctness.
- Lean toolchain is pinned by the repository and CI uses `leanprover/lean-action`.

## Attribution contract

Every theorem-bearing AdK file must preserve this split.

### SOURCE

- Li, Liu, Ji 2015, DOI `10.1016/j.bpj.2015.06.059`: source-facing AdK CV residue/domain roles.
- Prohaska et al., DOI `10.1515/pac-2019-0603`: adopted abridged atomic-mass convention used for the exact reconstruction.
- wwPDB/PDB deposition identity: coordinate-object provenance only.

### DASHI reconstruction

- exact rational carrier for PDB-decimal coordinates;
- exact rational carrier for the adopted rounded masses;
- canonical selected-content representation;
- exact finite mass-weighted center-of-mass function.

### DASHI-original theorems

- canonical selected-content equality implies COM equality;
- equality of the eight source-facing selection packets implies equality of the three-CV input surface;
- constructive projection collision from an unselected-atom perturbation;
- non-factorability / non-reconstruction of the full atomistic configuration through the three-CV projection.

### NOT PROMOTED

None of the following creates theorem or scientific authority:

- DOI/PDB/QID identity;
- Git blob identity;
- SHA-256 equality;
- parser execution;
- Python execution;
- mirror transport;
- numeric floating-point agreement.

## Minimal Lean surface

```text
AgdaMirror/AdK/
  Attribution.lean
  AtomisticConfiguration.lean
  SourceSelections.lean
  CanonicalSelectionContent.lean
  COMGeometry.lean
  CVProjection.lean
  NonFactorability.lean
```

`AgdaMirror.lean` imports the terminal AdK module after the tranche elaborates.

## Exact carriers

PDB Cartesian values are represented in Angstroms as `Rat`/`ℚ`, with source decimal thousandths embedded exactly. Example:

```text
12.345 A -> 12345 / 1000
```

The adopted working masses are likewise exact rationals over the explicitly rounded source convention, e.g. carbon `12.011 -> 12011 / 1000`.

This exact reconstruction is DASHI machinery. It is not a claim that the crystallographic experiment or atomic-weight source is intrinsically exact to those rationals.

## Atomistic carrier

The minimal configuration contains only what the theorem requires:

- stable atom identity;
- model / chain / residue / residue-name / atom-name / altloc / serial / element;
- exact rational Cartesian coordinates;
- attributed exact-rational working mass;
- enough structure to define selection and prove distinct configurations.

Chemical microstate, force-field state, dynamics, water/ligand interpretation, and PDB byte provenance remain outside the mathematical equality used by the CV theorem unless explicitly needed later.

## Source selections

Mirror exactly the source-facing roles already formalised in Agda:

- theta1 LID backbone: 123-155;
- hinge backbone: 161-165;
- CORE backbone: 1-8, 79-85, 104-110, 190-198;
- theta2 NMP backbone: 50-59;
- dLN LID domain: 122-159;
- dLN NMP domain: 30-59.

For theta1/theta2, the backbone role is source-paid.

For dLN, the source pays domain COM roles but does not resolve the exact atom subset. The Lean mirror therefore keeps `dLN` atom-policy choice explicit. Any backbone/heavy implementation is a DASHI evaluator convention and must not be promoted to Li-Liu-Ji source truth.

## Canonical selected content

`CanonicalAtomRow` contains the proof-relevant atom identity, exact rational working mass, and exact rational coordinates.

`CanonicalSelectionContent` is a canonical finite collection/list of rows with ordering normalised independently of source serialization.

The theorem premise is direct content equality, not hash equality:

```text
canonicalContent q1 S = canonicalContent q2 S
```

Hashes may later be retained as audit coordinates but do not participate in proof.

## Exact center of mass

For a non-empty selected finite atom collection with nonzero total mass:

```text
COM(S) = (sum_i m_i * r_i) / (sum_i m_i)
```

The COM function is defined natively over exact rationals.

Because `COM` is a pure function of canonical selected content, content equality implies COM equality by congruence/unfolding; no externally supplied extensionality witness is required.

## Three-CV theorem surface

Do not formalise `acos` merely to prove same-object equality.

Define the exact theorem-bearing CV input surface as the COM tuples required by theta1, theta2, and dLN. Equality of all required canonical selection packets implies equality of those COM tuples.

For dLN, squared distance can be exact if needed:

```text
d2 = dx^2 + dy^2 + dz^2
```

For theta angles, equality of the exact COM triples is sufficient to prove that any deterministic downstream angle evaluator receives equal inputs. Numeric transcendental evaluation remains a separate executable concern.

## Constructive non-injectivity

Construct configurations `q1` and `q2` such that:

- `q1 != q2`;
- they differ only in an atom outside the union of all selections used by the chosen three-CV convention;
- all eight canonical selected-content packets are definitionally/provably equal;
- therefore their three-CV input surfaces are equal.

Compile that collision through the existing/generic factorisation formulation when available; otherwise define the smallest faithful Lean witness that the full configuration cannot factor through the three-CV projection, and later crosswalk it to the shared generic mirror.

## Interop with JMD/meta-introspector machinery

The newly integrated JMD interoperability tooling is attribution/provenance infrastructure, not theorem authority for this tranche.

Where useful, retain:

- source Agda module paths;
- source repository revision/branch coordinates;
- formulation owner labels;
- JMD attribution for the interoperability machinery itself.

Do not reassign Li-Liu-Ji, Prohaska, JMD, or DASHI authorship across these layers.

## Testing and verification

Implementation is TDD-oriented.

1. Add Lean examples/theorems that fail before each production definition where practical.
2. Build the narrow AdK module/root first.
3. Build the aggregate `AgdaMirror` root after integration.
4. Check for `sorry`, declarations of new `axiom`, and unexpected assumptions in the new AdK namespace.
5. Use GitHub CI / Lean elaboration receipt as the authoritative execution evidence.

No claim of kernel GREEN is made until a fresh Lean build/CI reports success.

## Non-goals for this tranche

- full PDB fixed-column parser in Lean;
- OpenMM execution;
- canonical wwPDB byte parity;
- exact `acos`/angle numerics;
- historical force-field reproduction;
- replacing the Agda source/provenance ontology;
- deleting the Python acquisition scripts from `dashi_agda`.

## Success criterion

A Lean CI/elaboration receipt proves, without `sorry` or new axioms in the AdK tranche, that equality of the exact canonical selected-content surface implies equality of the exact three-CV input surface, and exhibits a constructive pair of distinct atomistic configurations with the same projected surface, under the stated source/evaluator conventions and attribution boundaries.
