# Navier–Stokes Goal-1 submission audit

This directory separates the **Clay-facing mathematical claim** from the
stronger project goal of reconstructing every analytic primitive inside DASHI.

The independent normative statement is `ClaySpec.lean`.  The source proof is
imported only through the pinned revision of
`openai/NavierStokesAndEuler@f9e8bc5b38b6e212696e8a30e3e91517af887bbd`.

## Current exact theorem routes

### Alternative D

```text
NavierStokes.PeriodicPaper.periodic_corollary
        ↓
NavierStokes.ComparatorBridge.option_D_of_paper_candidate
        ↓
NavierStokes.Comparator.navier_stokes_breakdown_periodic
        ↓
SemanticGap.ComparatorOptionD_to_ClayOptionD
        ↓
DASHILiteralClayNS.literalClayD
        ↓
DASHILiteralClayNS.SubmissionSurface.submissionClayD
```

The fixed-viscosity submission package records, for every `ν > 0`:

- smooth divergence-free periodic initial velocity;
- smooth periodic forcing;
- rapid time decay of every required space/time derivative of the forcing;
- the periodic pressure requirement from the official erratum;
- exclusion of every global smooth periodic solution for the same data.

The source-side nonexistence spine is:

```text
PeriodicPaper.CandidateProperties
  → PeriodicPaper.CandidateProperties.no_global_solution
  → PeriodicViscosity.excludes_global_solution
  → periodic uniqueness on every compact pre-singular interval
  → agreement with the candidate
  → SpeedUnboundedAtOne
  → contradiction with a continuous periodic extension through t = 1.
```

### Alternative C

```text
NavierStokesR3.theorem_1_1
        ↓
NavierStokes.ComparatorBridge.navier_stokes_breakdown_R3
        ↓
NavierStokes.Comparator.navier_stokes_breakdown_R3
        ↓
SemanticGap.ComparatorOptionC_to_ClayOptionC
        ↓
DASHILiteralClayNS.literalClayC
        ↓
DASHILiteralClayNS.SubmissionSurface.submissionClayC
```

The fixed-viscosity submission package records, for every `ν > 0`:

- smooth divergence-free rapidly decaying initial velocity;
- smooth rapidly space-time decaying forcing;
- the exact bounded-energy solution class from the independent Clay
  specification;
- exclusion of every global smooth bounded-energy solution for the same data.

The source-side nonexistence spine is:

```text
NavierStokesR3.ActualCandidate.selected_candidate_one_with_initial_rest
  → viscosity scaling
  → NavierStokesR3.theorem_1_1
  → R3 whole-space finite-energy comparison
  → classical uniqueness on every compact pre-singular interval
  → agreement with the compact candidate
  → terminal obstruction
  → contradiction.
```

## What still has to be checked before submission

Lean composition is an audit receipt, not a substitute for mathematical
refereeing.  A submission should not claim C or D solely because these theorem
terms typecheck.  The source-specific argument must be independently read at
the following attack points.

### D hostile-referee checklist

1. The candidate fields solve the same forced Navier–Stokes equations for every
   `0 < t < 1`, with exactly the viscosity and forcing later used by the
   comparator.
2. Spatial periodization introduces no cross-cell terms or support overlap in
   the PDE calculation.
3. The force is genuinely smooth and periodic on the required half-space.
4. Compact future-time support really implies the stated decay of **every**
   mixed derivative, uniformly in space.
5. The pressure is periodic, not merely periodic modulo a time-dependent gauge.
6. The periodic uniqueness theorem assumes no stronger regularity or hidden
   normalization than the official solution class.
7. Agreement on every compact interval `[0,T]`, `T<1`, is enough for the
   `t=1` contradiction.
8. `SpeedUnboundedAtOne` is proved for the same candidate, not a surrogate or
   rescaled object.
9. The positive-viscosity scaling preserves the exact official quantifier order
   and singular time claimed in the final statement.

### C hostile-referee checklist

1. The selected whole-space candidate is the same object used in the terminal
   nonexistence theorem.
2. Viscosity scaling preserves the exact data, smoothness and decay hypotheses.
3. Initial data and force satisfy the independent Fefferman decay predicates,
   not a weaker compact-support proxy with an unproved bridge.
4. The comparator bounded-energy predicate and `ClaySpec.BoundedEnergy` are
   genuinely equivalent in the direction used by the contradiction.
5. Whole-space uniqueness applies to the competitor on every compact
   pre-singular interval with exactly the available finite-energy assumptions.
6. The compact support assumptions used in the comparison are proved for the
   same candidate.
7. The terminal obstruction rules out a global smooth bounded-energy solution,
   rather than only a particular continuation or pressure gauge.
8. No theorem in the candidate-production chain assumes the desired breakdown
   conclusion or an equivalent external axiom.

## Build-time trust receipt

`ProvenanceAudit.lean` and `SubmissionSurface.lean` print the axioms of the
upstream source endpoints and final Clay endpoints.  A clean build receipt
should be archived with the submission materials.  Any non-foundational axiom
appearing there is a mandatory provenance item to explain before publication.

## A and B

A and B remain independent proof-production lanes and are **not prerequisites**
for submitting a valid C or D proof if either source-backed route survives the
audit above.

- A: finish the physical resolvent/projected-Gram same-object identification and
  the physical-state-to-finite-energy convolution majorant.
- B: finish B1/B7 exact welds and the genuine analytic estimates B2/B3/B4,
  especially the strict critical operator bound `θ < 1`.

These routes should continue as independent corroborating mathematics, but they
must not delay a complete C/D manuscript.
