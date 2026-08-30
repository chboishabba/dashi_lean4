# Aristotle Lean mirror worker brief

Wave: `wave1`
Lane: `analysis`
Claim: Mirror selected missing constructive analysis leaf surfaces.

## Task

Mirror the assigned Agda surfaces into the Lean4 baseline. Work only on the
assigned lane. Preserve existing Lean namespaces and reuse existing mirrored
definitions instead of duplicating them.

Assigned Agda targets:

- `DASHI/Analysis/CanonicalRationalMetric.agda`
- `DASHI/Analysis/ConcreteComplex.agda`
- `DASHI/Analysis/ConstructiveIntermediateValue.agda`


## Required honesty boundary

- Agda `postulate`s become explicit Lean hypotheses or structure fields.
- Do not add `sorry`, `admit`, Lean `axiom`, or fake `rfl` witnesses.
- Preserve all authority boundaries and keep Clay promotion flags false.
- Do not claim an Agda theorem is proved merely because a Lean interface was
  transcribed.

## Required result

Add or update only lane-owned files under `lean-baseline/`. Run
`cd lean-baseline && lake build`, report the exact command and result, list changed files, and list any remaining imported
hypotheses or blocked theorem surfaces.
