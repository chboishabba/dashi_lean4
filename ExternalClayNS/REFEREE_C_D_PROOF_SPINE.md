# Referee proof spine for Clay alternatives C and D

Pinned source revision:

```text
openai/NavierStokesAndEuler
f9e8bc5b38b6e212696e8a30e3e91517af887bbd
```

Normative target in this branch: `ExternalClayNS/ClaySpec.lean`.

This document is the human-proof audit layer.  It records the exact source
lemma carrying each nontrivial arrow.  A green Lean composition is evidence
that the propositions line up; it is **not** by itself a substitute for
checking the mathematical proofs of the source lemmas named below.

---

# D — periodic forced breakdown

## Target

For every `ν > 0`, exhibit smooth divergence-free periodic initial data and a
smooth periodic force whose every displayed mixed derivative decays faster than
every time power, such that there is no global smooth periodic velocity/pressure
solution.  Pressure periodicity is included, matching the official erratum.

The terminal source theorem is:

```text
NavierStokes.PeriodicPaper.periodic_corollary
```

and the exact Clay route is:

```text
PeriodicPaper.periodic_corollary
  → ComparatorBridge.option_D_of_paper_candidate
  → Comparator.navier_stokes_breakdown_periodic
  → SemanticGap.ComparatorOptionD_to_ClayOptionD
  → DASHILiteralClayNS.literalClayD
  → SubmissionSurface.submissionClayD
```

## D.1 Candidate and viscosity quantifier

Exact source:

```lean
theorem PeriodicPaper.periodic_corollary : breakdownStatement
```

with

```text
breakdownStatement :=
  ∀ ν : ℝ, 0 < ν →
    ∃ u p f K,
      CandidateProperties ν u p f K ∧
      ¬ Nonempty (GlobalSmoothSolution ν f)
```

The proof invokes

```text
NavierStokesR3.theorem_1_1_with_initial_rest ν hν
NavierStokesR3.ParabolicScaling.compressedCandidate
PeriodicPaper.of_compact_candidate
PeriodicPaper.CandidateProperties.no_global_solution
```

Audit question: verify that no intermediate scaling changes the final viscosity,
force, initial datum, or singular time without an explicit inverse bridge.

## D.2 Same Navier–Stokes equation / same force

Candidate-side equation field:

```text
PeriodicPaper.CandidateProperties.navier_stokes
```

states the viscosity-`ν` residual equals the candidate force on
`0 < t < 1`.

The periodization step is:

```text
PeriodicPaper.of_compact_candidate
PeriodicLocalization.navier_stokes_periodize
```

The comparator receives **the same force** through:

```text
ComparatorBridge.option_D_same_force_of_paper_candidate
ComparatorBridge.option_D_of_paper_candidate
```

No viscosity or time rescaling occurs in `PeriodicPaperComparator.lean`.

Referee check: inspect the support-separation hypotheses in
`navier_stokes_periodize` and verify they rule out cross-cell interaction for
the exact differentiated nonlinear term.

## D.3 Smooth periodic initial datum

The paper candidate has

```text
CandidateProperties.zero_initial_velocity
```

so the datum is `u₀ = 0`.

The comparator proof uses

```text
ComparatorBridge.zero_initial_condition
```

which supplies smoothness, divergence-free condition and unit spatial
periodicity.

Referee check: trivial once the comparator definition is confirmed to encode
the official datum conditions without an extra hidden assumption.

## D.4 Smooth periodic force

Source fields:

```text
CandidateProperties.force_smooth
CandidateProperties.force_periodic
CandidateProperties.force_time_support
```

Comparator bridge:

```text
ComparatorBridge.forceConditionPeriodic_of_paper_candidate
```

This invokes

```text
CandidateConsequences.futureJet_decay
```

from smoothness + spatial periodicity + compact future-time support.

Referee check: read `futureJet_decay` and verify it controls every derivative
order required by Fefferman, uniformly in space, rather than only the field
itself or finitely many derivatives.

## D.5 Pressure periodicity

The paper candidate includes

```text
CandidateProperties.pressure_periodic
```

and a hypothetical global solution includes

```text
GlobalSmoothSolution.pressure_periodic
```

The comparator solution predicate also requires pressure periodicity.  The
independent `ClaySpec.ClaySolutionPeriodic` explicitly includes

```text
SpatiallyPeriodic p
```

so the erratum is represented at both ends.

Referee check: ensure no intermediate uniqueness result requires literal
pressure equality rather than equality modulo a spatially constant gauge.
The source maximal-lifespan layer explicitly states that only velocity agreement
is used.

## D.6 Pre-singular uniqueness

Source route:

```text
MaximalLifespan.ClassicalSolution.agree_on_overlap
  → PeriodicUniqueness.classical_uniqueness_on_Icc
```

For every time strictly below the smaller lifespan, both solutions are
restricted to the compact slab and the energy uniqueness theorem identifies
their velocities.

Referee check: inspect `classical_uniqueness_on_Icc` directly.  Confirm its
hypotheses are exactly consequences of smooth periodic classical solutions and
do not smuggle in the desired global regularity assertion.

## D.7 Agreement for every T < 1

Exact theorem:

```text
MaximalLifespan.candidate_agree_on_overlap
```

and, for a solution past time one,

```text
MaximalLifespan.candidate_no_solution_after_one
```

The proof restricts the hypothetical solution to a slab containing `[0,1]`
and uses uniqueness on every pre-one time.

## D.8 Genuine t = 1 obstruction

Candidate property:

```text
SpeedUnboundedAtOne u
```

The contradiction is implemented by

```text
MaximalLifespan.periodic_bound_on_slab
MaximalLifespan.unbounded_excludes_continuous_extension
MaximalLifespan.candidate_no_solution_after_one
```

A smooth global periodic solution is continuous and therefore uniformly bounded
on a compact time slab modulo a fundamental spatial cell.  Pre-one agreement
would transfer this bound to the candidate, contradicting
`SpeedUnboundedAtOne`.

**Critical referee task:** inspect the proof of `SpeedUnboundedAtOne` for the
actual selected/periodized candidate.  This is source-specific and is the main
place where D can still fail mathematically even though every wrapper is closed.

## D stopping criterion

D is Goal-1 complete only after the proofs of these source-specific statements
have been independently checked:

```text
PeriodicPaper.of_compact_candidate
CandidateConsequences.futureJet_decay
PeriodicUniqueness.classical_uniqueness_on_Icc
SpeedUnboundedAtOne for the selected candidate
PeriodicPaper.periodic_corollary
```

If those proofs are sound and match the definitions above, the remaining
source-to-Clay path is already theorem-level bookkeeping.

---

# C — whole-space forced breakdown

## Target

For every `ν > 0`, exhibit smooth divergence-free rapidly decaying initial
data and smooth rapidly space-time decaying forcing for which no global smooth
bounded-energy solution exists.

Terminal source theorem:

```text
NavierStokesR3.theorem_1_1
```

Exact Clay route:

```text
NavierStokesR3.theorem_1_1
  → ComparatorBridge.navier_stokes_breakdown_R3
  → Comparator.navier_stokes_breakdown_R3
  → SemanticGap.ComparatorOptionC_to_ClayOptionC
  → DASHILiteralClayNS.literalClayC
  → SubmissionSurface.submissionClayC
```

## C.1 Exact selected candidate and arbitrary viscosity

Source:

```text
ActualCandidate.selected_candidate_one_with_initial_rest
NavierStokesR3.theorem_1_1_with_initial_rest
NavierStokesR3.theorem_1_1
```

The viscosity-one selected candidate is transformed by the explicit viscosity
scaling in `R3.ViscosityScaling`.

Referee check: trace the same `u,p,f,K` through scaling and into the terminal
nonexistence theorem.  No surrogate candidate is acceptable here.

## C.2 Initial datum

The selected construction is at rest near time zero, so the eventual comparator
datum is `u₀ = 0`.

The comparator bridge supplies:

```text
ComparatorBridge.zero_initial_condition_decay
```

Hence smoothness, divergence freedom and rapid spatial decay are immediate once
the semantic bridge is checked.

## C.3 Smooth rapidly decaying force

The compact candidate carries a compact spatial support witness and smoothness.
The R³ comparator bridge converts this into

```text
Comparator.ForceConditionDecay
```

through the compact-support decay machinery used in
`ComparatorR3Theorem.option_C_of_compact_candidate`.

The independent bridge then proves:

```text
SemanticGap.forceRapidDecayR3_of_comparator
```

which converts the comparator's all-jet decay to the exact
`ClaySpec.ForceRapidDecayR3` mixed-coordinate derivative statement.

Referee check: verify compact support is for the **same scaled force** and that
the all-derivative decay estimate is uniform on the entire nonnegative
space-time half-space.

## C.4 Exact bounded-energy solution class

Independent target:

```text
ClaySpec.BoundedEnergy
```

Comparator-to-independent semantic proof is in `Gap.lean`.

The source comparison layer begins with

```text
ComparatorBridge.GlobalSolutionRn.uniformFiniteEnergy
```

which extracts a uniform finite-energy bound on each compact time interval from
the comparator's global energy condition.

Referee check: verify the direction used is exactly

```text
hypothetical Clay/comparator global bounded-energy solution
  → finite-energy hypotheses required by whole-space uniqueness
```

and not the reverse.

## C.5 Whole-space uniqueness on every T < 1

Exact source call:

```text
NavierStokesR3.WholeSpaceUniqueness.classical_uniqueness_on_Icc
```

inside

```text
ComparatorBridge.compact_candidate_excludes_global_solution
```

Inputs include:

- smooth candidate and competitor on the slab;
- compact spatial support of the candidate;
- uniform finite energy for the competitor;
- divergence-free conditions;
- equality of the two forced NS equations;
- equal initial datum.

Referee check: inspect the uniqueness proof directly and verify no global
existence/regularity theorem is assumed.

## C.6 Terminal obstruction

The comparison theorem obtains equality between the hypothetical global
solution and the compact candidate for every pre-singular time and then applies

```text
R3CompactCandidate.Properties.not_global_agreement
```

through

```text
ComparatorBridge.compact_candidate_excludes_global_solution
```

The source theorem packages this as

```text
¬ Nonempty (GlobalFiniteEnergySolution ν f)
```

in `NavierStokesR3.theorem_1_1`.

**Critical referee task:** inspect the proof of the candidate's terminal
obstruction / unboundedness for the actual selected R³ candidate.  This is the
source-specific mathematical hinge.

## C.7 Circularity audit

The candidate-production chain must not use the target breakdown theorem, the
comparator challenge theorem, or an equivalent axiom.

At the current pinned revision the visible terminal route is:

```text
R3.ActualCandidate
R3.CandidateBreakdown
R3.ViscosityScaling
R3.IntegratedDissipation
  → R3.Theorem
  → ComparatorR3Theorem
  → ComparatorSolution
```

Referee action: inspect imports recursively from
`ActualCandidate.selected_candidate_one_with_initial_rest` and the terminal
obstruction proof, and record every non-Mathlib theorem on which the
construction depends.

## C stopping criterion

C is Goal-1 complete only after independent checking of:

```text
ActualCandidate.selected_candidate_one_with_initial_rest
viscosity scaling of the same candidate
compact support / all-derivative force decay
WholeSpaceUniqueness.classical_uniqueness_on_Icc
the actual candidate terminal obstruction
absence of circular imported assumptions
```

If those survive scrutiny, the exact source-to-`ClayOptionC` semantic route is
already explicit and lossless.

---

# Submission decision rule

No status flag or theorem term should be used as the sole reason to write
“Clay C/D proved.”

For each route, the paper is ready only when every **critical referee task**
above has either:

1. a short complete proof reproduced in the manuscript, or
2. a precise citation to a standard theorem whose hypotheses are checked
   explicitly, or
3. a source-specific lemma whose proof has itself been independently audited
   and included in the provenance record.

This is the Goal-1 boundary.  Reconstructing ordinary analysis in a second proof
assistant is not part of the stopping criterion.
