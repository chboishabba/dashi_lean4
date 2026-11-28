# Yang–Mills A–D Max-Cut Design

## Goal

Advance the live Yang–Mills Lean lane from the current finite-Wilson/reflection infrastructure to the sharp A–D frontier without introducing surrogate carriers or silently strengthening physical assumptions.

## Binding roadmap

### A — literal finite Wilson OS2

Close the pure-Wilson finite reflection-positivity leaf only on the actual boundary-Haar projected kernel. Reuse the literal positive/boundary/negative Haar split, the two periodic crossing slabs, the literal half-holonomy factorization, and continuous exponential crossing-kernel RP. Fixed-boundary positivity is explicitly not an allowed route.

The terminal proposition remains `LiteralSU2BoundaryGaugeProjectionRPExact`. Any new theorem must either prove it outright or isolate the final same-object half-path/Haar pullback equality needed to consume `su2_wilson_crossing_plane_integral_rp`.

### B — complete-action finite reflection positivity

Retain `CMP119ResidualReflectionCut` as the downstream compiler. The physical work is to classify the selected regular-E, R-operation, and boundary-B source polymers by their actual time-plane support, identify one-sided terms with reflected halves, and prove or falsify positivity of each genuine crossing kernel. Vacuum remains the already-proved constant reflected-half factor.

No theorem may infer reflection positivity from smallness alone.

### C — CMP119 literal residual source weld

Use one selected configuration, cutoff, evaluator, periodic polymer/shell carrier, and action throughout. The target is a literal equality identifying the complete residual `E + R + B + V` with the localized/dyadic residual consumed by `CMP119LiteralDyadicResidualWeld`.

The remaining dictionary obligations are component-to-polymer support for E, source-to-periodic carrier identifications for R and B, common shell embedding, source-vacuum evaluator equality, and additive evaluator semantics. Existing dyadic oscillation/localization machinery is downstream and must not be duplicated.

### D — continuum compactness producer

Treat actual tightness/compact containment as the first global analytic wall. Preserve D1/D2 (`isTightMeasureSet_of_uniform_coercive_lintegral_bound` and consumers) and add a D3 projective finite-marginal interface if it can be stated on actual probability measures without claiming a projective-limit theorem not supplied by mathlib/source estimates.

D3 should express:

1. a countable family of finite/smeared marginals;
2. uniform marginal tightness (or a producer sufficient for it);
3. marginal weak subsequential limits;
4. explicit consistency as a separate hypothesis/theorem boundary;
5. a clearly named remaining projective-limit existence obligation rather than pretending it is closed.

Path4 remains only a D producer if compact sublevels are proved in the selected global topology and its expectation is the selected measure integral.

## Non-goals

- Do not claim the Clay mass gap.
- Do not infer complete-action RP from residual smallness.
- Do not replace the literal CMP119/Yang–Mills measures with formally similar surrogates.
- Do not hide unproved source dictionaries inside opaque assumptions with names suggesting closure.
- Do not generalize to every compact simple group until the SU(2) finite/source and continuum producer leaves are explicit.

## Verification

All new Lean files live under `YangMills/` and are built by the existing `YMContinuum` target. New regression files should be imported by the lane and the exact branch workflow should remain the certification surface.