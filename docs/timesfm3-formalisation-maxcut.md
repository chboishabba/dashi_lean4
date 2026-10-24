# TimesFM-3 formalisation max-cut (2026-10-23)

Reference: https://github.com/google-research/timesfm
Research: https://www.research.google/blog/timesfm-3-a-zero-shot-foundation-model-for-multivariate-forecasting/

## Implemented (source-written, not kernel-certified)
- Dashi/Forecasting/TimesFM3ObservationExact.lean
- Typed full worlds with target, past-only and future-known variates
- Projection to available observations
- Structural noninterference for predictors factored through that projection
- Temporal/variate attention admissibility predicates
- Future-target masking substitution and independence theorem
- Nine-quantile shape and coherent-predictor *assumption* / consequence

## Interpretation and limits
The no-leakage theorem is parametric over predictors consuming the Observation record.
It does NOT establish that Google's PyTorch/JAX model consumes exactly such a view.
A future-target leak through normalization, patch lookahead, implementation caching
or cross-series attention remains possible until source-to-spec refinement is proved.
The model also does not establish quantile monotonicity: CoherentPredictor explicitly
requires it as a premise. Statistical calibration is not a theorem here.

The provisional patch-roundtrip lemma currently uses an identity-shaped
Fin d → Fin n → Fin 32 representation; it is *not* yet the flatten/unflatten
proof for physical series of length 32*n, and handles no padding.

## Next source-level maximum cut
1. Pin exact upstream commit and inspect src/timesfm3/torch/model.py and utils.
2. Formalize true Fin (32*n) ↔ (Fin n × Fin 32) roundtrip, then explicit
   padding, masks and prefix truncation for arbitrary series length.
3. Prove causal dependency preservation across time-attention and full variate
   attention, including future-known covariate lookahead token construction.
4. Model RevIN running-statistics and its freeze boundary. Check for leakage
   when masked horizon targets/past-only covariates are changed.
5. Bind torch preprocessing, CPM masking, forward pass, and quantile decoder
   to executable fixture comparisons; only then claim reference refinement.
6. Add quantile crossing counterexamples and monotonic projection with a
   soundness proof, plus held-out calibration/coverage tests.
7. Connect benchmark provenance, dataset timestamps, and leakage falsifiers
   to DASHI's evidence and experiment-design machinery.

## Local acceptance (do not invoke CI)
lake env lean Dashi/Forecasting/TimesFM3ObservationExact.lean

No exact-head kernel compilation or reference numerical test run was performed.
