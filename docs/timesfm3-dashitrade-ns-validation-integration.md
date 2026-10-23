# TimesFM-3 cross-repository integration: dashiTRADE and NS experimental screens

## Inspected source owners
- chboishabba/dashiTRADE README.md and docs/nashi_cross_asset_forensics.md
- chboishabba/dashiTRADE nashi/support.py, nashi/structural.py, nashi/quote_control.py
- chboishabba/dashi_agda #1234 canonical B4 R440 interface, #1233 frontier ledger, #1232 extraction
- chboishabba/dashi_agda DASHI/Physics/Closure/NSOpenAI2026ReleasedActualCandidatePhysicalInputsExact.agda
- chboishabba/dashi_agda #1240 VERID lab world model, #1241 LARES-2 experimental discrimination, #1238 optical/MCG observation

## Architectural decision
TimesFM is a read-only candidate-signal producer. It must not directly call
nashi.policy, create Intent, or bypass support/structural/quote_control gates.
A model forecast/quantile receipt has no automatic trade-execution authority.
Likewise, an empirical numerical screen does not inhabit a theorem proposition.

Flow:
pinned historical/known-future observations
 -> TimesFM forecast + quantiles
 -> timestamped source-bounded candidate receipt
 -> same-clock alignment and leakage/normalization checks
 -> shadow-only Nashi comparison
 -> independent support/structural/quote-governance
 -> experimental validation report (no automatic promotion).

## Minimal candidate receipt contract
- model_id, model_version, model_source_commit, checkpoint_digest, license
- dataset_id, dataset_digest, symbol/variate universe, local/UTC clock, horizon
- as_of_timestamp, input cutoff timestamp, future-known variable whitelist
- feature availability times, sampling cadence, time normalization policy
- normalization-statistics window, patch/mask policy, nonfinite-value policy
- raw point and quantiles (0.1...0.9), quantile crossing flag
- reference numerical fixture digest, forecast runtime, evaluation revision
- provenance of target outcomes and observation/payment timestamps
- policy_mode='shadow', allowed_to_trade=false

## Required falsifiers before a policy experiment
1. Perturb hidden future target values: forecast unchanged, with the same
   available inputs and stateless cache/normalization scope.
2. Perturb *allowed* future-known covariates: forecast MAY change. Distinguish
   deliberately available lookahead from target leakage.
3. Perturb historical-only covariates after cutoff: forecast unchanged.
4. Duplicate and reorder multivariate channels with explicit map: validate
   configured invariance/equivariance, not assumed universal symmetry.
5. Inject out-of-order timestamps, stale quotes, missing intervals, and
   alignment collisions. These must fail closed, not silently bucket.
6. Use distinct train/validation/test chronological spans with embargo/purge
   for overlapping horizons and source timestamps.
7. Test quantile crossings and empirical coverage separately by horizon,
   asset, regime and warning/response class.
8. Paired same-sample benchmark versus persistence, naive seasonal, Nashi
   baseline, and any established linear/statistical controls.
9. Preserve dashiTRADE's cross-asset stop: no runtime-policy reopening until
   dated anchor diversity AND fresh confirmed-collapse or recovering-after-
   warning class lineages exist, or a finer useful same-clock panel is sourced.
10. Any physical NS use requires unit-aware rescaling, solver/reference
    integrity, grid/time refinement, conservation/PDE-residual checks, and
    parameter/source controls; numerical residual != Clay proof.

## Candidate experimental designs
A. dashiTRADE BTC/ES/NQ intraday: use historical targets and genuinely
known-future calendar/venue inputs; record as-of timestamps; shadow compare
against current Nashi output and separate collapse/flatten/recovery cohorts.
B. NS phase-locked packet screen: treat canonical screen parameters as an
empirical fixture, not a theorem input. Forecast finite observables like
energy/enstrophy over held-out simulation trajectories, verify physical
identities with independent numerical diagnostics, and compare to simple
mechanistic extrapolation. Block all promotions from forecast to R440 payment.
C. VERID laboratory: optional read-only forecast as action-conditioned
candidate; retain physical-safety and external observation authority gates.

## Highest-leverage proof obligations
(1) end-to-end observation projection refinement through actual TimesFM
preprocessing, normalization, patch masking, attention and lookahead;
(2) true 32-patch slicing and reconstruction for arbitrary T with padding;
(3) reproducible numerical model/reference agreement;
(4) formal distinction between empirical receipt, calibrated prediction,
policy authorisation, and theorem witness.

This note is a cross-repository plan, not an executed experiment or kernel
verification. No CI is requested or invoked.
