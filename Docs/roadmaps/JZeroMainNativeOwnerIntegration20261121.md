# j=0 Eisenstein / GRH P0 — native main-source integration roadmap

**Date:** 2026-11-21  
**Owner:** `chboishabba/dashi_lean4` `main` native source; integration branch `integration/jzero-jacobi-primary-main-weld-20261121`  
**Priority:** universal **GRH P0** original pinned `UpperTheory.EveryCharacter` kernel/admission remains first; this j=0 CM/Hecke is a special-case donor, never a replacement for every Dirichlet character.

## Exact main audit — do not duplicate merged original owners

All following were fetched **on ref `main`** and checked blob-SHA identical to the corresponding older #69 / #73 source branches:

| Original main path | Source lineage | Main blob SHA | Status |
|---|---|---|---|
| `Integration/EisensteinJZeroPrimaryNormalizationExact.lean` | #73 | `c89010ffbec08bd69d76675dad51cf94b1be30f4` | present |
| `Integration/EisensteinJZeroSplitPrimeEisensteinCarrierExact.lean` | #69 | `e7f9ca9ca58127f51fcc4f9f3d17805129816390` | present |
| `Integration/EisensteinJZeroAllGoodPrimeLocalExact.lean` | #69 | `be61019b6a14f69906c7e9a248872ba93db828d3` | present |
| `Integration/EisensteinJZeroSplitPrimeUnitNormalizationExact.lean` | #69 | `f2db9cd400eb6d0ecc4235d7ed6ec7b1ebadc1f3` | present |
| `Integration/EisensteinJZeroPointCMExact.lean` | #73 | `e0dabf8e63fdab3d09923fef516b8b3bec166f9b` | present |
| `Integration/EisensteinSixUnitOrbitExact.lean` | shared | `4101e424044f46f6c2e4fcabcbc4e72c84aec09c` | present |

Main also has the original cubic Jacobi, finite-field, quadratic-algebra, inert Euler and other prerequisites. **Main does NOT yet have** our newer topic-branch `EisensteinJZeroPrimaryRayModulusBidiExact.lean` (#73), `EisensteinJZeroRayModulusLocalCandidateExact.lean` (#69), `EisensteinJZeroRayCongruenceCoordinateCompilerExact.lean` (#69), `EisensteinJZeroSplitPrimeConjugateEulerFactorExact.lean` (#69).

This is the integration failure: recent additions on stale branches are mistaken for source owners absent from the canonical main repository. Main is thousands of commits ahead of each older branch. As observed from GitHub compare at this point, #69 was 10 ahead / 2191 behind main, #73 was 4 ahead / 2251 behind main; do **not** merge stale topic branch wholesale.

## Main-native theorem composition and the small ported NEW ray BIDI (no copied original owners)

New `Integration/EisensteinJZeroMainJacobiPrimaryWeldExact.lean` consumes **two original main owner modules**, plus only the newer, distinct `EisensteinJZeroPrimaryRayModulusBidiExact` (ported byte-identically from #73 onto this main-based branch):

1. #69 `splitJacobiEisensteinElement p (by omega) hmod : EisensteinQA` with actual `splitJacobiEisensteinElement_norm` and `splitPrime_jZero_trace_formula`.
2. #73 `splitPrime_primary_associate_existsUnique` over original `IsJZeroPrimary z := Even z.im ∧ jZeroTrace z ≡ 2 [ZMOD 3]`, with actual six `eisensteinUnits`.

It source-writes:
- `originalJacobi_norm`: exact source `Norm(J_p)=p`;
- `originalJacobi_primary_unit_existsUnique`: **unconditional**, all split rational primes `p>3`, unique original Eisenstein unit carrying THE SOURCE CANONICAL JACOBI ELEMENT to original primary form (no prior cross-branch merge needed);
- `originalJacobi_trace_eq_negative_frobenius`: SAME source `a_p=-Tr(J_p)`;
- `originalJacobi_ray_unit_existsUnique`: **unconditional** all-split-prime existence and uniqueness of a six-unit normalizer with `OneModRay (u * originalJacobi)`; it composes the ORIGINAL main sources with only the new ray BIDI adapter;
- `OriginalSplitTraceModSixTarget`: the genuine all-split-prime finite-field Frobenius congruence `a_p%6=2`, not a new abstract character;
- `jacobi_trace_mod_six_of_original_source`: conditional arithmetic `a_p%6=2 ⇒ Tr(J_p)%6=4`;
- `originalJacobi_negative_ray_one_if_source_trace` and `originalJacobi_only_negative_one_if_source_trace`: if the SAME original curve supplies `a_p≡2 mod6`, its exact canonical Jacobi is uniquely normalized by the specific unit `-1`.

The source-written composition is a real **proof-candidate theorem application** of the original main declarations and the **new ported ray BIDI**. It does NOT claim new mathematical input proving GRH, an *unconditional* selected unit `-1`, the all-primes trace-mod-six premise, or a global ideal character. The newer BIDI module states ray congruence directly in original `EisensteinQA` using the original #73 primary predicate; no duplicate original six-unit theorem is present. Lean kernel and `#print axioms` execution still OPEN; `lean` / `lake` binaries were absent from the execution container; no CI.

## P1 next acceptance order (main-first)

1. **Build main-source closure**: in compatible pinned Lean environment, first `lake env lean Integration/EisensteinJZeroPrimaryRayModulusBidiExact.lean`, then `lake env lean Integration/EisensteinJZeroMainJacobiPrimaryWeldExact.lean`; inspect `#print axioms`. All three added files in this PR are on the same main-derived branch. The repo `lean-toolchain` declares `v4.35.0-rc3`, `lakefile.toml` requests mathlib `v4.28.0`: inspect the effective resolved Lake manifest/toolchain; do not assume they work together.
2. **Kernel-check the now-ported ray BIDI** `EisensteinJZeroPrimaryRayModulusBidiExact.lean` on this same main-derived branch: `IsJZeroPrimary z ↔ z≡1 (mod 2√(-3))` on original norm-p `EisensteinQA`. The new integrator already reuses this module to assert the **source-written unconditional unique ray unit** for the original `J_p`. Do not duplicate original #73 six-unit proof.
3. **Prove finite-field same-curve point-count/torsion lemma**: for all p>3, rational ((-1,0)) order 2 and ((0,1)) order 3 on `y²=x³+1` imply `6 | #E(F_p)`, so for split `p≡1 (mod6)`, `a_p≡2 (mod6)`; with #69 `a_p=-Tr(J_p)`, this selects the unique primary ray unit exactly `-1`. Existing exact finite tests 301/301 primes and 1776 norm-shell checks are only regressions.
4. **Global Hecke** still needs ideals (not just rational primes), generator/ideal multiplicativity, conductor/infinity type, p=2 and p=3 local factors, analytic Euler product and original `L(E,s)=L_K(Ψ,s)` equality.
5. **Universal GRH P0 remains independent and first**: pinned 4.33.1 fork original `EveryCharacter` theorem, all 5 published statements, same-theorem Lean root admission, kernel/axiom and cross-kernel/Agda semantic transport. A selected CM Hecke example does not prove all-character GRH.

## Reuse discipline

- If source is on `main`, import and apply it; do **not** copy #69/#73 files, or infer a missing proof from a stale topic-branch grep.
- Bring only NEW source-written modules forward in small, reviewable, main-derived commits.
- Treat source-written `#print axioms` lines as pending tests until an actual toolchain runs them.
- Update this roadmap and controlling RH/GRH roadmap with exact branch/ref SHA and PASS vs OPEN whenever a gate changes. Do not overwrite concurrent H07 indexed-cube work.
