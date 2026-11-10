# Kakeya 3D: exact external proof reuse and maximum cut (2026-11-10)

## Primary mathematical attribution

- Hong Wang and Joshua Zahl, *Volume estimates for unions of convex sets, and the Kakeya set conjecture in three dimensions* (2025), https://arxiv.org/abs/2502.17655.
- Larry Guth, Hong Wang and Joshua Zahl, *A streamlined proof of the Kakeya set conjecture in R3* (2026), https://arxiv.org/abs/2601.14411.
- Classical finite Cauchy--Schwarz: Augustin-Louis Cauchy and Hermann Amandus Schwarz.
- Geometric Kakeya concentration, graininess, and multiscale contributions retain their original authors' attribution.

## Verified source inventory (not a local kernel check)

Main development: https://github.com/project-numina/kakeya-3d
Proof path: https://github.com/project-numina/kakeya-3d/blob/main/PROOF-PATH.md
Attribution: https://github.com/project-numina/kakeya-3d/blob/main/ATTRIBUTION.md
Upstream sticky result: https://github.com/M32026/3d-sticky-kakeya

Exact upstream pin: `42f739b484fd055e0aa29601c35677ad996f2ef2`
Lean toolchain: `leanprover/lean4:v4.32.0-rc1`
Lean compiler hash: `b4812ae53eea93439ad5dce5a5c26591c31cb697`
Mathlib commit: `1b0782d8191b03e0001caac10e1601d17f2cd580`
Numina manifest SHA-256: `67bbc3bdc4691e6e36325c7688e5d71dbbcf3f685e87bd94b059eb4d725f39f6`

Reviewed Numina source checkout commit: `a26427e3c2fcaf9f98694fbd0d4dd49e41dcf5e3` (read via GitHub and checked for the referenced proof-path/bridge-lock files). The local launcher rejects all other Numina commits rather than treating moving HEAD as reproducible evidence.\n\nThese identifiers are transcribed from the external bridge-lock. The current Numina HEAD must be captured separately when running a check; no unverified HEAD is represented as pinned here.

### Exact external proof cut

1. `StickyKakeya.StickyFrostmanHypothesis` (GWZ 7.3(A) as input).
2. `StickyKakeya.stickyKatzTaoEstimate_of_stickyFrostmanEstimate`.
3. `Kakeya.KatzTaoEstimate.frostmanEstimate`.
4. `Kakeya.KatzTaoEstimate.katzTaoEstimate_sub_of_frostmanEstimate`.
5. `Kakeya.katzTaoEstimateDimensionThree`.
6. `KakeyaEstimateDimensionThree_pos`.
7. `dimH_ge_three_of_kakeyaEstimate`.
8. `KakeyaDimensionThree` (conditional endpoint).
9. `Kakeya.Assouad.PureWZ2Theorem5_2Unconditional` (Nankai/ByteDance input).
10. `stickyFrostmanHypothesis_of_pureWZ2` (bridge).
11. `Unconditional.KakeyaDimensionThree : KakeyaSetConjecture 3`.

The linked endpoint's documented axiom audit is exactly `[propext, Classical.choice, Quot.sound]`. This is a statement about the pinned external project's reported verification procedure, **not** a successful local build in DASHI.

## Local Lean cut

`DashiKakeya/FiniteIncidence.lean` implements finite rational cell/tube incidence double-counting using Mathlib's finite-sum commutation. It does not redefine the Kakeya theorem, vendor external sources, or assert new axioms.

`lake build DashiKakeya` is an opt-in local check to run in the existing pinned Nix environment. This check has NOT run in the current interaction. The repository toolchain is `v4.35.0-rc3`, but its Lake Mathlib requirement is `v4.28.0`; inspect/reconcile existing project pins before claiming a checked build.

## Why the same original geometric object is not yet obtained from finite incidence

The Agda `NSTriadKNRationalOrderedFiniteL2` Gram proof handles pairs of rationals `(a_c,b_c)`, giving `(sum a_c b_c)^2 ≤ (sum a_c²)(sum b_c²)`. For a genuine weighted cell partition with cell volume `v_c` and multiplicity `m_c`, the intended choice is `a_c = sqrt(v_c)`, `b_c = sqrt(v_c) m_c`. An arbitrary rational `v_c` need not have a rational square root. Therefore either select rational-square cell volumes with explicit witnesses or use a real/ENNReal/measure carrier and prove the corresponding finite Cauchy--Schwarz lemma there. This is a *semantic correspondence gate*, not a missing rational algebraic identity.

## Exact next unpaid gates

| Gate | Task | Proven status |
| --- | --- | --- |
| L0 | Kernel-check DashiKakeya finite incidence against actual Lake/Mathlib pin | Not run |
| L1 | Prove finite original tube-cell membership and volume correspondence | Open |
| L2 | Establish measure-theoretic second moment and overlaps in Mathlib | Open |
| L3 | Pin Numina HEAD, check hash/pins, fetch licensed external sources in isolated Nix environment | Open |
| L4 | Run `python3 verification/check.py --scope full --jobs 2 --require-clean` in external Kakeya repository | Not run |
| L5 | Verify external unconditional endpoint type, exact axiom list and independent Mathlib comparator | Open locally |
| L6 | Export the verified theorem identity and theorem-type receipt without claiming Agda internalisation | Open |
| L7 | Translate/import selected theorems into Agda only when necessary, retaining source and mathematical attribution | Open |
| L8 | Investigate claimed stronger maximal-function and 4D results as separate proof obligations | Open |

Do not change the external repository's theorem statements or claim a theorem has been proved by DASHI solely because it exists in a different formal system. Distinguish external proof verification, a trusted exported receipt, and internal Agda kernel proof. Do not vendor upstream code or libraries. Do not use CI as the only proof evidence.

## No-CI local verification entrypoint (2026-11-10)

The repository now has `scripts/verify_external_kakeya.py`. It checks an
**existing clean** local Project Numina checkout against the official pinned
bridge-lock (including Mathlib manifest hash, Lean toolchain, and sticky source
commit) and only then delegates to the upstream official verification suite.

From the dashi_lean4 checkout, use:

```sh
python3 scripts/verify_external_kakeya.py /absolute/path/to/kakeya-3d \
  --receipt /absolute/path/to/kakeya-preflight.json
python3 scripts/verify_external_kakeya.py /absolute/path/to/kakeya-3d \
  --execute --jobs 2 \
  --receipt /absolute/path/to/kakeya-full-run.json
```

Prepare the external checkout using **its own** instructions, including
`lake exe cache get` and
`git submodule update --init upstream/3d-sticky-kakeya`.
Do not vendor these sources or mutate the main DASHI Lean toolchain.
The official suite writes detailed stage logs and receipts under its own
`.verification-results/`; the launcher receipt alone is only status routing.

This wrapper has **not** executed a full proof build in this conversation.
Lean, Lake, Agda and Nix are unavailable in the current runtime, and network
git is unavailable. The script source and the negative preflight path were
checked with local Python tooling; that is not a successful proof receipt.
A successful `preflight_pass` is not equivalent to `verification_pass`.

The external project's full verification documentation is
https://github.com/project-numina/kakeya-3d/blob/main/RELEASING.md .
