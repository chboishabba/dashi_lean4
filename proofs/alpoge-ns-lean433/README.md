# Original unforced Navier–Stokes admission

Pinned upstream: https://github.com/tristanbuckmaster/navier-stokes/tree/ad53419de079eb8f95f60313473374624a348546
(Alpöge–Buckmaster, 20 November 2026). Lean v4.33.1, Mathlib
0df444a360eaa60ab8c11dca51a86af692955474.

Use the original Solution.lean, NOT the sorry-bearing comparator Challenge.
The upstream README explicitly states the Appendix B certificate data and
external interval-arithmetic verifier have not been released in this
checkout. The patched Lean package was not rebuilt when assembled.
Consequently neither a proof name nor a successful conditional build
constitutes an inhabitant of CellSystemCondition.

## Local acceptance (not CI)

From the DASHI Lean checkout of PR #123:

```sh
python3 proofs/alpoge-ns-lean433/audit_admission_axioms.py --self-test
bash proofs/alpoge-ns-lean433/check_original_admission.sh /path/to/original/checkout
```

Obtain the original upstream checkout independently, with appropriate
permission; no original upstream proof text redistributed here.

The runner verifies original commit, tracked source cleanliness, solution,
challenge, toolchain and package blobs, resolved Mathlib SHA, builds only
Solution, recompiles the original DASHI ClaySpec blob in the same kernel,
and builds the three source-local modules. The final axiom report must
contain all eight specified declarations with only standard axioms.

## Actual source cut

- UnforcedAdmission.lean: original profile and seven dependent cell input
  objects, source solution both space/torus; explicit refutation of original
  positive claims on compact-support and periodic domains.
- ClayDifferentialTransport.lean: exact Mathlib-only extract of existing
  DASHI Gap.lean blob d19d04e4e8db66cf4128d1a063ea6a8b588538df; no comparator
  authority imported. Needed because the original AB toolchain is distinct
  from the OpenAI/LeanDojo terminal toolchain.
- ClayUnforcedTransport.lean: actual time-first transport, derivative
  identities, same velocity/pressure, literal zero forcing, source torus
  nonexistence implies canonical Clay D (even with the erratum), and
  original CellSystemCondition implies Clay D.

OpenAI's independent forced C/D are already on main in
ExternalClayNS/LeanDojoExactTerminal.lean and SubmissionAudit.lean; no
independent similarity-profile producer is a dependency of that route.
Only one accepted literal alternative is needed.

## Verification and remaining

Local Python parser controls 10/10 normal and optimized; local source blob
3d35ad67697e2025c94fd639c54c7ab9a388e4a5 equals committed blob. No Lean/Lake
available here, no kernel replay or CI. New native theorem bodies are
source-written, not kernel accepted. Whole-space original terminal is
consumed locally; its direct canonical Clay C compact-support/energy
transport is not part of this cut and is not a prerequisite to D.
The real original certificate and validated fifteen-condition witness remain
unpaid. No invented profile, certificate, axiom or official recognition.
Original analytic proofs credited to Alpöge–Buckmaster and OpenAI separately;
DASHI only original-source coordinate/statement transport and admission.
