# RH inverse-square shell max-cut design

## Intent

Continue the live RH one-scale Route-A branch from the literal inverse-square window weld.  The immediate goal is to remove all remaining zero-count bookkeeping that is independent of the witness-curvature problem, then connect that result to the existing adverse-budget compiler without manufacturing any unpaid analytic sign.

## Binding route

1. Partition the half-height far carrier `|gamma-t| > t/2` into separate left and right distance charts.  Use literal half-open windows and keep negative ordinates on the existing all-real `Ncount` carrier.
2. Prove the pure numerical summation statement needed by those charts.  Dyadic shell `k` should cost at most a constant multiple of `(log t + k)/(2^k t)`, so the complete raw inverse-square tail is `O(log t/t)`.
3. Expose a single literal producer `ThreeTapInverseSquareTailBound` for `threeTapInverseSquareZeroTailAfter t (t/2)` and wire it into the existing `threeTapRouteAAdverseBudget_le_logOverT` compiler.
4. Keep witness width and compact-alpha curvature logically separate.  Any theorem that uses curvature must consume `ThreeTapUniformCurvatureBound` or a genuinely proved fixed-width determinant compiler; no pointwise-in-`t` width choice may be silently promoted to a uniform constant.
5. After raw-tail compression, normalize the compensation side as an explicit asymptotic comparison against `-(Gamma+Pole)-LocalSlack/2`.  Do not claim a positive floor unless a source theorem proves it.
6. Mid-strip mesh remains downstream of a near-line PASS.  Route B / signed-fifth remains independent.
7. Mirror provenance/status into Agda only; Agda must not pretend to provide the missing real-analysis proofs.

## Success criteria

- Lean contains a focused shell/series module and a Route-A compiler that consumes its result on the exact literal tail carrier.
- The frontier file states precisely which parts are source-written versus still analytic assumptions.
- The selected-three-tap workflow builds every new module.
- Agda PR #1082 records: arbitrary-endpoint literal count paid; inverse-square window paid; all-real/negative unit windows paid; shell/series status; width/curvature status; compensation status; exact-head kernel status; RH false.

## Trust boundary

No RH theorem is asserted from an unpaid inequality.  Exact-head kernel success is claimed only after an exact-head workflow run passes.