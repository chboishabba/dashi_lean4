# RH Max-Cut Globalization Design

## Goal

Extend the source-written one-scale three-tap decision surface without adding new representation layers. The implementation must expose the exact remaining analytic inequalities, provide conditional globalization from a near-line PASS to all displacements `0 < a <= 1/2`, formalize the clean trigger for promoting the existing two-scale source after a one-scale FAIL, and keep the signed-fifth route as an independent consumer of the same canonical terminal margin.

## Constraints

- Reuse the existing `QuarticFourSignedPolePair`, adaptive local/far split, paid-cost owner, atomic-to-smooth J2 envelope, two-scale detector, and signed-fifth bridge.
- Do not infer signs not proved on the same transformed object.
- In particular, do not transfer unshifted pole positivity to a translated detector.
- Keep `J4` quarantined until actual smooth `J2 = 0` is proved.
- A near-line PASS is not RH; globalization requires the compact mid-strip `[delta, 1/2]`.
- A one-scale FAIL promotes the existing two-scale operator but does not manufacture a completed two-scale sign theorem.
- Route B remains independent and lands on `canonicalTerminalMargin > 0`.

## Design

### 1. FarExact normal form

Rewrite `threeTapAdaptiveFarExact` using the existing exact off-ordinate half-`tsum` reflection-pair weld:

`FarExact = 1/2 * tsum adaptivePairTerm - LocalExact`.

Then rewrite the paid-cost comparison directly as a signed reflection-pair tail inequality against compensation plus local exact. This is the strongest source-native normal form currently available and identifies the remaining analytic theorem without hiding it behind `FarExact`.

### 2. Globalization consumer

For fixed `t`, witness `W`, tap strength `eps`, and multiplicity `mult`, define the full positive displacement goal as positivity of `threeTapAdaptiveTerminalProfile eps mult a` for every `0 < a <= 1/2`.

Prove a generic interval-gluing theorem: a near-line band `(0, delta)` plus positivity on the compact strip `[delta, 1/2]` implies the full displacement goal. Also expose a uniform mid-strip margin consumer: if `c > 0` and the profile is at least `c` throughout `[delta,1/2]`, then the mid-strip premise follows.

This does not claim the compact minimum exists with a positive value; it creates the exact consumer for the analytic bound.

### 3. One-scale fail -> two-scale promotion

Define a named one-scale resonance failure proposition using strict negativity of the one-scale terminal profile on a right neighbourhood. Prove that either strict paid-cost failure or the balanced-cost positive-J2 branch produces this proposition.

Connect that failure proposition to the already-existing two-scale source by packaging the exact independent prime-2/prime-3 sample theorem at `t >= 300`. The theorem records that promotion is mathematically available without claiming the two-scale completed margin is already paid.

### 4. Signed-fifth direct route

Name the exact eventual signed-fifth analytic hypothesis (boundary control, interior lower bound, and outer-terminal limit) and prove it is sufficient for `CanonicalTerminalPositive`. This is a packaging theorem over the existing signed-fifth bridge, preserving route independence.

### 5. Route union

Provide a final source-level route union theorem: either full three-tap displacement positivity, or the signed-fifth analytic hypothesis, supplies the corresponding terminal positivity consumer. Do not export RH itself unless an existing repository theorem already consumes exactly these hypotheses.

## Verification boundary

All new files must be added to the existing RH selected-three-tap workflow build list. Until an exact-head workflow run exists and passes, report the result as source-written/static rather than kernel-verified.
