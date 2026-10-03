# BSD Kummer/Localization Design

## Goal
Close the finite-level explicit-2-descent to genuine cohomological `Sha[2]` bridge on PR #39 using the literal geometric elliptic curve objects already present.

## Current paid structure
- Actual geometric `E[2]` subgroup and Galois `TopRep`.
- Continuous `H¹(K,E[2])` and square-class comparison on the same coefficient object.
- Genuine degree-one Tate–Shafarevich localization kernel on the elliptic-point representation.
- Exact group-level kernel identity `range(E[2]→E(Kbar)) = ker([2])`.
- Reduction of `[2]`-surjectivity to Mathlib's standard `DivisibleBy` property.

## Immediate closure
Prefer a general theorem: over an algebraically closed field, multiplication by every nonzero natural number on geometric elliptic points is surjective. If the current Mathlib elliptic/scheme API does not support a sound general proof, implement only the `n=2` theorem required for Kummer, but keep the theorem boundary explicit.

Then lift the short exact sequence `0 → E[2] → E(Kbar) →[2] E(Kbar) → 0` to the continuous Galois-module/TopRep setting, construct the continuous-cohomology connecting morphism, and prove localization naturality. Weld the existing square-class/Stoll local conditions to the cohomological local conditions and descend the quotient to obtain the actual explicit cokernel equivalence with genuine `Sha(E)[2]`.

## Non-goals
- Do not replace geometric divisibility with an interface field.
- Do not identify explicit `C₂(E)` with `Sha(E)[2]` before the Kummer/localization square is proved.
- Do not claim the higher Selmer tower or analytic rank equality from this finite-level theorem.
