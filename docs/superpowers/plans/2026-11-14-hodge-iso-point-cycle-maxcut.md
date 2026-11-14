# Hodge exact scheme-cycle naturality max-cut (14 Nov 2026)

## Original retained dependencies (merged Lean PR #40)

- MillenniumHodgeRealAlgebraicCycleMultiplicityExact.pointCycle:
  actual AlgebraicGeometry.AlgebraicCycle X ℤ, with actual
  divisor predicate when a point has coheight one.
- MillenniumHodgeCycleIsoPushforwardExact.actualCyclePushforward_iso_apply:
  literal residue-degree-weighted Mathlib pushforward along an
  actual scheme isomorphism reindexes by e.inv on point carriers.
- MillenniumHodgeRulingCycleSwapMaxCutExact already carries
  the exact selected P¹×P¹ factor swap and a DIFFERENCE
  anti-invariance compiler, conditional on actual ruling
  cycles being exchanged.

## New Lean owners (draft, kernel acceptance pending)

Synthesis/MillenniumHodgeActualIsoPointCycleTransportExact.lean

- actualCyclePushforward_iso_pointCycle:
    e_*[x]=[e(x)] for EVERY scheme iso and actual point.
- actualCyclePushforward_iso_pointDifference:
    e_*([x]-[y])=[e(x)]-[e(y)] on actual Mathlib cycles.
- actualIsoSwap_pointDifference_antiInvariant:
    a swap of two scheme points negates their literal
    difference as an actual algebraic cycle.

No new symbolic correspondence object, no new residue
multiplicity axiom, no artificial two-ruling lattice.

## What remains before the requested genuine Hodge weld

1. Locate/construct the actual codimension-one generic points
   of the two P¹×P¹ ruling divisors (not arbitrary rational
   *closed* points with the wrong codimension).
2. Construct their genuine fundamental cycle classes with
   the appropriate coefficient, and prove that actual factor
   swap sends ruling-one generic point/cycle to ruling-two.
3. Use the new actual point/difference transport to
   instantiate P1QRulingCycleExchange; check codimension
   and divisor status. This is cycle-side only.
4. Construct/identify a true cycle-class morphism CH¹→
   H²_sing or H²_deRham on the SAME selected complex variety.
5. Prove cycle class commutes with the actual scheme
   factor swap/proper pushforward; reconcile proper-pushforward
   degree conventions and cohomology grading.
6. For universal Hodge, construct algebraic representatives
   of EVERY rational (p,p) class on arbitrary smooth
   projective complex varieties. The P¹×P¹ regression alone
   does not discharge this far stronger conjecture.

## Acceptance

bash scripts/hodge_iso_point_cycle_local_verify.sh

Runs actual local Lean, imports the exact source module, and
prints axioms for all three theorems. The script fails closed
without lake. PR is draft/source-written until that is run
on the pinned local toolchain.

Do not confuse the above new point-cycle transport with the
still-open singular/de Rham cycle-class map or universal Hodge.
