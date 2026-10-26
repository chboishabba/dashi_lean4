# Millennium submission max-cut checks

`test_millennium_submission_surface.py` is intentionally stricter than the general external-target registry audit. It guards the transition from conditional representation compilers to unconditional exact external theorems.

For Navier--Stokes C, the old opaque statement-equivalence seam has been reduced to five explicit transport leaves: conditions (4) and (5), momentum boundary/coordinate transport, incompressibility boundary/coordinate transport, and energy representation. The exact target must remain fail-closed until all five are inhabited and the final theorem kernel-checks.

For P versus NP, the exact compiler proves that one finite-alphabet LeanDojo language in NP but outside P suffices for the pinned negative branch. This compiler is not itself a P≠NP proof; the actual SAT lower-bound producer and same-object machine-model transport remain required.

Source tests are not evidence of a kernel proof. The Lean workflow and `#print axioms` output are the acceptance evidence.
