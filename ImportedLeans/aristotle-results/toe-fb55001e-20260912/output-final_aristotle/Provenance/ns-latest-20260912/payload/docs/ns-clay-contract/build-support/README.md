# Build-support shim (not part of any proof)

The bundle's Agda sources import `Data.Rational.Tactic.RingSolver` in 1 320
files.  That module exists in no released agda-stdlib (2.1, 2.2 and 2.3 ship
only the `Data.Nat` and `Data.Integer` ring solvers) and the bundle does not
ship its own copy, so nothing here can be typechecked without supplying it.

`Data/Rational/Tactic/RingSolver.agda` in this directory reconstructs the
module from the generic `Tactic.RingSolver` over
`Data.Rational.Properties.+-*-commutativeRing`.  It is recorded here purely so
that the audit in `../closure-audit.md` is reproducible.  It is *not* on the
project's own source path and contributes no mathematical content.

Reproduce with, for example,

    agda --no-libraries -i. -i<agda-stdlib>/src \
         -idocs/ns-clay-contract/build-support <file>.agda
