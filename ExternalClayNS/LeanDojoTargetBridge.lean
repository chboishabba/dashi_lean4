import LiteralABCD
import Problems.NavierStokes.Millennium

/-!
# LeanDojo target bridge for the literal DASHI Clay C/D terminal

This file is elaborated in the `ExternalClayNS` package with the pinned
LeanMillenniumPrizeProblems source root added to `LEAN_PATH`.

`LiteralABCD` already contains theorem terms for the independent Fefferman C
and D specifications.  Consequently the remaining external-acceptance seam is
not a Navier--Stokes estimate: it is the same-statement identification between
that independently frozen Clay specification and LeanDojo's independently
formalised `FeffermanC` / `FeffermanD` propositions.

The structure below makes precisely that semantic weld proof-relevant.  It does
not replace it by a Boolean receipt and it does not manufacture the equivalence.
Once the two equivalences are supplied, the exact LeanDojo target terms follow
by composition only.
-/

namespace DASHILiteralClayNS

structure LeanDojoCDStatementWeld : Prop where
  c_iff : ClayOptionC ↔ MillenniumNavierStokes.FeffermanC
  d_iff : ClayOptionD ↔ MillenniumNavierStokes.FeffermanD

/-- Exact LeanDojo Fefferman C follows from the existing literal C theorem and
only the proposition-level same-statement weld. -/
theorem leanDojoFeffermanC_of_statementWeld
    (w : LeanDojoCDStatementWeld) :
    MillenniumNavierStokes.FeffermanC :=
  w.c_iff.mp literalClayC

/-- Exact LeanDojo Fefferman D follows from the existing literal D theorem and
only the proposition-level same-statement weld. -/
theorem leanDojoFeffermanD_of_statementWeld
    (w : LeanDojoCDStatementWeld) :
    MillenniumNavierStokes.FeffermanD :=
  w.d_iff.mp literalClayD

/-- One weld pays both independently admissible LeanDojo breakdown targets. -/
theorem leanDojoFeffermanCD_of_statementWeld
    (w : LeanDojoCDStatementWeld) :
    MillenniumNavierStokes.FeffermanC ∧ MillenniumNavierStokes.FeffermanD :=
  ⟨leanDojoFeffermanC_of_statementWeld w,
    leanDojoFeffermanD_of_statementWeld w⟩

#print axioms leanDojoFeffermanC_of_statementWeld
#print axioms leanDojoFeffermanD_of_statementWeld
#print axioms leanDojoFeffermanCD_of_statementWeld

end DASHILiteralClayNS
