import Integration.F4RootWeylExact
import Integration.F4AlbertDerivationRecognitionBoundary
import Integration.E8StructuredFullWeylRecognition
import Mathlib

/-!
# F4 / Albert current max-cut

Companion Agda owns the actual rational Albert algebra H_3(O_Q), arbitrary
inner-derivation law, exact signed-basis octonion automorphisms, selected
Moufang triality automorphism, and arbitrary-word closure of the known Albert
automorphism generators.

Exact companion computation on the SAME 27-coordinate Jordan product gives a
52-dimensional perfect centerless inner-derivation algebra.  The negative trace
form is positive definite on an independent 52-basis, a deterministic regular
element has centralizer dimension 4, and complexified adjoint diagnostics expose
48 nonzero one-dimensional root spaces split 24+24 into long/short classes with
length ratio two and a standard F4 Cartan simple system.

This Lean branch independently owns the abstract F4 root datum: 48 roots and the
four simple reflections/Coxeter relations.  What remains is a formal scalar-
extension/root-space intertwiner identifying the concrete Albert derivation Lie
algebra with that F4 datum, then the group-level Aut(J)=F4 statement.  No result
is inferred merely from 52 = 4 + 48.
-/

namespace Integration.F4AlbertCurrentMaxCut

open Integration.F4RootWeylExact
open Integration.F4AlbertDerivationRecognitionBoundary

structure Boundary where
  structuredE8AlreadyPaid : Bool
  abstractF4Root48Paid : Bool
  abstractF4CartanPaid : Bool
  abstractF4CoxeterPaid : Bool
  AlbertJordanAlgebraOnCompanionAgda : Bool
  arbitraryAlbertInnerDerivationLawOnCompanionAgda : Bool
  exactDerivationRank52Diagnostic : Bool
  exactPerfectCenterlessDiagnostic : Bool
  exactTracePositiveDiagnostic : Bool
  regularCentralizerRank4Diagnostic : Bool
  complexified48RootSpacesDiagnostic : Bool
  longShortTwentyFourTwentyFourDiagnostic : Bool
  standardF4CartanOnAlbertDiagnostic : Bool
  formalSameLieAlgebraIntertwinerPaid : Bool
  rationalFormClassificationPaid : Bool
  fullAutAlbertEqualsF4Paid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  structuredE8AlreadyPaid := true
  abstractF4Root48Paid := true
  abstractF4CartanPaid := true
  abstractF4CoxeterPaid := true
  AlbertJordanAlgebraOnCompanionAgda := true
  arbitraryAlbertInnerDerivationLawOnCompanionAgda := true
  exactDerivationRank52Diagnostic := true
  exactPerfectCenterlessDiagnostic := true
  exactTracePositiveDiagnostic := true
  regularCentralizerRank4Diagnostic := true
  complexified48RootSpacesDiagnostic := true
  longShortTwentyFourTwentyFourDiagnostic := true
  standardF4CartanOnAlbertDiagnostic := true
  formalSameLieAlgebraIntertwinerPaid := false
  rationalFormClassificationPaid := false
  fullAutAlbertEqualsF4Paid := false

end Integration.F4AlbertCurrentMaxCut
