import Integration.ConstructiveRealToStandardReal

/-!
# Moonshine compatibility adapter for constructive-real transport

Moonshine does not own a second real-extraction semantics.  It consumes the
repository-wide contract from `Integration.ConstructiveRealToStandardReal`.

This module intentionally contains only aliases and boundary receipts so older
application-facing imports can depend on a Moonshine-named surface without
forking the transport law.
-/

namespace Synthesis.MoonshineConstructiveRealAdapter

abbrev SetoidRealCore :=
  Integration.ConstructiveRealToStandardReal.SetoidRealCore

abbrev SetoidRealTranscendental :=
  Integration.ConstructiveRealToStandardReal.SetoidRealTranscendental

abbrev StandardRealTranscendental :=
  Integration.ConstructiveRealToStandardReal.StandardRealTranscendental

abbrev StandardRealInterpretation :=
  Integration.ConstructiveRealToStandardReal.StandardRealInterpretation

abbrev FaithfulStandardRealInterpretation :=
  Integration.ConstructiveRealToStandardReal.FaithfulStandardRealInterpretation

abbrev StandardComplex :=
  Integration.ConstructiveRealToStandardReal.StandardComplex

abbrev ConstructiveRealToStandardRealBoundary :=
  Integration.ConstructiveRealToStandardReal.ConstructiveRealToStandardRealBoundary

def constructiveRealBoundary : ConstructiveRealToStandardRealBoundary :=
  Integration.ConstructiveRealToStandardReal.canonicalBoundary

theorem setoidRespect_is_primitive :
    constructiveRealBoundary.setoidRespectRequired = true := rfl

theorem rawRepresentativeInjectivity_is_not_required :
    constructiveRealBoundary.rawRepresentativeInjectivityRequired = false := rfl

theorem faithfulness_is_separate :
    constructiveRealBoundary.faithfulnessSeparatedFromTransport = true := rfl

end Synthesis.MoonshineConstructiveRealAdapter
