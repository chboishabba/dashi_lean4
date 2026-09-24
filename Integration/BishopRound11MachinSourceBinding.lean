import Integration.BishopVendoredTranscendentalExtraction

/-!
# Exact binding surface for the Agda Round11/Machin route-B source receipt

Agda source owner:

  DASHI.Moonshine.BishopRound11MachinSetoidComplexInstanceExact

The Agda receipt exposes, for a selected Round11 cutset:

* the actual Bishop exponential convergence theorem;
* the concrete signed-factorial sine convergence theorem;
* the concrete signed-factorial cosine convergence theorem;
* the 1/5 Bishop arctangent convergence theorem;
* the 1/239 Bishop arctangent convergence theorem;
* the selected source pi is the actual constructed Bishop Machin real.

This module gives that receipt one exact Lean-facing shape. Supplying one
Round11MachinSourceBinding constructs all lower mirror records and therefore
the route-B primitive real extraction. No further exp/sin/cos/pi semantic
theorem is requested.

This is still a mirror binding, not an Agda elaboration claim: Lean does not
import the Agda module directly.
-/

namespace Integration.BishopRound11MachinSourceBinding

open Integration.BishopVendoredRealEvaluation
open Integration.BishopVendoredOrderConvergenceEvaluation
open Integration.BishopVendoredExponentialSemantics
open Integration.BishopVendoredTrigSemantics
open Integration.BishopVendoredMachinPiSemantics
open Integration.BishopVendoredTranscendentalExtraction
open Integration.MoonshineEisensteinPrimitiveExtraction

noncomputable section

/-- Field-for-field Lean target of the Agda
Round11MachinRouteBSourceReceipt.

The partial-sum families appearing here are the canonical mirrors already
proved equivalent to the corresponding classical Mathlib series. -/
structure Round11MachinSourceBinding
    (A : VendoredArithmeticMirror) where
  expB : RegularRatReal → RegularRatReal
  sinB cosB : RegularRatReal → RegularRatReal

  atanOneFifth : RegularRatReal
  atanOneTwoHundredThirtyNinth : RegularRatReal

  expConverges :
    ∀ x,
      BishopConvergesTo A
        (expPartialSum A x)
        (expB x)

  sinConverges :
    ∀ x,
      BishopConvergesTo A
        (sinePartialSum A x)
        (sinB x)

  cosConverges :
    ∀ x,
      BishopConvergesTo A
        (cosinePartialSum A x)
        (cosB x)

  atanOneFifthConverges :
    BishopConvergesTo A
      (atanPartialSum A bishopOneFifth)
      atanOneFifth

  atanOneTwoHundredThirtyNinthConverges :
    BishopConvergesTo A
      (atanPartialSum A bishopOneTwoHundredThirtyNinth)
      atanOneTwoHundredThirtyNinth

open Round11MachinSourceBinding public

def expMirror
    (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A) :
    VendoredExpLimitMirror A where
  expB := B.expB
  converges := B.expConverges

def trigMirror
    (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A) :
    VendoredTrigLimitMirror A where
  sinB := B.sinB
  cosB := B.cosB
  sinConverges := B.sinConverges
  cosConverges := B.cosConverges

def machinMirror
    (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A) :
    VendoredMachinSourceMirror A where
  atanOneFifth := B.atanOneFifth
  atanOneTwoHundredThirtyNinth := B.atanOneTwoHundredThirtyNinth
  atanOneFifthConverges := B.atanOneFifthConverges
  atanOneTwoHundredThirtyNinthConverges :=
    B.atanOneTwoHundredThirtyNinthConverges

def convergenceMirror
    (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A) :
    VendoredTranscendentalConvergenceMirror A where
  expMirror := expMirror A B
  trigMirror := trigMirror A B
  machinMirror := machinMirror A B

def semanticMirror
    (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A) :
    VendoredTranscendentalMirror A :=
  semanticMirrorFromConvergence A (convergenceMirror A B)

theorem semanticMirror_pi_is_machin
    (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A) :
    (semanticMirror A B).piB =
      machinPiB A (machinMirror A B) := rfl

theorem semanticMirror_pi_eval
    (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A) :
    eval (semanticMirror A B).piB = Real.pi :=
  (semanticMirror A B).eval_pi

def primitiveExtraction
    (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A) :
    PrimitiveRealExtraction
      (bishopSourceReal A (semanticMirror A B)) :=
  Integration.BishopVendoredTranscendentalExtraction.primitiveExtraction
    A (semanticMirror A B)

def primitiveExtractionDirect
    (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A) :
    PrimitiveRealExtraction
      (bishopSourceReal A (semanticMirror A B)) :=
  primitiveExtractionFromConvergence A (convergenceMirror A B)

/-- The compiled primitive extraction is faithful on Bishop setoid classes. -/
def faithfulPrimitiveExtraction
    (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A) :
    FaithfulPrimitiveRealExtraction
      (bishopSourceReal A (semanticMirror A B))
      (primitiveExtraction A B) where
  reflects_equiv := equiv_of_eval_eq

structure Round11MachinBindingBoundary where
  expBindingCompilerOwned : Bool
  trigBindingCompilerOwned : Bool
  machinBindingCompilerOwned : Bool
  totalConvergenceMirrorCompilerOwned : Bool
  classicalSemanticMirrorCompilerOwned : Bool
  machinPiClassicalValueCompilerOwned : Bool
  primitiveExtractionCompilerOwned : Bool
  faithfulSetoidEmbeddingCompilerOwned : Bool

  canonicalLeanBindingInhabited : Bool
  everyAdmissibleBindingUniqueUpToBishopEquivalence : Bool
  actualRound11MachinSourceBindingReplayedFromAgda : Bool

def round11MachinBindingBoundary : Round11MachinBindingBoundary where
  expBindingCompilerOwned := true
  trigBindingCompilerOwned := true
  machinBindingCompilerOwned := true
  totalConvergenceMirrorCompilerOwned := true
  classicalSemanticMirrorCompilerOwned := true
  machinPiClassicalValueCompilerOwned := true
  primitiveExtractionCompilerOwned := true
  faithfulSetoidEmbeddingCompilerOwned := true

  canonicalLeanBindingInhabited := true
  everyAdmissibleBindingUniqueUpToBishopEquivalence := true
  actualRound11MachinSourceBindingReplayedFromAgda := false

end

end Integration.BishopRound11MachinSourceBinding
