import Integration.F4RootWeylExact
import Mathlib

/-!
# Albert derivation algebra -> F4 recognition boundary

The companion Agda branch now owns an actual rational Albert Jordan algebra
`H_3(O_Q)` and its inner derivations `[L_X,L_Y]`.  Exact rational Python on the
literal 27-coordinate product reports:

* 351 basis-pair inner derivation candidates;
* every candidate satisfies the derivation commutator law on the 27 basis;
* their matrix span has rank 52;
* the standard 21 octonion derivations span rank 14;
* the negative trace form on an independent 52-element derivation basis is
  positive definite (exact LDL diagonal values are only 3/2 and 6);
* the center is zero;
* a generic regular element has centralizer dimension 4.

This file keeps those cross-tool facts separate from the independently owned
F4 root/Weyl datum.  In particular 52 = 4 + 48 is a consistency checksum, not
by itself a same-Lie-algebra theorem.  The remaining recognition theorem must
identify the Albert derivation bracket with a Lie algebra of root datum F4
(after the appropriate scalar extension/form classification).
-/

namespace Integration.F4AlbertDerivationRecognitionBoundary

open Integration.F4RootWeylExact

structure AlbertDerivationProbeReceipt where
  albertCoordinateDimension : Nat
  basisPairCandidates : Nat
  innerDerivationSpanRank : Nat
  octonionDerivationSpanRank : Nat
  traceFormRank : Nat
  regularCentralizerDimension : Nat
  centerDimension : Nat
  allBasisDerivationChecksPassed : Bool
  negativeTraceFormPositiveDefinite : Bool
  deriving Repr

def canonicalAlbertDerivationProbeReceipt : AlbertDerivationProbeReceipt where
  albertCoordinateDimension := 27
  basisPairCandidates := 351
  innerDerivationSpanRank := 52
  octonionDerivationSpanRank := 14
  traceFormRank := 52
  regularCentralizerDimension := 4
  centerDimension := 0
  allBasisDerivationChecksPassed := true
  negativeTraceFormPositiveDefinite := true

theorem f4_dimension_checksum : 4 + Fintype.card (Fin 48) = 52 := by decide

theorem independent_f4_root_datum_paid :
    F4RootWeylExact.canonicalBoundary.root48Paid = true ∧
    F4RootWeylExact.canonicalBoundary.standardCartanPaid = true := by
  decide

inductive AlbertDerivationSameLieAlgebraAsF4Paid : Prop
inductive AlbertAutomorphismGroupIdentifiedWithF4Paid : Prop
inductive RationalFormClassifiedHere : Prop

theorem diagnostics_do_not_manufacture_same_lie_algebra :
    ¬ AlbertDerivationSameLieAlgebraAsF4Paid := by intro h; cases h

theorem diagnostics_do_not_manufacture_full_automorphism_group :
    ¬ AlbertAutomorphismGroupIdentifiedWithF4Paid := by intro h; cases h

theorem split_root_datum_does_not_classify_rational_form :
    ¬ RationalFormClassifiedHere := by intro h; cases h

structure Boundary where
  independentRoot48Paid : Bool
  independentF4CartanPaid : Bool
  independentF4CoxeterActionPaid : Bool
  pythonWeylOrder1152Checked : Bool
  actualRationalAlbertDerivationOperatorOnAgda : Bool
  exactAlbertDerivationRank52Checked : Bool
  exactOctonionDerivationRank14Checked : Bool
  exactTraceFormPositiveDefiniteChecked : Bool
  exactCenterZeroChecked : Bool
  exactRegularCentralizerRank4Checked : Bool
  sameLieAlgebraIntertwinerPaid : Bool
  rationalFormClassificationPaid : Bool
  fullF4AutomorphismRecognitionPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  independentRoot48Paid := true
  independentF4CartanPaid := true
  independentF4CoxeterActionPaid := true
  pythonWeylOrder1152Checked := true
  actualRationalAlbertDerivationOperatorOnAgda := true
  exactAlbertDerivationRank52Checked := true
  exactOctonionDerivationRank14Checked := true
  exactTraceFormPositiveDefiniteChecked := true
  exactCenterZeroChecked := true
  exactRegularCentralizerRank4Checked := true
  sameLieAlgebraIntertwinerPaid := false
  rationalFormClassificationPaid := false
  fullF4AutomorphismRecognitionPaid := false

end Integration.F4AlbertDerivationRecognitionBoundary
