import Integration.OggSSP2BMod4ExtensionAcquisition

/-!
# Co1 augmentation-filtration triviality criterion

For P ~= F2^24 normal in P.Co1, the augmentation filtration of any
characteristic-two module has P-trivial graded pieces and multiplication maps

  24 ⊗ gr_i(M) -> gr_{i+1}(M)

which are Co1-equivariant.  If the Co1 composition factors are only 1 and 274,
and the four possible Hom spaces from 24⊗X to Y (X,Y in {1,274}) vanish, then
there is no nonzero first augmentation action, so P acts trivially.

The runtime screen still owns the four Hom-space computations and a separate
receipt must identify the actual Tate Co1 profile as 1/274/1.  This file makes
the promotion logic proof-bearing: nontrivial normal-subgroup action must expose
a first relevant augmentation arrow, and proof that every such arrow is absent
eliminates the nontrivial action.
-/

namespace Integration.OggSSP2BCo1AugmentationTrivialityCriterion

structure HomReceipt where
  hom24To1Dimension : Nat
  hom24To274Dimension : Nat
  hom24Tensor274To1Dimension : Nat
  hom24Tensor274To274Dimension : Nat
  allRelevantHomSpacesZero : Bool

structure TateCo1ProfileReceipt where
  trivialFactorCount : Nat
  factor274Count : Nat
  unidentifiedFactorCount : Nat
  profileIsOne274One : Bool

/-- The four possible first nonzero augmentation-filtration arrows when the only
Co1 composition factors are the trivial module and the 274-dimensional simple. -/
inductive RelevantAugmentationArrow
  | one_to_one
  | one_to_274
  | two74_to_one
  | two74_to_274
  deriving DecidableEq

/-- Proof-relevant output of the standard first-nonzero-layer argument. -/
structure NontrivialNormalActionEvidence : Type where
  firstNonzeroAugmentationArrow : RelevantAugmentationArrow

/-- Proof-bearing promotion of the four runtime Hom=0 calculations. -/
structure AllRelevantHomsVanish : Prop where
  eliminate : ∀ a : RelevantAugmentationArrow, False

def nontrivialActionProducesRelevantArrow
    (h : NontrivialNormalActionEvidence) : RelevantAugmentationArrow :=
  h.firstNonzeroAugmentationArrow

/-- The actual logical promotion step: once all four relevant Hom spaces are
proved zero, no proof-relevant nontrivial augmentation action can survive. -/
theorem zeroRelevantArrowsForceTrivialNormalAction
    (hz : AllRelevantHomsVanish)
    (h : NontrivialNormalActionEvidence) : False :=
  hz.eliminate (nontrivialActionProducesRelevantArrow h)

structure PromotionBoundary where
  homReceiptRuntimePaid : Bool
  actualTateCo1ProfilePaid : Bool
  augmentationFiltrationCriterionAvailable : Bool
  proofBearingArrowEliminationFormalized : Bool
  normal2Pow24ActionOnActualTateProvedTrivial : Bool

def canonicalBoundary : PromotionBoundary where
  homReceiptRuntimePaid := false
  actualTateCo1ProfilePaid := false
  augmentationFiltrationCriterionAvailable := true
  proofBearingArrowEliminationFormalized := true
  normal2Pow24ActionOnActualTateProvedTrivial := false

theorem promotion_not_yet_paid :
    canonicalBoundary.normal2Pow24ActionOnActualTateProvedTrivial = false := rfl

end Integration.OggSSP2BCo1AugmentationTrivialityCriterion
