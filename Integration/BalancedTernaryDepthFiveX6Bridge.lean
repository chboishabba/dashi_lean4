import Integration.BalancedTernarySparseKernel
import Integration.HeisenbergX6AppraisalSlice
import Integration.TernaryHub
import Mathlib

/-!
# Depth-five residual: X6 + four-trit cardinal bridge

Arithmetic / carrier-count mirror of the Agda bridge.

The sparse kernel gives

  196830 = 3^5 * 810
  810 = 3^6 + 3^4.

The existing Lean X6 carrier has 729 = 3^6 states.  Lean does not yet have the
Agda fixed-rank ternary hierarchy, so this file introduces only the literal
four-trit carrier SSPTrit^4, whose cardinality is 81 = 3^4.

This is a cardinality bridge only.  No residual/coproduct equivalence or
semantic RH/Monster identification is claimed.
-/

namespace Integration.BalancedTernaryDepthFiveX6Bridge

open Integration.TernaryHub
open Integration.BalancedTernarySparseKernel
open Integration.HeisenbergX6AppraisalSlice

structure T4Carrier where
  d3 : SSPTrit
  d2 : SSPTrit
  d1 : SSPTrit
  d0 : SSPTrit
  deriving DecidableEq, Repr, Fintype

theorem t4_state_count :
    Fintype.card T4Carrier = 81 := by
  decide

def zeroT4 : T4Carrier :=
  ⟨.zero, .zero, .zero, .zero⟩

abbrev PuncturedT4Carrier :=
  {x : T4Carrier // x ≠ zeroT4}

theorem punctured_t4_state_count :
    Fintype.card PuncturedT4Carrier = 80 := by
  native_decide

theorem pole_coefficient_matches_punctured_t4 :
    (80 : Nat) = Fintype.card PuncturedT4Carrier := by
  simpa using punctured_t4_state_count.sym

theorem full_t4_is_punctured_plus_origin :
    Fintype.card T4Carrier =
      Fintype.card PuncturedT4Carrier + 1 := by
  norm_num [t4_state_count, punctured_t4_state_count]

def punctureT4 (x : T4Carrier) : Option PuncturedT4Carrier :=
  if h : x = zeroT4 then
    none
  else
    some ⟨x, h⟩

def reopenPuncturedT4 : PuncturedT4Carrier → T4Carrier :=
  Subtype.val

theorem puncture_reopens_nonzero (x : PuncturedT4Carrier) :
    punctureT4 (reopenPuncturedT4 x) = some x := by
  unfold punctureT4 reopenPuncturedT4
  split
  · rename_i h
    exact False.elim (x.property h)
  · rename_i h
    apply congrArg some
    exact Subtype.ext rfl

theorem puncture_zero :
    punctureT4 zeroT4 = none := by
  simp [punctureT4]

theorem depth_five_residual_is_x6_plus_puncture_plus_origin :
    depthFiveResidualCount =
      Fintype.card X6 + Fintype.card PuncturedT4Carrier + 1 := by
  norm_num [depthFiveResidualCount, x6_state_count, punctured_t4_state_count]

theorem bulk_factors_through_x6_puncture_origin :
    (196830 : Nat) =
      3^5 *
        (Fintype.card X6 + Fintype.card PuncturedT4Carrier + 1) := by
  norm_num [x6_state_count, punctured_t4_state_count]

theorem x6_state_count_again :
    Fintype.card X6 = 729 :=
  x6_state_count

def depthFiveResidualCount : Nat :=
  3^6 + 3^4

theorem depth_five_residual_is_810 :
    depthFiveResidualCount = 810 := by
  norm_num [depthFiveResidualCount]

theorem depth_five_residual_is_x6_plus_t4 :
    depthFiveResidualCount =
      Fintype.card X6 + Fintype.card T4Carrier := by
  norm_num [depthFiveResidualCount, x6_state_count, t4_state_count]

theorem bulk_factors_through_x6_plus_t4 :
    (196830 : Nat) =
      3^5 * (Fintype.card X6 + Fintype.card T4Carrier) := by
  norm_num [x6_state_count, t4_state_count]

inductive CardinalitySplitCreatesCoproductEquiv : Prop
inductive ResidualIsHeisenbergPlusT4SemanticCarrier : Prop

theorem count_split_does_not_create_coproduct_equiv :
    ¬ CardinalitySplitCreatesCoproductEquiv := by
  intro h
  cases h

theorem count_split_does_not_create_semantic_identity :
    ¬ ResidualIsHeisenbergPlusT4SemanticCarrier := by
  intro h
  cases h

structure Boundary where
  x6Count729Reused : Bool
  literalFourTritCount81Owned : Bool
  literalPuncturedFourTritCount80Owned : Bool
  poleCoefficientMatchesPuncturedFourTrit : Bool
  partialPunctureReopenMapOwned : Bool
  residual810Equals729Plus81 : Bool
  residual810Equals729Plus80PlusOrigin : Bool
  bulk196830FactorsThroughCountSplit : Bool
  concreteCoproductEquivConstructed : Bool
  semanticCarrierIdentityClaimed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  x6Count729Reused := true
  literalFourTritCount81Owned := true
  literalPuncturedFourTritCount80Owned := true
  poleCoefficientMatchesPuncturedFourTrit := true
  partialPunctureReopenMapOwned := true
  residual810Equals729Plus81 := true
  residual810Equals729Plus80PlusOrigin := true
  bulk196830FactorsThroughCountSplit := true
  concreteCoproductEquivConstructed := false
  semanticCarrierIdentityClaimed := false

end Integration.BalancedTernaryDepthFiveX6Bridge
