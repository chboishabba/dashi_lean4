import Integration.OggSSP2BActualFiveLengthNoGo

/-!
# Constructive five-slice decomposition inside the actual weight-two 2B Tate multiplicity

The Carnahan--Urano 4A(2B) decomposition gives 276 copies of the A-family at
weight two, and each A-copy contributes one ordinary Hhat0(C2,-) class.
Therefore the source-derived weight-two Tate multiplicity has length 276.

This file shows constructively that one may choose five DISJOINT groups of
copy-indices with sizes (3,3,2,1,1), leaving 266 source A-copies.

This is the strongest honest "make the five modules" statement available from
the published multiplicity theorem alone: after choosing an enumeration of the
276 identical A summands, the five requested lengths can be realized as direct
sums of A-copy Tate classes.  The choice is noncanonical and carries NO
published identification with the five binary-tetrahedral inertia sectors.
That geometric identification remains extra data.
-/

namespace Integration.OggSSP2BActualFiveSlices

namespace M := Integration.OggSSP2B4AActualIntegralMultiplicities
namespace T := Integration.OggSSP2BActualRestrictedTate

inductive FiveSlice
  | identity
  | minusOne
  | orderFour
  | orderThree
  | orderSix
  deriving DecidableEq, Repr, Fintype

/-- An explicit partition of the first ten of the 276 actual A-copy indices. -/
def sliceOfWeightTwoAIndex (i : Fin 276) : Option FiveSlice :=
  if i.val < 3 then some .identity
  else if i.val < 6 then some .minusOne
  else if i.val < 8 then some .orderFour
  else if i.val < 9 then some .orderThree
  else if i.val < 10 then some .orderSix
  else none

def sliceCard (s : FiveSlice) : ℕ :=
  ((Finset.univ : Finset (Fin 276)).filter
    (fun i => sliceOfWeightTwoAIndex i = some s)).card

def residualCard : ℕ :=
  ((Finset.univ : Finset (Fin 276)).filter
    (fun i => sliceOfWeightTwoAIndex i = none)).card

theorem source_weightTwo_A_count_is_276 :
    M.weightTwo.a = 276 := by
  decide

theorem actual_weightTwo_H0_length_is_276 :
    T.gradeH0Length M.weightTwo = 276 := by
  exact (T.weight_two_ordinary_tate_lengths).1

theorem explicit_five_slice_cards :
    sliceCard .identity = 3 ∧
    sliceCard .minusOne = 3 ∧
    sliceCard .orderFour = 2 ∧
    sliceCard .orderThree = 1 ∧
    sliceCard .orderSix = 1 := by
  native_decide

theorem explicit_residual_card :
    residualCard = 266 := by
  native_decide

theorem explicit_partition_counts_all_A_copies :
    sliceCard .identity +
    sliceCard .minusOne +
    sliceCard .orderFour +
    sliceCard .orderThree +
    sliceCard .orderSix +
    residualCard = M.weightTwo.a := by
  native_decide

theorem requested_five_total_is_ten :
    sliceCard .identity +
    sliceCard .minusOne +
    sliceCard .orderFour +
    sliceCard .orderThree +
    sliceCard .orderSix = 10 := by
  native_decide

/-- The requested five numerical lengths are constructible inside the actual
source multiplicity, but they necessarily leave a residual at weight two. -/
theorem five_slices_exist_with_unavoidable_residual :
    (sliceCard .identity, sliceCard .minusOne, sliceCard .orderFour,
      sliceCard .orderThree, sliceCard .orderSix, residualCard)
      = (3,3,2,1,1,266) := by
  native_decide

/-!
## Concrete selected Tate modules

Each actual A-copy contributes one ordinary Hhat0 class over F2.  After the
explicit enumeration choice above, the selected direct sums are therefore
ordinary finite-dimensional F2 modules of the requested dimensions.
-/

abbrev IdentitySelectedTateModule := Fin 3 → ZMod 2
abbrev MinusOneSelectedTateModule := Fin 3 → ZMod 2
abbrev OrderFourSelectedTateModule := Fin 2 → ZMod 2
abbrev OrderThreeSelectedTateModule := Fin 1 → ZMod 2
abbrev OrderSixSelectedTateModule := Fin 1 → ZMod 2
abbrev ResidualSelectedTateModule := Fin 266 → ZMod 2

theorem identity_selected_module_card :
    Fintype.card IdentitySelectedTateModule = 2^3 := by
  native_decide

theorem minusOne_selected_module_card :
    Fintype.card MinusOneSelectedTateModule = 2^3 := by
  native_decide

theorem orderFour_selected_module_card :
    Fintype.card OrderFourSelectedTateModule = 2^2 := by
  native_decide

theorem orderThree_selected_module_card :
    Fintype.card OrderThreeSelectedTateModule = 2^1 := by
  native_decide

theorem orderSix_selected_module_card :
    Fintype.card OrderSixSelectedTateModule = 2^1 := by
  native_decide

/-- The five selected factors together have 10 binary Tate generators. -/
theorem five_selected_binary_generator_count :
    3 + 3 + 2 + 1 + 1 = 10 := by
  decide

/-- Source provenance boundary: these module objects are selected direct sums
of actual A-copy Tate classes, but the five *names* are an enumeration choice.
No theorem in the source identifies those names with geometric inertia sectors. -/
structure FiveSliceSelectionBoundary where
  selectedFromActualWeightTwoACopies : Bool
  perCopyOrdinaryTateClassIsBinary : Bool
  requestedDimensionsRealized : Bool
  residualDimension : Nat
  inertiaSectorIdentificationSourced : Bool
  deriving Repr

def canonicalFiveSliceSelectionBoundary : FiveSliceSelectionBoundary where
  selectedFromActualWeightTwoACopies := true
  perCopyOrdinaryTateClassIsBinary := true
  requestedDimensionsRealized := true
  residualDimension := 266
  inertiaSectorIdentificationSourced := false

end Integration.OggSSP2BActualFiveSlices
