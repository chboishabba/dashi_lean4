import Integration.MoonshineMonstrousExponentTrialecticCodec
import Integration.Kernel.Quotient
import Mathlib

namespace Integration.MoonshineTrialecticSurfaceConsumerRouting

open Integration.MoonshineMonstrousExponentTrialecticCodec
open Integration.Kernel.Quotient

/-!
# Arithmetic T3 surface -> declared T9 carrier routing

This is the Lean carrier-level mirror of the Agda trialectic surface-consumer
routing theorem.

Lean does not yet mirror the full Agda trialectic/Rubik/Cech stack, so this file
does not manufacture those structures.  It proves the exact statement already
available at the shared carrier level:

* one coarse arithmetic T3 surface can be inserted into a declared A/B/C row of
  a T9 carrier;
* the selected row reopens exactly;
* every consumer computed from that declared T9 carrier descends through the
  coarse T3 surface;
* arithmetic magnitudes still do not descend merely because the T3 row has been
  embedded into T9.

Thus T3 -> T9 adds presentation structure but no arithmetic information.
-/

inductive DeclaredRowSlot
  | rowA | rowB | rowC
  deriving DecidableEq, Repr

abbrev T9Carrier := Surface3 × Surface3 × Surface3

def neutralSurface : Surface3 :=
  ⟨.zero, .zero, .zero⟩

def embedDeclaredRow : DeclaredRowSlot → Surface3 → T9Carrier
  | .rowA, row => (row, neutralSurface, neutralSurface)
  | .rowB, row => (neutralSurface, row, neutralSurface)
  | .rowC, row => (neutralSurface, neutralSurface, row)

def selectedRow : DeclaredRowSlot → T9Carrier → Surface3
  | .rowA, matrix => matrix.1
  | .rowB, matrix => matrix.2.1
  | .rowC, matrix => matrix.2.2

theorem selected_row_after_embedding
    (slot : DeclaredRowSlot) (row : Surface3) :
    selectedRow slot (embedDeclaredRow slot row) = row := by
  cases slot <;> rfl

/-! ## Surface-only geometric consumers -/

def declaredMatrixConsumer (slot : DeclaredRowSlot) (row : Surface3) : T9Carrier :=
  embedDeclaredRow slot row

theorem matrix_consumer_descends_through_surface
    (slot : DeclaredRowSlot) :
    DescendsThrough
      (fun t : ArithmeticTriple => declaredMatrixConsumer slot (surface t))
      surface :=
  ⟨declaredMatrixConsumer slot, fun _ => rfl⟩

/-- Any further consumer of the declared T9 carrier also descends through the
same T3 surface. -/
theorem composed_t9_consumer_descends
    {Outcome : Type*}
    (slot : DeclaredRowSlot)
    (consume : T9Carrier → Outcome) :
    DescendsThrough
      (fun t : ArithmeticTriple => consume (embedDeclaredRow slot (surface t)))
      surface :=
  ⟨fun row => consume (embedDeclaredRow slot row), fun _ => rfl⟩

/-! ## Embedding adds no arithmetic information -/

theorem p7_p13_same_declared_matrix
    (slot : DeclaredRowSlot) :
    embedDeclaredRow slot (surface p7Triple) =
      embedDeclaredRow slot (surface p13Triple) := by
  rw [p7_p13_surface_collision]

theorem exponent_sum_does_not_descend_through_declared_matrix
    (slot : DeclaredRowSlot) :
    ¬ DescendsThrough
      exponentSum
      (fun t : ArithmeticTriple => embedDeclaredRow slot (surface t)) :=
  not_descendsThrough_of_collision
    (x := p7Triple) (y := p13Triple)
    (p7_p13_same_declared_matrix slot)
    p7_p13_sum_distinct

theorem fricke_magnitude_does_not_descend_through_declared_matrix
    (slot : DeclaredRowSlot) :
    ¬ DescendsThrough
      (roleMagnitude .frickeComparison)
      (fun t : ArithmeticTriple => embedDeclaredRow slot (surface t)) :=
  not_descendsThrough_of_collision
    (x := p7Triple) (y := p13Triple)
    (p7_p13_same_declared_matrix slot)
    (by decide)

theorem level_p_magnitude_does_not_descend_through_declared_matrix
    (slot : DeclaredRowSlot) :
    ¬ DescendsThrough
      (roleMagnitude .levelPComparison)
      (fun t : ArithmeticTriple => embedDeclaredRow slot (surface t)) :=
  not_descendsThrough_of_collision
    (x := p7Triple) (y := p13Triple)
    (p7_p13_same_declared_matrix slot)
    (by decide)

/-! ## Exact-code handoff

If a downstream consumer really needs arithmetic information, it should consume
the dependent residual code rather than infer it from the T9 presentation.
-/

theorem exact_code_still_suffices_after_t9_routing
    {Outcome : Type*}
    (consumer : ArithmeticTriple → Outcome) :
    DescendsThrough consumer encodeTriple :=
  every_consumer_descends_through_exact_code consumer

structure Boundary where
  declaredT9CarrierOwned : Bool
  rowSlotMustBeDeclared : Bool
  selectedRowReopensExactly : Bool
  arbitraryT9ConsumerDescendsThroughT3 : Bool
  t9EmbeddingAddsArithmeticMagnitude : Bool
  exponentSumStillNeedsResidual : Bool
  frickeMagnitudeStillNeedsResidual : Bool
  levelPMagnitudeStillNeedsResidual : Bool
  exactArithmeticCodeStillSuffices : Bool
  fullAgdaRubikCechMirrorClaimedHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  declaredT9CarrierOwned := true
  rowSlotMustBeDeclared := true
  selectedRowReopensExactly := true
  arbitraryT9ConsumerDescendsThroughT3 := true
  t9EmbeddingAddsArithmeticMagnitude := false
  exponentSumStillNeedsResidual := true
  frickeMagnitudeStillNeedsResidual := true
  levelPMagnitudeStillNeedsResidual := true
  exactArithmeticCodeStillSuffices := true
  fullAgdaRubikCechMirrorClaimedHere := false

end Integration.MoonshineTrialecticSurfaceConsumerRouting
