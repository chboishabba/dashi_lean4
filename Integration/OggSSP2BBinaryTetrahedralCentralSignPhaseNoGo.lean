import Integration.OggSSP2BDefectTwoBitProvenanceSelector

/-!
# Binary-tetrahedral central sign is not the Completion10 BinaryPhase

The current Completion10 ontology is

  TenState ≃ Mode5 × BinaryPhase

and its complement involution preserves the Mode5 coordinate while flipping
BinaryPhase.

By contrast, multiplication by the central element -1 in the binary
tetrahedral group exchanges the order strata

  1 <-> 2,
  3 <-> 6,
  4 -> 4.

Therefore no Mode5-to-order-stratum chart can make the Completion10 phase flip
look like central-sign multiplication at the order-stratum level: the former is
identity on Mode5, while the latter moves four of the five strata.

This kills a tempting but incorrect shortcut for choosing the two provenance
bits.  The bits must come from independent source structure.
-/

namespace Integration.OggSSP2BBinaryTetrahedralCentralSignPhaseNoGo

namespace F := Integration.OggSSP2BFiveByTwoDefectArchitecture
namespace D := Integration.OggSSP2BBinaryTetrahedralDefectSource

/-- Action of the central -1 on the five order strata. -/
def centralSignOnStratum : D.OrderStratum → D.OrderStratum
  | .identity => .centralMinusOne
  | .centralMinusOne => .identity
  | .orderFour => .orderFour
  | .orderThree => .orderSix
  | .orderSix => .orderThree

theorem centralSignOnStratum_involutive :
    Function.Involutive centralSignOnStratum := by
  intro s
  cases s <;> rfl

theorem centralSign_moves_identity :
    centralSignOnStratum .identity ≠ .identity := by
  decide

theorem centralSign_moves_orderThree :
    centralSignOnStratum .orderThree ≠ .orderThree := by
  decide

/-- Completion complement is invisible on the Mode5 quotient. -/
theorem completion_phase_is_identity_on_mode
    (x : F.TenState) :
    (F.encode (F.complement x)).1 = (F.encode x).1 :=
  F.complement_preserves_mode x

/-- Any bijection from Mode5 to the order strata transports the Completion10
phase action to the identity on order strata, because complement preserves the
Mode5 coordinate.  Hence it cannot equal central-sign multiplication, which
moves the identity stratum. -/
theorem no_mode_chart_intertwines_completion_phase_with_central_sign
    (e : F.Mode5 ≃ D.OrderStratum) :
    ¬ (∀ m : F.Mode5, centralSignOnStratum (e m) = e m) := by
  intro h
  let m := e.symm D.OrderStratum.identity
  have hm := h m
  have he : e m = D.OrderStratum.identity := by
    simp [m]
  rw [he] at hm
  exact centralSign_moves_identity hm

/-- In particular, none of the four defect-compatible charts can source-select
D by identifying BinaryPhase with the central sign. -/
theorem defect_compatible_chart_central_sign_shortcut_killed
    (e : Integration.OggSSP2BDefectRecognitionAmbiguity.DefectCompatibleChart) :
    ¬ (∀ m : F.Mode5, centralSignOnStratum (e.1 m) = e.1 m) :=
  no_mode_chart_intertwines_completion_phase_with_central_sign e.1

end Integration.OggSSP2BBinaryTetrahedralCentralSignPhaseNoGo
