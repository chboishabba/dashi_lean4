import Synthesis.MillenniumBSDNumberFieldSelmerShaOriginalWeldExact
import Synthesis.MillenniumBSDGeneralKummerCosetExact

/-!
Source-native rational doubles, number-field two-Selmer inclusion,
and original Sha kernel have the SAME K-curve and actual completions.
No generic substitute field, square-class quotient or extra half data.
-/
namespace BSDCohomology
open WeierstrassCurve
noncomputable section
universe u
variable {K : Type u} [Field K] [NumberField K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- Original rational double-coset BIDI at the selected original
number-field Selmer source. This uses actual rational, not geometric,
halves on the right. -/
theorem numberFieldKummerSelmer_sameCoset
    (P R : BasePoint W) :
    numberFieldKummerToSelmer W P =
      numberFieldKummerToSelmer W R ↔
      ∃ S : BasePoint W, (2 : ℕ) • S = P - R := by
  constructor
  · intro h
    apply (general_rationalKummer_sameCoset W P R).mp
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    exact (general_rationalKummer_sameCoset W P R).mpr h

/-- Image of original rational point group equals kernel of the
original number-field Selmer-to-point-Sha map. The quotient is
already provided by numberFieldSelmerQuotientEquivShaTwo. -/
theorem numberFieldSelmerSha_zero_iff_globalKummer
    (z : numberFieldSelmerTwo W) :
    selmerToShaTwo W
      (general_geometric_doubling_onto W)
      (fun v => general_geometric_doubling_onto (localCurve W v)) z = 0 ↔
      ∃ P : BasePoint W, numberFieldKummerToSelmer W P = z := by
  change z ∈
    (selmerToShaTwo W
      (general_geometric_doubling_onto W)
      (fun v => general_geometric_doubling_onto (localCurve W v))).ker ↔ _
  rw [numberField_selmerToSha_kernel W]
  change z ∈ (numberFieldKummerToSelmer W).range ↔ _
  exact AddSubgroup.mem_range

end
end BSDCohomology
