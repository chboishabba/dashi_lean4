import Synthesis.MillenniumBSDGeneralGeometricDoublingExact
import Synthesis.MillenniumBSDOriginalPlaceKummerNaturalityExact

namespace BSDCohomology
open WeierstrassCurve CategoryTheory DASHI.BSD.OriginalH1
noncomputable section
universe u
variable {K : Type u} [Field K] [NumberField K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- All-place naturality without supplied geometric doubling witnesses.
The actual general tangent-quartic construction owns both witnesses. -/
theorem general_place_rationalKummer_natural
    (v : OriginalPlace K) (P : BasePoint W) :
    placeTorsionLoc W v
      (rationalKummerClass W (general_geometric_doubling_onto W) P) =
      rationalKummerClass (localCurve W v)
        (general_geometric_doubling_onto (localCurve W v))
        (placeBasePoint W v P) := by
  exact place_rationalKummer_natural W
    (general_geometric_doubling_onto W)
    (fun v => general_geometric_doubling_onto (localCurve W v)) v P

end
end BSDCohomology
