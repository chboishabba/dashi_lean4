import Synthesis.MillenniumHodgeCP1SingularTransport
import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.Topology.Constructions

/-!
# Same-object CP¹ ≃ TopCat.sphere 2, reusing actual source objects

Producers:
  Synthesis.MillenniumHodgeCP1TopologicalSphere.cp1HomeomorphSphere
  Synthesis.MillenniumHodgeCP1SingularTransport.cp1SingularH2
  Mathlib.Topology.Category.TopCat.Sphere.sphere (v4.28.0)

Mathlib defines `TopCat.sphere n` as the ULift of the unit sphere in
`EuclideanSpace ℝ (Fin (n+1))`. The existing CP¹ homeomorphism targets
the same Euclidean sphere before ULift. This module discharges that
*actual point-set identification*, leaving no mysterious "same sphere"
name-only assumption.

Hatcher-at's `Hatcher.Sphere.reducedHomology_sphere` (Jack McCarthy,
2026, based on Hatcher Corollary 2.14) concerns this same TopCat.sphere
but currently uses mathlib v4.34.1; dashi_lean4 pins v4.28.0. This
module does not import Hatcher-at and does not claim to transport its
kernel certificate across incompatible mathlib revisions.
-/

namespace Synthesis.ExoticTopology

open CategoryTheory
open AlgebraicTopology
open Synthesis.Millennium.Hodge

/-- Canonical homeomorphism of a space and its universe lift. The continuity
    lemmas are sourced directly from Mathlib.Topology.Constructions v4.28. -/
def sphere2ToULift : UnitSphere2 ≃ₜ ULift UnitSphere2 where
  toFun := ULift.up
  invFun := ULift.down
  left_inv := by intro x; rfl
  right_inv := by intro x; cases x; rfl
  continuous_toFun := continuous_uliftUp
  continuous_invFun := continuous_uliftDown

/-- A genuine homeomorphism to the exact TopCat.sphere 2 UNDERLYING TYPE. -/
noncomputable def cp1HomeomorphTopCatSphere2 :
    CP1 ≃ₜ ULift UnitSphere2 :=
  cp1HomeomorphSphere.trans sphere2ToULift

/-- No new topology is postulated: the target unfolds to TopCat.sphere 2. -/
noncomputable def cp1IsoTopCatSphere2 :
    TopCat.of CP1 ≅ TopCat.sphere 2 :=
  TopCat.isoOfHomeo cp1HomeomorphTopCatSphere2

/-- Functorial rational singular degree-two homology transport to Mathlib's
    exact `TopCat.sphere 2`, with no supplied analytic/homological gap token.
    This is STILL transport, not a calculation of the target homology object. -/
noncomputable def cp1SingularH2IsoTopCatSphere2 :
    cp1SingularH2 ≅
      ((singularHomologyFunctor (ModuleCat ℚ) 2).obj
        rationalCoefficientObject).obj (TopCat.sphere 2) :=
  ((singularHomologyFunctor (ModuleCat ℚ) 2).obj
    rationalCoefficientObject).mapIso cp1IsoTopCatSphere2

theorem cp1TopCatSphereH2_left_right :
    cp1SingularH2IsoTopCatSphere2.hom ≫
      cp1SingularH2IsoTopCatSphere2.inv = 𝟙 cp1SingularH2 := by
  simp

end Synthesis.ExoticTopology
