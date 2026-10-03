import BSDCohomology.EllipticPointTopRep
import BSDCohomology.EllipticKummerKernelExact

/-!
# Elliptic Kummer maps as actual TopRep morphisms

The underlying group maps

  E[2] → E(Kbar) →[2] E(Kbar)

already exist and commute with the literal absolute-Galois point action.  This
file packages them as morphisms between the exact continuous representations
used by the cohomological BSD lane.
-/

namespace BSDCohomology

open WeierstrassCurve
open CategoryTheory

noncomputable section

universe u

variable {K : Type u} [Field K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

------------------------------------------------------------------------
-- Work with the same discrete topologies used to construct the TopRep objects.
------------------------------------------------------------------------

local instance : TopologicalSpace (GeometricPoint W) := ⊥
local instance : DiscreteTopology (GeometricPoint W) :=
  discreteTopology_bot _
local instance : TopologicalSpace (EllipticTwoTorsion W) := ⊥
local instance : DiscreteTopology (EllipticTwoTorsion W) :=
  discreteTopology_bot _

noncomputable def twoTorsionInclusionContinuousLinear :
    EllipticTwoTorsion W →L[ℤ] GeometricPoint W where
  __ := (twoTorsionInclusion W).toIntLinearMap
  cont := continuous_of_discreteTopology

noncomputable def geometricDoublingContinuousLinear :
    GeometricPoint W →L[ℤ] GeometricPoint W where
  __ := (geometricDoubling W).toIntLinearMap
  cont := continuous_of_discreteTopology

/-- Inclusion of literal E[2] into geometric points as an equivariant
continuous linear map. -/
noncomputable def twoTorsionInclusionIntertwining :
    (ellipticTwoTorsionContRepresentation W) →ⁱL
      (geometricPointContRepresentation W) :=
  ⟨twoTorsionInclusionContinuousLinear W, by
    intro σ
    ext P
    rfl⟩

/-- Multiplication by two on geometric points as an equivariant continuous
linear map. -/
noncomputable def geometricDoublingIntertwining :
    (geometricPointContRepresentation W) →ⁱL
      (geometricPointContRepresentation W) :=
  ⟨geometricDoublingContinuousLinear W, by
    intro σ
    ext P
    exact galoisPointMap_double W σ P⟩

/-- Actual TopRep morphism E[2] → E(Kbar). -/
noncomputable def twoTorsionInclusionTopRep :
    ellipticTwoTorsionTopRep W ⟶ geometricPointTopRep W :=
  TopRep.ofHom (twoTorsionInclusionIntertwining W)

/-- Actual TopRep morphism [2] : E(Kbar) → E(Kbar). -/
noncomputable def geometricDoublingTopRep :
    geometricPointTopRep W ⟶ geometricPointTopRep W :=
  TopRep.ofHom (geometricDoublingIntertwining W)

@[simp] theorem twoTorsionInclusionTopRep_apply
    (P : EllipticTwoTorsion W) :
    twoTorsionInclusionTopRep W P = P.1 := rfl

@[simp] theorem geometricDoublingTopRep_apply
    (P : GeometricPoint W) :
    geometricDoublingTopRep W P = 2 • P := rfl

/-- The TopRep Kummer complex composes to zero on the literal same objects. -/
theorem geometricDoubling_comp_twoTorsionInclusionTopRep_zero :
    twoTorsionInclusionTopRep W ≫ geometricDoublingTopRep W = 0 := by
  ext P
  change (2 : ℕ) • (P : GeometricPoint W) = 0
  exact P.2

/-!
PAID:
* literal inclusion and doubling are morphisms of the actual continuous
  Galois representations;
* equivariance is proved from the same point action;
* the Kummer complex composes to zero as a TopRep complex.

NEXT:
* transport underlying injectivity/range=kernel/surjectivity to the selected
  curve's TopRep morphisms;
* instantiate the low-degree connecting morphism.
-/

end

end BSDCohomology
