import BSDCohomology.EllipticTwoTorsionAction
import Mathlib.RepresentationTheory.Continuous.TopRep
import Mathlib.Topology.Order

/-!
# Actual geometric elliptic-point and E[2] topological Galois representations

This module takes the literal base-change point actions already constructed and
bundles them with the discrete topology used for classical Galois cohomology.

Two distinct representations are needed:

* E(K̄), whose H¹ localization kernel is the classical elliptic Tate–Shafarevich
  target (up to the standard completion/base-change comparison);
* E[2], whose H¹ receives the Kummer connecting map used to define Sel₂.

Keeping these distinct prevents the false identification Sha¹(K,E[2]) = Sha(E)[2].
-/

namespace BSDCohomology

open WeierstrassCurve

noncomputable section

universe u

variable {K : Type u} [Field K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

------------------------------------------------------------------------
-- Discrete topology on geometric points.
------------------------------------------------------------------------

section GeometricPointTopology

local instance : TopologicalSpace (GeometricPoint W) := ⊥
local instance : DiscreteTopology (GeometricPoint W) :=
  discreteTopology_bot _

/-- Each Galois point action is automatically a continuous ℤ-linear
endomorphism for the discrete topology. -/
noncomputable def galoisPointContinuousEnd
    (σ : Field.absoluteGaloisGroup K) :
    GeometricPoint W →L[ℤ] GeometricPoint W where
  __ := (galoisPointMap W σ).toIntLinearMap
  cont := continuous_of_discreteTopology

/-- The literal geometric point action as a continuous representation. -/
noncomputable def geometricPointContRepresentation :
    ContRepresentation ℤ (Field.absoluteGaloisGroup K) (GeometricPoint W) :=
  ContRepresentation.ofMonoidHom
    { toFun := galoisPointContinuousEnd W
      map_one' := by
        ext P
        exact galoisPointMap_one W P
      map_mul' := by
        intro σ τ
        ext P
        exact galoisPointMap_mul W σ τ P }

/-- Actual E(K̄) Galois module as a TopRep. -/
noncomputable def geometricPointTopRep :
    TopRep ℤ (Field.absoluteGaloisGroup K) :=
  TopRep.of (geometricPointContRepresentation W)

end GeometricPointTopology

------------------------------------------------------------------------
-- Discrete topology on the literal E[2] subgroup.
------------------------------------------------------------------------

section TwoTorsionTopology

local instance : TopologicalSpace (EllipticTwoTorsion W) := ⊥
local instance : DiscreteTopology (EllipticTwoTorsion W) :=
  discreteTopology_bot _

/-- Each restricted E[2] action is a continuous ℤ-linear endomorphism. -/
noncomputable def galoisTwoTorsionContinuousEnd
    (σ : Field.absoluteGaloisGroup K) :
    EllipticTwoTorsion W →L[ℤ] EllipticTwoTorsion W where
  __ := (galoisTwoTorsionMap W σ).toIntLinearMap
  cont := continuous_of_discreteTopology

/-- Actual E[2] continuous representation. -/
noncomputable def ellipticTwoTorsionContRepresentation :
    ContRepresentation ℤ (Field.absoluteGaloisGroup K)
      (EllipticTwoTorsion W) :=
  ContRepresentation.ofMonoidHom
    { toFun := galoisTwoTorsionContinuousEnd W
      map_one' := by
        ext P
        exact congrArg Subtype.val
          (congrFun
            (congrArg (fun f => fun x => f x)
              (galoisTwoTorsionMap_one W)) P)
      map_mul' := by
        intro σ τ
        ext P
        apply Subtype.ext
        exact galoisPointMap_mul W σ τ P.1 }

/-- Actual E[2] Galois module as a TopRep. -/
noncomputable def ellipticTwoTorsionTopRep :
    TopRep ℤ (Field.absoluteGaloisGroup K) :=
  TopRep.of (ellipticTwoTorsionContRepresentation W)

end TwoTorsionTopology

/-!
NEXT:
* construct the inclusion E[2] → E(K̄) as a morphism of TopRep;
* prove exactness of 0 → E[2] → E(K̄) --[2]→ E(K̄);
* derive the degree-zero/degree-one connecting morphism;
* compare its local conditions with Stoll's x-T presentation.
-/

end

end BSDCohomology
