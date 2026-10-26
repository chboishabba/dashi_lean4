import Synthesis.ExoticTopologyCantorInverseLimit
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Topology.Constructions
import Mathlib.Topology.Clopen

/-!
# Source-owned compatible binary frontiers have the Cantor product topology

Reuse without a second tower:
* `Integration.Address.Addr n Bool` is the *actual* existing finite
  frontier carrier.
* `Synthesis.ExoticTopologyCantorInverseLimit.CompatibleCantorTower`
  is the prior exact coherent-prefix inverse limit with both
  stream/tower round trips.
* Mathlib v4.28.0 already provides the genuine
  `cantorSetHomeomorphNatToBool` on the literal real Cantor set
  (original Mathlib theorem and contributors retained).

The topology of the source tower is INDUCED by its simultaneous
projection to all discrete finite-depth stages. It is *not*
defined by pulling a topology back along the new homeomorphism:
this matters for proving the correct inverse-limit universal
presentation, not manufacturing a homeomorphism by definition.

This source attempts to prove both directions continuous directly
from Mathlib's continuous finite-coordinate evaluations. Thus the
symbolic inverse-limit/Cantor-realisation join is an actual
topological homeomorphism, not just a set equivalence.

It DOES NOT define the topological Freudenthal/Richards ideal-boundary
space of the actual infinite oriented PL two-manifold; that separate
same-object end-space comparison is the next geometry obligation.
No equivalence of the uniform ternary product probability measure
and the fair dyadic product measure is implied or claimed.

Attribution: classical Cantor product-topology mathematics, the
original Mathlib CantorSet module; Richards (1963) only for the
actual noncompact surface ideal-boundary classification.
Source-written / kernel-check pending as of the authoring commit.
-/

namespace Synthesis.ExoticTopology

/-- The REAL stagewise inverse-limit topology, induced by the
simultaneous map into the product of finite binary-frontier spaces. -/
instance compatibleCantorTowerTopology : TopologicalSpace CompatibleCantorTower :=
  TopologicalSpace.induced
    (fun t : CompatibleCantorTower => t.stage) inferInstance

/-- The actual source stage projection into the full product of
finite frontier spaces is continuous by definition of this induced
topology. Its codomain uses the ordinary product topology. -/
theorem continuous_towerStage :
    Continuous (fun t : CompatibleCantorTower => t.stage) :=
  continuous_induced_dom

/-- The k-th stream coordinate is the final coordinate of stage k+1.
Prove continuity using the inherited product topology on stage data. -/
theorem continuous_towerToStream :
    Continuous (towerToStream : CompatibleCantorTower → BinaryEndStream) := by
  apply continuous_pi
  intro k
  change Continuous
    (fun t : CompatibleCantorTower => t.stage (k + 1) (Fin.last k))
  exact (continuous_apply (Fin.last k)).comp
    ((continuous_apply (k + 1)).comp continuous_towerStage)

/-- Build ALL finite coherent stages from a product-topology binary
stream. Each stage and each of its Fin n coordinates is a continuous
evaluation map. -/
theorem continuous_streamToTower :
    Continuous (streamToTower : BinaryEndStream → CompatibleCantorTower) := by
  apply continuous_induced_rng.mpr
  change Continuous
    (fun s : BinaryEndStream => (streamToTower s).stage)
  apply continuous_pi
  intro n
  apply continuous_pi
  intro i
  change Continuous (fun s : BinaryEndStream => s i.val)
  exact continuous_apply i.val

/-- GENUINE homeomorphism of the canonical binary inverse limit
with streams under its stage-product topology. -/
def cantorEndInverseLimitHomeomorph :
    CompatibleCantorTower ≃ₜ BinaryEndStream where
  toEquiv := cantorEndInverseLimitEquiv
  continuous_toFun := continuous_towerToStream
  continuous_invFun := continuous_streamToTower


/-- Actual clopen cylinder on the existing coherent tower:
select every infinite address whose STAGE-n source address is w.
Not a clopen subset of the connected 2D surface itself. -/
def sourceStageCylinder (n : ℕ) (w : CantorStage n) :
    Set CompatibleCantorTower :=
  { t | t.stage n = w }

/-- Genuine topological clopen, not merely the Boolean claim that a
finite string has an address. Uses the pinned v4.28.0 Mathlib
`isClopen_discrete` and `IsClopen.preimage` APIs. -/
theorem sourceStageCylinder_isClopen (n : ℕ) (w : CantorStage n) :
    IsClopen (sourceStageCylinder n w) := by
  have h : Continuous (fun t : CompatibleCantorTower => t.stage n) :=
    (continuous_apply n).comp continuous_towerStage
  change IsClopen
    ((fun t : CompatibleCantorTower => t.stage n) ⁻¹' ({w} : Set (CantorStage n)))
  exact (isClopen_discrete ({w} : Set (CantorStage n))).preimage h

/-- Actual child cylinder EVENT inclusion on the coherent-product
topology. This proof relies on the ORIGINAL compatible tower proof,
not an incompatible prepend-word convention. -/
theorem sourceStageChildCylinder_subset (n : ℕ)
    (child : CantorStage (n + 1)) :
    sourceStageCylinder (n + 1) child ⊆
      sourceStageCylinder n (forgetLast n child) := by
  intro t ht
  change t.stage (n + 1) = child at ht
  change t.stage n = forgetLast n child
  have hcompat : forgetLast n (t.stage (n + 1)) = t.stage n := by
    funext i
    exact t.compatible n i
  exact hcompat.symm.trans (congrArg (forgetLast n) ht)

/-- Compose with Mathlib's pinned v4.28.0 theorem on the LITERAL
real middle-thirds Cantor set, not a new hand-defined subset. -/
noncomputable def realCantorSetHomeomorphToSourceFrontiers :
    cantorSet ≃ₜ CompatibleCantorTower :=
  cantorSetHomeomorphNatToBool.trans
    cantorEndInverseLimitHomeomorph.symm

/-- Retains the same exact finite-stage projection identity for
the resulting real Cantor-set point via the SOURCE coherent tower. -/
theorem realCantorStageForget
    (x : cantorSet) (n : ℕ) :
    forgetLast n ((realCantorSetHomeomorphToSourceFrontiers x).stage (n + 1)) =
      (realCantorSetHomeomorphToSourceFrontiers x).stage n := by
  funext i
  exact (realCantorSetHomeomorphToSourceFrontiers x).compatible n i

end Synthesis.ExoticTopology
