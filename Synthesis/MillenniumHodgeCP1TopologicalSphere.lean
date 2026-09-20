import Synthesis.MillenniumHodgeCP1Quotient
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.Topology.Homeomorph.TransferInstance
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic

/-!
# The literal complex projective line is topologically a 2-sphere

Mathlib provides a set-theoretic equivalence
`OnePoint ℂ ≃ Projectivization ℂ (Fin 2 → ℂ)` and a homeomorphism from
`OnePoint ℂ` to the unit sphere in `ℝ³`.  We transport the canonical
one-point-compactification topology across the projective equivalence and
compose the homeomorphisms.

This pays the literal topological CP¹ realization.  It does not compute
singular cohomology or assert a cycle-class theorem.
-/

namespace Synthesis.Millennium.Hodge

open Projectivization
open scoped LinearAlgebra.Projectivization

noncomputable instance cp1TopologicalSpace : TopologicalSpace CP1 :=
  ((OnePoint.equivProjectivization ℂ).symm).topologicalSpace

noncomputable def cp1HomeomorphOnePoint :
    CP1 ≃ₜ OnePoint ℂ :=
  ((OnePoint.equivProjectivization ℂ).symm).homeomorph

abbrev UnitSphere2 :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

noncomputable def onePointComplexHomeomorphSphere :
    OnePoint ℂ ≃ₜ UnitSphere2 :=
  onePointEquivSphereOfFinrankEq
    (V := ℂ) (ι := Fin 3)
    (by norm_num [Complex.finrank_real_complex])

noncomputable def cp1HomeomorphSphere :
    CP1 ≃ₜ UnitSphere2 :=
  cp1HomeomorphOnePoint.trans onePointComplexHomeomorphSphere

theorem cp1_topologically_is_sphere :
    Nonempty (CP1 ≃ₜ UnitSphere2) :=
  ⟨cp1HomeomorphSphere⟩


end Synthesis.Millennium.Hodge
