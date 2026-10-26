import Mathlib.Topology.CWComplex.Classical.Finite
import Synthesis.MillenniumHodgeCP1TopologicalSphere

/-!
# CW realisation consumers: reuse Mathlib's actual point-set CW class

Pinned source: mathlib4 v4.28.0 (lake-manifest commit
8f9d9cff6bd728b17a24e163c9402775d9e6a365).
Source authors of Classical.Basic/Finite: Floris van Doorn,
Hannah Scholz, and contributors. The actual classes are
`Topology.CWComplex`, `Topology.RelCWComplex`.
Pinned finite constructors are `Topology.CWComplex.mkFinite` and
`Topology.CWComplex.mkFiniteType`, NOT `mkFinite_map`.

This acceptance contract has NO constructor from cell counts, Betti
numbers, homology alone, or the `CP1 ≃ₜ S²` homeomorphism.
It requires an instantiated Mathlib CW structure on the actual point set.

CW is data (a Type-valued class), not a Prop theorem automatically
derivable from a numeric Euler characteristic. No Whitehead theorem
or claim that a particular CW structure has been supplied.
-/

namespace Synthesis.ExoticTopology

universe u

/-- Concrete CW realisation as Mathlib-native data. -/
structure RealisedCW (X : Type u) [TopologicalSpace X] where
  carrier : Set X
  cw : Topology.CWComplex carrier

/-- A genuine Mathlib CW structure can be imported without duplication. -/
def RealisedCW.fromMathlib {X : Type u} [TopologicalSpace X]
    (C : Set X) [inst : Topology.CWComplex C] : RealisedCW X :=
  ⟨C, inst⟩

/-- Extract the same-carrier structure; this does not build a CW complex. -/
def RealisedCW.sourceCW {X : Type u} [TopologicalSpace X]
    (R : RealisedCW X) : Topology.CWComplex R.carrier :=
  R.cw

open Synthesis.Millennium.Hodge

/-- CP¹ already has a genuine sphere homeomorphism in
    MillenniumHodgeCP1TopologicalSphere. This additional obligation
    represents a *real CW structure on that exact CP¹ carrier*.
    It is deliberately not inhabited by the homeomorphism alone. -/
structure CP1CellularTopologicalAcceptance where
  cw : Topology.CWComplex (Set.univ : Set CP1)

/-- Source-owned topological equivalence is usable independently of a CW
    acceptance witness. -/
def cp1ActualSphereHomeomorphism :
    CP1 ≃ₜ UnitSphere2 :=
  cp1HomeomorphSphere

/-- Once a proper CW structure on CP¹ is actually supplied,
    it can be passed directly to any Mathlib CW consumer. -/
def CP1CellularTopologicalAcceptance.toRealisedCW
    (a : CP1CellularTopologicalAcceptance) :
    RealisedCW CP1 :=
  ⟨Set.univ, a.cw⟩

end Synthesis.ExoticTopology
