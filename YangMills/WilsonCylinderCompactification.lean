import Mathlib
import YangMills.WilsonCountableToL2Density

/-!
# Canonical compact Wilson-cylinder continuum state space

For a chosen countable real Wilson/cylinder family on any raw configuration
carrier, first apply `tanh` coordinatewise and map into the countable cube
`[-1,1]^ℕ`.  Define the generalized continuum cylinder state space to be the
topological closure of that image.

This is the weakest state space needed by the cylinder-first route.  It is
compact by construction, its coordinate functions separate points tautologically,
and Stone--Weierstrass/L2 density therefore follow without any additional
abstract separation hypothesis.  Recovering a stronger local-field topology is
left to the later G regularity programme.
-/

namespace RequestProject.YangMills

/-- Closed unit interval used as each bounded Wilson coordinate. -/
abbrev WilsonUnitInterval := Set.Icc (-1 : ℝ) 1

noncomputable instance : CompactSpace WilsonUnitInterval :=
  isCompact_iff_compactSpace.mp isCompact_Icc

/-- Coordinatewise bounded Wilson map into the countable compact cube. -/
def wilsonTanhCubeMap
    {Ω : Type*}
    (raw : ℕ → Ω → ℝ) : Ω → (ℕ → WilsonUnitInterval) :=
  fun x i =>
    ⟨Real.tanh (raw i x), by
      constructor
      · exact le_of_lt (Real.neg_one_lt_tanh (raw i x))
      · exact le_of_lt (Real.tanh_lt_one (raw i x))⟩

/-- The generalized Wilson-cylinder state is the closure of the selected bounded coordinate image. -/
def WilsonCylinderState
    {Ω : Type*}
    (raw : ℕ → Ω → ℝ) :=
  {z : ℕ → WilsonUnitInterval //
    z ∈ closure (Set.range (wilsonTanhCubeMap raw))}

noncomputable instance wilsonCylinderStateCompact
    {Ω : Type*} (raw : ℕ → Ω → ℝ) :
    CompactSpace (WilsonCylinderState raw) :=
  isCompact_iff_compactSpace.mp isClosed_closure.isCompact

/-- Real-valued coordinate projection on the compactified cylinder state. -/
def wilsonCylinderCoordinate
    {Ω : Type*} (raw : ℕ → Ω → ℝ) (i : ℕ) :
    C(WilsonCylinderState raw, ℝ) where
  toFun := fun z => (z.1 i).1
  continuous_toFun := by fun_prop

/-- The coordinate projections separate the compactified cylinder states by definition. -/
theorem wilsonCylinderCoordinateMap_injective
    {Ω : Type*} (raw : ℕ → Ω → ℝ) :
    Function.Injective
      (fun z : WilsonCylinderState raw =>
        fun i => wilsonCylinderCoordinate raw i z) := by
  intro x y hxy
  apply Subtype.ext
  funext i
  apply Subtype.ext
  exact congrFun hxy i

/-- Canonical merged D/F2 source on the cylinder compactification. -/
def wilsonCylinderDF2Source
    {Ω : Type*} (raw : ℕ → Ω → ℝ) :
    CountableWilsonDF2Source (WilsonCylinderState raw) where
  wilson := wilsonCylinderCoordinate raw
  coordinateMapInjective := wilsonCylinderCoordinateMap_injective raw

/-- Uniform density of the cylinder-coordinate algebra is now theorem-bearing. -/
theorem wilsonCylinderGeneratedAlgebra_dense
    {Ω : Type*} (raw : ℕ → Ω → ℝ) :
    (wilsonGeneratedAlgebra (wilsonCylinderCoordinate raw)).topologicalClosure = ⊤ :=
  (wilsonCylinderDF2Source raw).uniform_dense

end RequestProject.YangMills
