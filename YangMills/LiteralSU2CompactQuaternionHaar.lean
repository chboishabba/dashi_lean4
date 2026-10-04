import Mathlib
import Mathlib.Analysis.Quaternion
import Mathlib.Analysis.Normed.Field.UnitBall
import YangMills.LiteralSU2FourDimensionalLattice
import YangMills.FourDimensionalNativeHaarProductWeld

/-!
# Literal SU(2) quaternion carrier as a compact Haar group

This file closes the representation seam between the quaternion links used by
`LiteralSU2FourDimensionalLattice` and the compact-group Haar infrastructure.

The compact model is the unit sphere in Mathlib's normed quaternion division
ring.  The existing literal unit-quaternion structure is multiplicatively
identical to that sphere, so we build an exact `MulEquiv`, push normalized Haar
back to the literal carrier, and prove inversion invariance there.

No matrix surrogate or second lattice action is introduced.
-/

namespace RequestProject.YangMills

open scoped Quaternion

/-- The standard compact unit-quaternion group S^3. -/
abbrev SU2CompactQuaternion :=
  Metric.sphere (0 : Quaternion ℝ) 1

/-- Coordinates of the repository's literal quaternion as a Mathlib quaternion. -/
def literalSU2ToQuaternion (U : SU2PlaquetteHolonomy) : Quaternion ℝ :=
  ⟨U.a, U.b, U.c, U.d⟩

lemma literal_su2_to_quaternion_normSq
    (U : SU2PlaquetteHolonomy) :
    Quaternion.normSq (literalSU2ToQuaternion U) = 1 := by
  simpa [literalSU2ToQuaternion, Quaternion.normSq_def'] using U.unit_quaternion

lemma literal_su2_to_quaternion_norm
    (U : SU2PlaquetteHolonomy) :
    ‖literalSU2ToQuaternion U‖ = 1 := by
  have hs := Quaternion.normSq_eq_norm_mul_self (literalSU2ToQuaternion U)
  rw [literal_su2_to_quaternion_normSq U] at hs
  have hn : 0 ≤ ‖literalSU2ToQuaternion U‖ := norm_nonneg _
  nlinarith

/-- Exact embedding of the literal carrier into the compact unit sphere. -/
def literalSU2ToCompactQuaternion
    (U : SU2PlaquetteHolonomy) : SU2CompactQuaternion :=
  ⟨literalSU2ToQuaternion U,
    Metric.mem_sphere_zero_iff_norm.mpr (literal_su2_to_quaternion_norm U)⟩

/-- Read a compact unit quaternion back into the repository's literal carrier. -/
def literalSU2FromCompactQuaternion
    (q : SU2CompactQuaternion) : SU2PlaquetteHolonomy :=
  ⟨q.1.re, q.1.imI, q.1.imJ, q.1.imK, by
    have hn : ‖q.1‖ = 1 := Metric.mem_sphere_zero_iff_norm.mp q.2
    have hs := Quaternion.normSq_eq_norm_mul_self q.1
    rw [hn] at hs
    have hs' : Quaternion.normSq q.1 = 1 := by simpa using hs
    simpa [Quaternion.normSq_def'] using hs'⟩

@[simp] theorem literal_su2_from_to_compact
    (U : SU2PlaquetteHolonomy) :
    literalSU2FromCompactQuaternion (literalSU2ToCompactQuaternion U) = U := by
  apply su2_holonomy_ext <;> rfl

@[simp] theorem literal_su2_to_from_compact
    (q : SU2CompactQuaternion) :
    literalSU2ToCompactQuaternion (literalSU2FromCompactQuaternion q) = q := by
  apply Subtype.ext
  apply Quaternion.ext <;> rfl

/--
The literal repository group law is exactly Mathlib quaternion multiplication
restricted to the unit sphere.
-/
def literalSU2QuaternionGroupEquiv :
    SU2PlaquetteHolonomy ≃* SU2CompactQuaternion where
  toFun := literalSU2ToCompactQuaternion
  invFun := literalSU2FromCompactQuaternion
  left_inv := literal_su2_from_to_compact
  right_inv := literal_su2_to_from_compact
  map_mul' x y := by
    apply Subtype.ext
    apply Quaternion.ext <;> rfl

/-- The compact model really is compact. -/
instance : CompactSpace SU2CompactQuaternion :=
  inferInstanceAs (CompactSpace (Metric.sphere (0 : Quaternion ℝ) 1))

/-- The compact model uses the genuine nonabelian topological group structure. -/
instance : IsTopologicalGroup SU2CompactQuaternion :=
  inferInstanceAs (IsTopologicalGroup (Metric.sphere (0 : Quaternion ℝ) 1))

/-- The inverse carrier map is measurable for the pre-existing coordinate sigma algebra. -/
theorem literal_su2_from_compact_measurable :
    Measurable literalSU2FromCompactQuaternion := by
  fun_prop

/-- Inversion on the pre-existing literal measurable carrier is measurable. -/
theorem literal_su2_inv_measurable :
    Measurable (fun U : SU2PlaquetteHolonomy => U⁻¹) := by
  change Measurable (fun U : SU2PlaquetteHolonomy =>
    ⟨U.a, -U.b, -U.c, -U.d, by
      have h : U.a ^ 2 + (-U.b) ^ 2 + (-U.c) ^ 2 + (-U.d) ^ 2 =
          U.a ^ 2 + U.b ^ 2 + U.c ^ 2 + U.d ^ 2 := by ring
      rw [h, U.unit_quaternion]⟩)
  fun_prop

/-- Make the coordinate proof available to product-measure/fun_prop consumers. -/
instance : MeasurableInv SU2PlaquetteHolonomy where
  measurable_inv := literal_su2_inv_measurable

/--
Normalized compact Haar, transported to the exact literal unit-quaternion
carrier used by every Wilson link and plaquette theorem in this lane.
-/
noncomputable def literalSU2OneLinkHaar :
    MeasureTheory.ProbabilityMeasure SU2PlaquetteHolonomy :=
  (compactGroupNativeHaar SU2CompactQuaternion).map
    literalSU2FromCompactQuaternion

/-- Transport commutes exactly with inversion because the carrier equivalence is multiplicative. -/
theorem literal_su2_from_compact_inv
    (q : SU2CompactQuaternion) :
    literalSU2FromCompactQuaternion q⁻¹ =
      (literalSU2FromCompactQuaternion q)⁻¹ := by
  exact literalSU2QuaternionGroupEquiv.symm.map_inv q

/--
The literal one-link Haar law is inversion invariant.  This is the exact
one-link fact consumed by the selected time-reflection on temporal links.
-/
theorem literal_su2_one_link_haar_inversion_invariant :
    MeasureTheory.Measure.map (fun U : SU2PlaquetteHolonomy => U⁻¹)
      (((literalSU2OneLinkHaar :
        MeasureTheory.ProbabilityMeasure SU2PlaquetteHolonomy) :
        MeasureTheory.Measure SU2PlaquetteHolonomy))
    =
      (((literalSU2OneLinkHaar :
        MeasureTheory.ProbabilityMeasure SU2PlaquetteHolonomy) :
        MeasureTheory.Measure SU2PlaquetteHolonomy) := by
  let μ : MeasureTheory.Measure SU2CompactQuaternion :=
    ((compactGroupNativeHaar SU2CompactQuaternion :
      MeasureTheory.ProbabilityMeasure SU2CompactQuaternion) :
      MeasureTheory.Measure SU2CompactQuaternion)
  change MeasureTheory.Measure.map (fun U : SU2PlaquetteHolonomy => U⁻¹)
      (MeasureTheory.Measure.map literalSU2FromCompactQuaternion μ)
    = MeasureTheory.Measure.map literalSU2FromCompactQuaternion μ
  rw [MeasureTheory.Measure.map_map]
  · rw [show (fun U : SU2PlaquetteHolonomy => U⁻¹) ∘
        literalSU2FromCompactQuaternion =
        literalSU2FromCompactQuaternion ∘
          (fun q : SU2CompactQuaternion => q⁻¹) by
      funext q
      exact (literal_su2_from_compact_inv q).symm]
    rw [← MeasureTheory.Measure.map_map]
    · rw [compact_group_native_haar_inversion_invariant SU2CompactQuaternion]
    · exact literal_su2_from_compact_measurable.aemeasurable
    · fun_prop
  · exact literal_su2_inv_measurable.aemeasurable
  · exact literal_su2_from_compact_measurable.aemeasurable

end RequestProject.YangMills
