import Mathlib
import Mathlib.MeasureTheory.Group.Measure
import YangMills.LiteralSU2BoundaryPlaneHaarSplit

/-!
# Translation invariance of the literal SU(2) boundary Haar laws

The boundary-projection proof needs genuine Haar translation, not only
inversion invariance.  This file transports compact-group right invariance to
the exact literal unit-quaternion carrier and then lets mathlib's finite product
Haar instance lift it to the upper and lower boundary-plane fields.
-/

open MeasureTheory

namespace RequestProject.YangMills

/-- Quaternion multiplication is measurable for the literal coordinate sigma algebra. -/
theorem literal_su2_mul_measurable :
    Measurable (fun z : SU2PlaquetteHolonomy × SU2PlaquetteHolonomy => z.1 * z.2) := by
  change Measurable (fun z : SU2PlaquetteHolonomy × SU2PlaquetteHolonomy =>
    ⟨z.1.a*z.2.a - z.1.b*z.2.b - z.1.c*z.2.c - z.1.d*z.2.d,
     z.1.a*z.2.b + z.1.b*z.2.a + z.1.c*z.2.d - z.1.d*z.2.c,
     z.1.a*z.2.c - z.1.b*z.2.d + z.1.c*z.2.a + z.1.d*z.2.b,
     z.1.a*z.2.d + z.1.b*z.2.c - z.1.c*z.2.b + z.1.d*z.2.a,
     by
       have hNorm :
          (z.1.a*z.2.a - z.1.b*z.2.b - z.1.c*z.2.c - z.1.d*z.2.d)^2 +
          (z.1.a*z.2.b + z.1.b*z.2.a + z.1.c*z.2.d - z.1.d*z.2.c)^2 +
          (z.1.a*z.2.c - z.1.b*z.2.d + z.1.c*z.2.a + z.1.d*z.2.b)^2 +
          (z.1.a*z.2.d + z.1.b*z.2.c - z.1.c*z.2.b + z.1.d*z.2.a)^2 =
          (z.1.a^2 + z.1.b^2 + z.1.c^2 + z.1.d^2) *
          (z.2.a^2 + z.2.b^2 + z.2.c^2 + z.2.d^2) := by ring
       rw [z.1.unit_quaternion, z.2.unit_quaternion] at hNorm
       simpa using hNorm⟩)
  fun_prop

instance : MeasurableMul SU2PlaquetteHolonomy where
  measurable_mul := literal_su2_mul_measurable

instance : MeasurableInv SU2PlaquetteHolonomy where
  measurable_inv := literal_su2_inv_measurable

/-- The compact-to-literal carrier map respects multiplication. -/
theorem literal_su2_from_compact_mul
    (q r : SU2CompactQuaternion) :
    literalSU2FromCompactQuaternion (q * r) =
      literalSU2FromCompactQuaternion q * literalSU2FromCompactQuaternion r := by
  exact literalSU2QuaternionGroupEquiv.symm.map_mul q r

/-- Exact one-link literal Haar is right-translation invariant. -/
theorem literal_su2_one_link_haar_mul_right_invariant
    (g : SU2PlaquetteHolonomy) :
    Measure.map (fun U : SU2PlaquetteHolonomy => U * g)
      (((literalSU2OneLinkHaar : ProbabilityMeasure SU2PlaquetteHolonomy) :
        Measure SU2PlaquetteHolonomy)) =
      (((literalSU2OneLinkHaar : ProbabilityMeasure SU2PlaquetteHolonomy) :
        Measure SU2PlaquetteHolonomy) := by
  let μ : Measure SU2CompactQuaternion :=
    ((compactGroupNativeHaar SU2CompactQuaternion :
      ProbabilityMeasure SU2CompactQuaternion) : Measure SU2CompactQuaternion)
  letI : Measure.IsMulRightInvariant μ :=
    compact_group_native_haar_right_invariant SU2CompactQuaternion
  change Measure.map (fun U : SU2PlaquetteHolonomy => U * g)
      (Measure.map literalSU2FromCompactQuaternion μ) =
    Measure.map literalSU2FromCompactQuaternion μ
  rw [Measure.map_map]
  · rw [show
      (fun U : SU2PlaquetteHolonomy => U * g) ∘ literalSU2FromCompactQuaternion =
        literalSU2FromCompactQuaternion ∘
          (fun q : SU2CompactQuaternion => q * literalSU2ToCompactQuaternion g) by
      funext q
      simp [Function.comp_def, literal_su2_from_compact_mul]]
    rw [← Measure.map_map]
    · rw [MeasureTheory.map_mul_right_eq_self μ
        (literalSU2ToCompactQuaternion g)]
    · exact literal_su2_from_compact_measurable.aemeasurable
    · fun_prop
  · fun_prop
  · exact literal_su2_from_compact_measurable.aemeasurable

instance literalSU2OneLinkHaarIsMulRightInvariant :
    Measure.IsMulRightInvariant
      (((literalSU2OneLinkHaar : ProbabilityMeasure SU2PlaquetteHolonomy) :
        Measure SU2PlaquetteHolonomy)) where
  map_mul_right_eq_self := literal_su2_one_link_haar_mul_right_invariant

/-- Upper boundary-plane product Haar is invariant under pointwise right translation. -/
theorem literal_su2_upper_boundary_haar_mul_right_invariant
    (n : ℕ) [NeZero n]
    (g : SU2UpperBoundaryTemporalLinks n) :
    Measure.map
      (fun b : SU2UpperBoundaryTemporalLinks n => fun p => b p * g p)
      (literalSU2UpperBoundaryTemporalHaar n) =
      literalSU2UpperBoundaryTemporalHaar n := by
  simpa [literalSU2UpperBoundaryTemporalHaar] using
    (MeasureTheory.map_mul_right_eq_self
      (literalSU2UpperBoundaryTemporalHaar n) g)

/-- Lower boundary-plane product Haar is invariant under pointwise right translation. -/
theorem literal_su2_lower_boundary_haar_mul_right_invariant
    (n : ℕ) [NeZero n]
    (g : SU2LowerBoundaryTemporalLinks n) :
    Measure.map
      (fun b : SU2LowerBoundaryTemporalLinks n => fun p => b p * g p)
      (literalSU2LowerBoundaryTemporalHaar n) =
      literalSU2LowerBoundaryTemporalHaar n := by
  simpa [literalSU2LowerBoundaryTemporalHaar] using
    (MeasureTheory.map_mul_right_eq_self
      (literalSU2LowerBoundaryTemporalHaar n) g)

end RequestProject.YangMills
