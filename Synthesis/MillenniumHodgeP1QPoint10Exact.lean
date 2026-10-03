import Synthesis.MillenniumHodgeP1QStructureMapExact
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-!
# Hodge max-cut: the actual rational point [1:0] on P¹_Q

This owner constructs `[1:0]` directly through Mathlib's genuine
`Proj.fromOfGlobalSections` API.  The homogeneous-coordinate evaluation

  X₀ ↦ 1,   X₁ ↦ 0

lands in the global sections of `Spec Q`.  Since `X₀` belongs to the
irrelevant ideal and evaluates to one, the image of the irrelevant ideal is
the unit ideal, exactly the hypothesis required by `fromOfGlobalSections`.

No synthetic projective-point carrier is introduced.
-/

namespace Synthesis.Millennium.Hodge

open AlgebraicGeometry
open CategoryTheory
open MvPolynomial

noncomputable section

/-- The homogeneous-coordinate evaluation underlying `[1:0]`. -/
def p1QPoint10Eval : P1QCoordinateRing →+* ℚ :=
  MvPolynomial.eval₂Hom (RingHom.id ℚ)
    (fun i : Fin 2 => if i = 0 then 1 else 0)

@[simp] theorem p1QPoint10Eval_X0 :
    p1QPoint10Eval (MvPolynomial.X (0 : Fin 2)) = 1 := by
  simp [p1QPoint10Eval]

@[simp] theorem p1QPoint10Eval_X1 :
    p1QPoint10Eval (MvPolynomial.X (1 : Fin 2)) = 0 := by
  simp [p1QPoint10Eval]

/-- Evaluation followed by the canonical inverse Γ(Spec Q) ≅ Q. -/
def p1QPoint10GlobalSections :
    P1QCoordinateRing →+* Γ(Spec (.of ℚ), ⊤) :=
  (Scheme.ΓSpecIso (.of ℚ)).inv.hom.comp p1QPoint10Eval

/-- `X₀` is a positive-degree homogeneous element, hence belongs to the
irrelevant ideal. -/
theorem p1Q_X0_mem_irrelevant :
    MvPolynomial.X (0 : Fin 2) ∈
      (HomogeneousIdeal.irrelevant P1QGrading).toIdeal := by
  exact HomogeneousIdeal.mem_irrelevant_of_mem
    (by norm_num : 0 < (1 : ℕ))
    (by
      simpa [P1QGrading] using
        (MvPolynomial.isHomogeneous_X (R := ℚ) (0 : Fin 2)))

/-- The coordinate evaluation sends the irrelevant ideal onto the unit ideal,
because the irrelevant element `X₀` maps to one. -/
theorem p1QPoint10_irrelevant_maps_top :
    (HomogeneousIdeal.irrelevant P1QGrading).toIdeal.map
      p1QPoint10GlobalSections = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have hx := Ideal.mem_map_of_mem p1QPoint10GlobalSections p1Q_X0_mem_irrelevant
  simpa [p1QPoint10GlobalSections, p1QPoint10Eval] using hx

/-- The literal scheme morphism represented by the rational homogeneous point
`[1:0]`. -/
def p1QPoint10 :
    Spec (.of ℚ) ⟶ P1QScheme :=
  Proj.fromOfGlobalSections P1QGrading
    p1QPoint10GlobalSections p1QPoint10_irrelevant_maps_top

/-- On the degree-zero subring, `[1:0]` evaluation is exactly the already-paid
constant-coefficient map. -/
theorem p1QPoint10Eval_gradeZero
    (p : P1QGrading 0) :
    p1QPoint10Eval p.1 = p1QGradeZeroToRat p := by
  have hp : p.1 = MvPolynomial.C (p.1.coeff 0) := by
    apply (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp
    exact (MvPolynomial.totalDegree_zero_iff_isHomogeneous).mpr p.2
  rw [hp]
  simp [p1QPoint10Eval, p1QGradeZeroToRat]

/-- The induced ring map from the grade-zero piece is exactly the paid
identification with Q. -/
theorem p1QPoint10Eval_comp_gradeZero :
    p1QPoint10Eval.comp (algebraMap (P1QGrading 0) P1QCoordinateRing) =
      p1QGradeZeroToRat := by
  ext p
  exact p1QPoint10Eval_gradeZero p

/-- `[1:0]` is a genuine section of the displayed P¹_Q structure morphism.
The proof is the library formula for `fromOfGlobalSections` followed by the
paid degree-zero ring identification and the Γ-Spec triangle identity. -/
theorem p1QPoint10_isSection :
    p1QPoint10 ≫ p1QToSpecQ = 𝟙 (Spec (.of ℚ)) := by
  rw [p1QToSpecQ, Category.assoc]
  rw [Proj.fromOfGlobalSections_toSpecZero]
  rw [← Spec.map_comp_assoc]
  simp only [p1QPoint10GlobalSections, CommRingCat.ofHom_comp]
  rw [p1QPoint10Eval_comp_gradeZero]
  simp [p1QGradeZeroSpecIso]

/-!
MAX-CUT STATUS

PAID HERE (subject to exact-head kernel certification):
* the literal coordinate evaluation X₀↦1, X₁↦0;
* irrelevant-ideal image = top on the genuine homogeneous coordinate ring;
* `[1:0] : Spec Q ⟶ P1QScheme` through `Proj.fromOfGlobalSections`;
* its restriction to the grade-zero ring is exactly the previously-paid
  `(P1QGrading 0) ≃+* Q` map;
* `[1:0]` is a section of the displayed structure morphism.

NEXT:
* instantiate `relativeRulingOne` and `relativeRulingTwo` using this section;
* define the corresponding genuine algebraic cycles and prove factor-swap
  exchange / the (-1)-eigencycle.
-/

end

end Synthesis.Millennium.Hodge
