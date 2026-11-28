import Synthesis.MillenniumHodgeDicksonAffineFiniteProperExact
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! The universal coupled affine fold, not just a finite family of
geometric points. The six base surface coordinates and product
address are retained in R. Impose the actual monic fold and product
equations in the polynomial algebra, including nonreduced fibres.
The base may itself be the quotient imposing the Dickson surface
and derivative-product equations. Global projective closure and
Chow/primitive identification are not supplied by affine properness.
-/
namespace DASHI.Hodge.DicksonCoupled
open AlgebraicGeometry CategoryTheory
open scoped BigOperators
noncomputable section
variable {R : Type*} [CommRing R]

def foldRelation (a x : Address → R) (i : Address) : MvPolynomial Address R :=
  MvPolynomial.X i^2-MvPolynomial.C (x i)*MvPolynomial.X i+MvPolynomial.C (a i)

def coupledFoldIdeal (a x : Address → R) (η : R) : Ideal (MvPolynomial Address R) :=
  Ideal.span (Set.range (foldRelation a x) ∪
    { (∏ i : Address,MvPolynomial.X i)-MvPolynomial.C η })

abbrev CoupledFoldAlgebra (a x : Address → R) (η : R) :=
  MvPolynomial Address R ⧸ coupledFoldIdeal a x η

def foldCoord (a x : Address → R) (η : R) (i : Address) : CoupledFoldAlgebra a x η :=
  Ideal.Quotient.mk _ (MvPolynomial.X i)

theorem foldCoord_relation (a x : Address → R) (η : R) (i : Address) :
    foldCoord a x η i^2-algebraMap R (CoupledFoldAlgebra a x η) (x i)*foldCoord a x η i+
      algebraMap R (CoupledFoldAlgebra a x η) (a i)=0 := by
  have h : foldRelation a x i∈coupledFoldIdeal a x η :=
    Ideal.subset_span (Or.inl ⟨i,rfl⟩)
  have he := Ideal.Quotient.eq_zero_iff_mem.mpr h
  simpa [foldRelation,foldCoord,← Ideal.Quotient.mk_algebraMap] using he

theorem foldCoord_product (a x : Address → R) (η : R) :
    (∏ i,foldCoord a x η i)=algebraMap R (CoupledFoldAlgebra a x η) η := by
  have h : (∏ i : Address,MvPolynomial.X i)-MvPolynomial.C η∈coupledFoldIdeal a x η :=
    Ideal.subset_span (Or.inr rfl)
  have he := Ideal.Quotient.eq_zero_iff_mem.mpr h
  apply sub_eq_zero.mp
  simpa [foldCoord,← Ideal.Quotient.mk_algebraMap] using he

theorem coupledFold_generated (a x : Address → R) (η : R) :
    Algebra.adjoin R (Set.range (foldCoord a x η))=⊤ := by
  classical
  let A := CoupledFoldAlgebra a x η
  let S : Subalgebra R A := Algebra.adjoin R (Set.range (foldCoord a x η))
  apply top_unique
  intro q _
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective q
  induction p using MvPolynomial.induction_on with
  | C c => exact S.algebraMap_mem c
  | add p q hp hq => simpa only [map_add] using S.add_mem hp hq
  | mul_X p i hp =>
    simpa only [map_mul] using S.mul_mem hp (Algebra.subset_adjoin ⟨i,rfl⟩)

theorem coupledFold_finite (a x : Address → R) (η : R) :
    Module.Finite R (CoupledFoldAlgebra a x η) := by
  let A := CoupledFoldAlgebra a x η
  let S : Subalgebra R A := rotationChartRing (R:=R) (foldCoord a x η)
  letI : Module.Finite R S := rotationChart_finite a x (foldCoord a x η)
    (foldCoord_relation a x η)
  apply Module.Finite.of_surjective S.val.toLinearMap
  intro q
  refine ⟨⟨q,?_⟩,rfl⟩
  change q∈Algebra.adjoin R (Set.range (foldCoord a x η))
  rw [coupledFold_generated]
  trivial

def coupledFoldProjection (a x : Address → R) (η : R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (CoupledFoldAlgebra a x η)))

theorem coupledFoldProjection_proper (a x : Address → R) (η : R) :
    IsProper (coupledFoldProjection a x η) := by
  letI : Module.Finite R (CoupledFoldAlgebra a x η) := coupledFold_finite a x η
  letI : IsFinite (coupledFoldProjection a x η) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  infer_instance

end
end DASHI.Hodge.DicksonCoupled
