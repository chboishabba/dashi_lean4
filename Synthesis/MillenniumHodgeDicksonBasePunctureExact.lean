import Synthesis.MillenniumHodgeDicksonActualPuncturedChartExact

/-! The actual source puncture is the inverse image of a base
principal open. This matters for properness: deleting an arbitrary
open subset of the source of a proper map need not preserve
properness. Here the squared denominator is literally from the base.
No projective closure or primitive pairing is claimed. -/
namespace DASHI.Hodge.DicksonCoupled
open scoped BigOperators
noncomputable section

def baseFoldDiscriminant (i : Address) : CoupledSurfaceBase :=
  baseX i^2-4*baseA i

def baseChartDenominator : CoupledSurfaceBase :=
  baseEta^6*baseDelta^2*
    ∏ i : Address,baseA i^2*baseFoldDiscriminant i

theorem fold_discriminant_identity {R : Type*} [CommRing R]
    (a x v : R) (h : v^2-x*v+a=0) :
    (v^2-a)^2=v^2*(x^2-4*a) := by
  linear_combination (v^2+x*v+a)*h

theorem actualChartDenominator_square :
    chartDenominator^2=algebraMap CoupledSurfaceBase ActualCoupledFoldAlgebra
      baseChartDenominator := by
  let f := algebraMap CoupledSurfaceBase ActualCoupledFoldAlgebra
  let v := foldCoord baseA baseX baseEta
  have h (i : Address) : (v i^2-f (baseA i))^2=
      v i^2*(f (baseX i)^2-4*f (baseA i)) :=
    fold_discriminant_identity _ _ _ (foldCoord_relation baseA baseX baseEta i)
  have hp : (∏ i,v i)=f baseEta := foldCoord_product baseA baseX baseEta
  have hf (i : Address) :
      (f (baseA i)*v i*(v i^2-f (baseA i)))^2=
      v i^4*f (baseA i^2*baseFoldDiscriminant i) := by
    rw [mul_pow,mul_pow,h i]
    simp [baseFoldDiscriminant,map_sub,map_mul,map_pow]
    ring
  change (f baseEta*f baseDelta*∏ i : Address,
    f (baseA i)*v i*(v i^2-f (baseA i)))^2=f baseChartDenominator
  rw [mul_pow,mul_pow,← Finset.prod_pow]
  simp_rw [hf,Finset.prod_mul_distrib,Finset.prod_pow,hp]
  simp [baseChartDenominator,map_mul,map_pow,map_prod]
  ring

/-- Pointwise nonzero on the source iff nonzero on the base. Thus the
puncture is exactly the inverse image of the base principal open.
This identity holds for every geometric point, not only the sample. -/
theorem actualChartDenominator_nonzero_iff {F : Type*} [Field F]
    (p : ActualCoupledFoldAlgebra →+* F) :
    p chartDenominator≠0 ↔
      p (algebraMap CoupledSurfaceBase ActualCoupledFoldAlgebra baseChartDenominator)≠0 := by
  rw [← actualChartDenominator_square,map_pow,pow_ne_zero_iff (by decide : (2:ℕ)≠0)]

/-- At the ring level the same unit test includes nonreduced fibres. -/
theorem actualChartDenominator_unit_iff {R : Type*} [CommRing R]
    (p : ActualCoupledFoldAlgebra →+* R) :
    IsUnit (p chartDenominator) ↔
      IsUnit (p (algebraMap CoupledSurfaceBase ActualCoupledFoldAlgebra baseChartDenominator)) := by
  rw [← actualChartDenominator_square,map_pow,pow_two,isUnit_mul]
  simp

end
end DASHI.Hodge.DicksonCoupled
