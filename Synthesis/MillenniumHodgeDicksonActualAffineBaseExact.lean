import Synthesis.MillenniumHodgeDicksonCoupledAffineSchemeExact

/-! Literal affine base of the six coupled Dickson surface equations
and derivative product, over Q. This defines a universal coordinate
algebra, not a selected geometric point. CoupledFoldAlgebra then
imposes the rotation product eta and six monic fold equations.
Open-chart localization and saturation/projective closure, irreducible
cycle and primitive pairing remain separate.
-/
namespace DASHI.Hodge.DicksonCoupled
open AlgebraicGeometry
open scoped BigOperators
noncomputable section

inductive SurfaceCoord where
  | a (i : Address)
  | x (i : Address)
  | s (i : Address)
  | eta
  | delta
  deriving DecidableEq

abbrev SurfacePoly := MvPolynomial SurfaceCoord ℚ

def surfaceA (i : Address) : SurfacePoly := MvPolynomial.X (.a i)
def surfaceX (i : Address) : SurfacePoly := MvPolynomial.X (.x i)
def surfaceS (i : Address) : SurfacePoly := MvPolynomial.X (.s i)

def surfaceRelation (i : Address) : SurfacePoly :=
  let a := surfaceA i
  let x := surfaceX i
  let s := surfaceS i
  x^7-7*a*x^5+14*a^2*x^3-7*a^3*x-
    (-3*a^3-3*a^2*s-a^2+3*a*s+3*a-2*s^2+s+3)

def surfaceDerivative (i : Address) : SurfacePoly :=
  -3*(surfaceA i)^2+3*surfaceA i+1-4*surfaceS i

def coupledSurfaceIdeal : Ideal SurfacePoly :=
  Ideal.span (Set.range surfaceRelation ∪
    { (∏ i : Address,surfaceDerivative i)-MvPolynomial.X .delta })

abbrev CoupledSurfaceBase := SurfacePoly ⧸ coupledSurfaceIdeal

def baseA (i : Address) : CoupledSurfaceBase := Ideal.Quotient.mk _ (surfaceA i)
def baseX (i : Address) : CoupledSurfaceBase := Ideal.Quotient.mk _ (surfaceX i)
def baseS (i : Address) : CoupledSurfaceBase := Ideal.Quotient.mk _ (surfaceS i)
def baseEta : CoupledSurfaceBase := Ideal.Quotient.mk _ (MvPolynomial.X .eta)
def baseDelta : CoupledSurfaceBase := Ideal.Quotient.mk _ (MvPolynomial.X .delta)

theorem actualBaseSurfaceRelation (i : Address) :
    baseX i^7-7*baseA i*baseX i^5+14*(baseA i)^2*baseX i^3-7*(baseA i)^3*baseX i=
      -3*(baseA i)^3-3*(baseA i)^2*baseS i-(baseA i)^2+
      3*baseA i*baseS i+3*baseA i-2*(baseS i)^2+baseS i+3 := by
  have h : surfaceRelation i∈coupledSurfaceIdeal :=
    Ideal.subset_span (Or.inl ⟨i,rfl⟩)
  apply sub_eq_zero.mp
  simpa [surfaceRelation,baseA,baseX,baseS] using (Ideal.Quotient.eq_zero_iff_mem.mpr h)

theorem actualBaseDerivativeProduct :
    (∏ i : Address,-3*(baseA i)^2+3*baseA i+1-4*baseS i)=baseDelta := by
  have h : (∏ i : Address,surfaceDerivative i)-MvPolynomial.X .delta∈coupledSurfaceIdeal :=
    Ideal.subset_span (Or.inr rfl)
  apply sub_eq_zero.mp
  simpa [surfaceDerivative,baseA,baseS,baseDelta] using (Ideal.Quotient.eq_zero_iff_mem.mpr h)

abbrev ActualCoupledFoldAlgebra := CoupledFoldAlgebra baseA baseX baseEta

def actualCoupledAffineProjection :=
  coupledFoldProjection baseA baseX baseEta

theorem actualCoupledAffineProjection_proper :
    IsProper actualCoupledAffineProjection :=
  coupledFoldProjection_proper baseA baseX baseEta

end
end DASHI.Hodge.DicksonCoupled
