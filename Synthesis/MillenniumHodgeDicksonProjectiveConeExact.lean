import Synthesis.MillenniumHodgeDicksonAffineSaturationExact

namespace DASHI.Hodge.DicksonCoupled
open Polynomial
noncomputable section

/-- Full original affine coordinates over Q (not merely the six
fold variables relative to the base). The extra none coordinate is
the homogenizing coordinate. -/
abbrev OriginalCoord := Sum SurfaceCoord Address
abbrev ProjectiveAmbientPoly := MvPolynomial (Option OriginalCoord) ℚ

def originalOpenCoord : OriginalCoord → ActualSourceOpen
  | .inl i => algebraMap ActualCoupledFoldAlgebra ActualSourceOpen
      (algebraMap CoupledSurfaceBase ActualCoupledFoldAlgebra
        (Ideal.Quotient.mk coupledSurfaceIdeal (MvPolynomial.X i)))
  | .inr i => algebraMap ActualCoupledFoldAlgebra ActualSourceOpen
      (foldCoord baseA baseX baseEta i)

def actualConeMap : ProjectiveAmbientPoly →+* Polynomial ActualSourceOpen :=
  MvPolynomial.eval₂Hom
    (Polynomial.C.comp (algebraMap ℚ ActualSourceOpen))
    (fun i => match i with
      | none => Polynomial.X
      | some j => Polynomial.C (originalOpenCoord j)*Polynomial.X)

def actualConeIdeal : Ideal ProjectiveAmbientPoly := RingHom.ker actualConeMap

theorem actualConeMap_h :
    actualConeMap (MvPolynomial.X none)=Polynomial.X := by
  simp [actualConeMap]

theorem actualConeMap_coord (i : OriginalCoord) :
    actualConeMap (MvPolynomial.X (some i))=
      Polynomial.C (originalOpenCoord i)*Polynomial.X := by
  simp [actualConeMap]

/-- X is regular even over the possibly nonreduced actual open ring. -/
theorem actualCone_X_regular (p : Polynomial ActualSourceOpen)
    (h : Polynomial.X*p=0) : p=0 := by
  ext n
  have he := congrArg (fun q : Polynomial ActualSourceOpen=>q.coeff (n+1)) h
  simpa using he

/-- The schematic cone ideal admits no extra component supported only
at the homogenizing hyperplane, expressed by exact saturation. -/
theorem actualCone_h_saturated (p : ProjectiveAmbientPoly) (n : ℕ) :
    (MvPolynomial.X none)^n*p∈actualConeIdeal ↔ p∈actualConeIdeal := by
  change actualConeMap ((MvPolynomial.X none)^n*p)=0 ↔ actualConeMap p=0
  rw [map_mul,map_pow,actualConeMap_h]
  constructor
  · intro h
    induction n with
    | zero => simpa using h
    | succ n ih =>
      apply ih
      apply actualCone_X_regular
      simpa [pow_succ',mul_assoc] using h
  · intro h
    rw [h,mul_zero]

/-- At h=1 the original coordinate is recovered without discarding
the base coordinates or nilpotent information. -/
theorem actualCone_coord_at_one (i : OriginalCoord) :
    (actualConeMap (MvPolynomial.X (some i))).eval 1=originalOpenCoord i := by
  rw [actualConeMap_coord]
  simp

end
end DASHI.Hodge.DicksonCoupled
