import Jordan.AlbertAlgebra
import ExternalAlbert.RealAlbertAdapterProbe

/-!
# Corrected standard cubic on the external H3(O) carrier

The pinned donor's current `det` cross-term fails an associative-complex
Hermitian determinant check.  The carrier, `albertEquiv`, and Jordan product are
still useful.  This probe therefore defines the standard cubic independently
from the public `3 + 8 + 8 + 8` coordinates, using exactly the orientation of
the repo-native rational Agda Albert construction.

This file remains outside the ordinary DASHI rollup until the external package
compatibility seam is crossed.
-/

namespace ExternalAlbert.CorrectedRealAlbertCubicProbe

open ExternalAlbert.RealAlbertAdapterProbe

abbrev O := Octonion ℝ (-1 : ℝ) (-1 : ℝ) (1 : ℝ)

/-- Quadratic octonion norm in the donor coordinate convention. -/
def octNormSq (x : O) : ℝ := (x * star x).1.re

/-- Real part of a left-associated octonion triple product. -/
def tripleReal (x y z : O) : ℝ := ((x * y) * z).1.re

/-- Public additive coordinates of one Hermitian matrix. -/
noncomputable def coords (X : RealAlbert) :=
  Octonion.albertEquiv X

/-- Standard Freudenthal/Albert cubic in the donor's upper-entry convention
`(x01,x02,x12)`.  It is the direct translation of the repo-native Agda formula
with `z=x01`, `conj(y)=x02`, `x=x12`. -/
noncomputable def correctedCubic (X : RealAlbert) : ℝ :=
  let q := coords X
  let a := q.1 0
  let b := q.1 1
  let c := q.1 2
  let x01 := q.2.1
  let x02 := q.2.2.1
  let x12 := q.2.2.2
  a * b * c
    - a * octNormSq x12
    - b * octNormSq x02
    - c * octNormSq x01
    + 2 * tripleReal x12 (star x02) x01

/-- Exact semantic boundary: the corrected cubic is deliberately independent
of the donor's current `realDetTrace.det`. -/
inductive CorrectedCubicEqualsDonorDetWithoutProof : Prop

theorem corrected_cubic_not_promoted_to_donor_det :
    ¬ CorrectedCubicEqualsDonorDetWithoutProof := by
  intro h; cases h

structure Boundary where
  donorCarrierReused : Bool
  donorJordanProductReused : Bool
  donorCurrentDetQuarantined : Bool
  correctedStandardCubicSourceWritten : Bool
  correctedCubicUnitProofPendingKernel : Bool
  correctedCubicHomogeneityProofPendingKernel : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  donorCarrierReused := true
  donorJordanProductReused := true
  donorCurrentDetQuarantined := true
  correctedStandardCubicSourceWritten := true
  correctedCubicUnitProofPendingKernel := true
  correctedCubicHomogeneityProofPendingKernel := true

#check correctedCubic

end ExternalAlbert.CorrectedRealAlbertCubicProbe
