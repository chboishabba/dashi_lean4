import Mathlib

/-!
# Audit of the pinned donor's Albert determinant cross term

The pinned external donor defines the cubic cross term (in upper-entry
coordinates `p = x01`, `q = x02`, `t = x12`) as

  2 Re(t * (q * star p)).

Before using that expression as the Albert/Freudenthal norm, test it on the
associative complex subalgebra.  For a Hermitian 3x3 matrix with zero diagonal
and upper entries p,q,t, ordinary determinant expansion gives

  p*t*conj(q) + q*conj(p)*conj(t)
    = 2 Re(p*t*conj(q)).

The explicit Gaussian-integer example

  p = 1+i, q = 1+2i, t = 2+3i

has ordinary Hermitian determinant 18, while the donor cross-term orientation
gives 6.  Therefore the pinned source formula cannot be promoted to the
canonical Albert determinant without repair or an explanation of a different
coordinate convention that changes the matrix entries themselves.

This file uses only integer-pair complex arithmetic; it does not import the
external package and so the counterexample is independent of the toolchain
compatibility seam.
-/

namespace Integration.AlbertDonorDeterminantAudit

abbrev Gaussian := Int × Int

def gadd (x y : Gaussian) : Gaussian := (x.1 + y.1, x.2 + y.2)
def gmul (x y : Gaussian) : Gaussian :=
  (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1)
def gconj (x : Gaussian) : Gaussian := (x.1, -x.2)
def gre (x : Gaussian) : Int := x.1

/-- Determinant of the zero-diagonal Hermitian matrix

  [ 0      p      q ]
  [ p*     0      t ]
  [ q*     t*     0 ]

expanded in the associative Gaussian subalgebra. -/
def hermitianZeroDiagonalDet (p q t : Gaussian) : Gaussian :=
  gadd (gmul p (gmul t (gconj q)))
       (gmul q (gmul (gconj p) (gconj t)))

/-- Cross term used by the pinned donor's current `det` source. -/
def donorCrossTerm (p q t : Gaussian) : Int :=
  2 * gre (gmul t (gmul q (gconj p)))

def pExample : Gaussian := (1, 1)
def qExample : Gaussian := (1, 2)
def tExample : Gaussian := (2, 3)

/-- Ground-truth associative Hermitian determinant for the explicit example. -/
theorem hermitian_example_det_18 :
    hermitianZeroDiagonalDet pExample qExample tExample = (18, 0) := by
  norm_num [hermitianZeroDiagonalDet, pExample, qExample, tExample,
    gadd, gmul, gconj]

/-- The donor's current cross-term orientation evaluates to 6 on the same
entries. -/
theorem donor_example_cross_6 :
    donorCrossTerm pExample qExample tExample = 6 := by
  norm_num [donorCrossTerm, pExample, qExample, tExample, gre, gmul, gconj]

/-- Exact mismatch: the donor expression is not the ordinary Hermitian
3x3 determinant even on the associative complex subalgebra. -/
theorem donor_cross_term_mismatch :
    donorCrossTerm pExample qExample tExample ≠
      (hermitianZeroDiagonalDet pExample qExample tExample).1 := by
  norm_num [donorCrossTerm, hermitianZeroDiagonalDet,
    pExample, qExample, tExample, gre, gadd, gmul, gconj]

/-- Candidate corrected associative cross term in upper-entry coordinates. -/
def associativeHermitianCrossTerm (p q t : Gaussian) : Int :=
  2 * gre (gmul p (gmul t (gconj q)))

theorem corrected_example_cross_18 :
    associativeHermitianCrossTerm pExample qExample tExample = 18 := by
  norm_num [associativeHermitianCrossTerm, pExample, qExample, tExample,
    gre, gmul, gconj]

structure Boundary where
  donorCrossTermSourceAudited : Bool
  associativeComplexCounterexamplePaid : Bool
  donorCurrentDetPromotableAsAlbertNorm : Bool
  correctedOrientationFullyProvedForOctonions : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  donorCrossTermSourceAudited := true
  associativeComplexCounterexamplePaid := true
  donorCurrentDetPromotableAsAlbertNorm := false
  correctedOrientationFullyProvedForOctonions := false

end Integration.AlbertDonorDeterminantAudit
