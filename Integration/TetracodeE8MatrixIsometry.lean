import Mathlib

/-!
# Exact matrix isometry behind the tetracode/E8 construction

DASHI derivation around the explicit external 8x8 matrix used to identify the
four-coordinate Eisenstein tetracode lattice with the standard real E8 lattice.

Rather than treating the finite 240-root equality as an isolated computation,
this owner proves the ambient bilinear identity

  M^T M = 12 * G_E,

where `G_E` is four copies of the doubled Eisenstein Gram matrix
`[[2,-1],[-1,2]]`.  Thus the explicit linear map is a scaled isometry on the
whole ambient carrier.  Lattice membership / tetracode admission remains a
separate finite arithmetic obligation.
-/

namespace Integration.TetracodeE8MatrixIsometry

structure R8 where
  x0 : ℝ
  x1 : ℝ
  x2 : ℝ
  x3 : ℝ
  x4 : ℝ
  x5 : ℝ
  x6 : ℝ
  x7 : ℝ
  deriving Repr

private def m0 (v : R8) : ℝ := 3*v.x4 + 3*v.x6
private def m1 (v : R8) : ℝ := -2*v.x2 - 2*v.x3 + v.x4 - 2*v.x5 + v.x6 - 2*v.x7
private def m2 (v : R8) : ℝ := -2*v.x2 + 4*v.x3 + v.x4 - 2*v.x5 + v.x6 - 2*v.x7
private def m3 (v : R8) : ℝ := 4*v.x2 - 2*v.x3 + v.x4 - 2*v.x5 + v.x6 - 2*v.x7
private def m4 (v : R8) : ℝ := 3*v.x4 - 3*v.x6
private def m5 (v : R8) : ℝ := -2*v.x0 - 2*v.x1 + v.x4 - 2*v.x5 - v.x6 + 2*v.x7
private def m6 (v : R8) : ℝ := -2*v.x0 + 4*v.x1 + v.x4 - 2*v.x5 - v.x6 + 2*v.x7
private def m7 (v : R8) : ℝ := 4*v.x0 - 2*v.x1 + v.x4 - 2*v.x5 - v.x6 + 2*v.x7

/-- Euclidean pairing after applying the integer matrix `M`. -/
def mappedPair (v w : R8) : ℝ :=
  m0 v * m0 w + m1 v * m1 w + m2 v * m2 w + m3 v * m3 w
  + m4 v * m4 w + m5 v * m5 w + m6 v * m6 w + m7 v * m7 w

/-- Four-copy doubled Eisenstein bilinear pairing. -/
def eisensteinPair (v w : R8) : ℝ :=
  (2*v.x0*w.x0 - v.x0*w.x1 - v.x1*w.x0 + 2*v.x1*w.x1)
  + (2*v.x2*w.x2 - v.x2*w.x3 - v.x3*w.x2 + 2*v.x3*w.x3)
  + (2*v.x4*w.x4 - v.x4*w.x5 - v.x5*w.x4 + 2*v.x5*w.x5)
  + (2*v.x6*w.x6 - v.x6*w.x7 - v.x7*w.x6 + 2*v.x7*w.x7)

/-- Polynomial form of `M^T M = 12 G_E`. -/
theorem matrix_isometry (v w : R8) :
    mappedPair v w = 12 * eisensteinPair v w := by
  rcases v with ⟨a,b,c,d,e,f,g,h⟩
  rcases w with ⟨A,B,C,D,E,F,G,H⟩
  simp [mappedPair, eisensteinPair, m0, m1, m2, m3, m4, m5, m6, m7]
  ring

/-- Quadratic specialization of the bilinear identity. -/
def mappedNorm (v : R8) : ℝ := mappedPair v v

def eisensteinNorm4 (v : R8) : ℝ := eisensteinPair v v

theorem matrix_norm_isometry (v : R8) :
    mappedNorm v = 12 * eisensteinNorm4 v := by
  exact matrix_isometry v v

/-- After dividing the explicit matrix by 6, Euclidean norm is one third of the
`eisensteinPair` normalization used here.  The finite minimal shell has
`eisensteinPair v v = 6`, hence standard E8 norm squared `2`. -/
theorem scaled_map_norm_two_of_eisenstein_six
    (v : R8) (h : eisensteinNorm4 v = 6) :
    (mappedNorm v) / 36 = 2 := by
  rw [matrix_norm_isometry, h]
  norm_num

structure Boundary where
  ambientScaledIsometryKernelTheoremSourceWritten : Bool
  tetracodeAdmissionProvedHere : Bool
  finite240ImageEqualityProvedHere : Bool
  relativeT5IdentifiedHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  ambientScaledIsometryKernelTheoremSourceWritten := true
  tetracodeAdmissionProvedHere := false
  finite240ImageEqualityProvedHere := false
  relativeT5IdentifiedHere := false

end Integration.TetracodeE8MatrixIsometry
