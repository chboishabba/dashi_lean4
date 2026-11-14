import Mathlib.Tactic
import Synthesis.RiemannG21SixTermDeterminantBound

/-!
# G21 support-only determinant polynomial

This proves the real ordered-field majorant behind the Agda normalized radius
gate.  With

  A1 = 6 N1 + N3,
  A2 = 12 N1 + 8 N3,
  c  = N5/20,

and compact-support bounds

  N3 <= R^2 N1,
  N5 <= R^4 N1,

the six-term determinant coefficient satisfies

  C <= (N1(a) N1(p) / 25)
         * (510 R^4 + 100 R^6 + 4 R^8).

The constants 510,100,4 therefore are not merely ledger bookkeeping; they are
the exact normalization of the six-term coefficient after support domination.
-/

namespace Synthesis

/-- Historical support-only polynomial. -/
-- Reuses the definition from `RiemannG21OddRatioGapRadiusGate`.

/-- Exact support-polynomial majorant for the determinant error constant. -/
theorem determinantErrorConstant_le_supportPolynomial
    {R n1a n3a n5a n1p n3p n5p : ℝ}
    (hR : 0 <= R)
    (h1a : 0 <= n1a) (h3a0 : 0 <= n3a) (h5a0 : 0 <= n5a)
    (h1p : 0 <= n1p) (h3p0 : 0 <= n3p) (h5p0 : 0 <= n5p)
    (h3a : n3a <= R^2*n1a) (h5a : n5a <= R^4*n1a)
    (h3p : n3p <= R^2*n1p) (h5p : n5p <= R^4*n1p) :
    determinantErrorConstant
      (6*n1a+n3a) (12*n1a+8*n3a)
      (6*n1p+n3p) (12*n1p+8*n3p)
      (n5a/20) (n5p/20)
      <= (n1a*n1p/25) * g21OddSupportPolynomial R := by
  have hR2 : 0 <= R^2 := sq_nonneg R
  have hR4 : 0 <= R^4 := by positivity
  have hA1a0 : 0 <= 6*n1a+n3a := by positivity
  have hA2a0 : 0 <= 12*n1a+8*n3a := by positivity
  have hA1p0 : 0 <= 6*n1p+n3p := by positivity
  have hA2p0 : 0 <= 12*n1p+8*n3p := by positivity
  have hca0 : 0 <= n5a/20 := by positivity
  have hcp0 : 0 <= n5p/20 := by positivity
  have hA1a : 6*n1a+n3a <= n1a*(6+R^2) := by nlinarith
  have hA2a : 12*n1a+8*n3a <= n1a*(12+8*R^2) := by nlinarith
  have hA1p : 6*n1p+n3p <= n1p*(6+R^2) := by nlinarith
  have hA2p : 12*n1p+8*n3p <= n1p*(12+8*R^2) := by nlinarith
  have hca : n5a/20 <= n1a*R^4/20 := by nlinarith
  have hcp : n5p/20 <= n1p*R^4/20 := by nlinarith
  have hBa1 : 0 <= n1a*(6+R^2) := by positivity
  have hBa2 : 0 <= n1a*(12+8*R^2) := by positivity
  have hBp1 : 0 <= n1p*(6+R^2) := by positivity
  have hBp2 : 0 <= n1p*(12+8*R^2) := by positivity
  have hBca : 0 <= n1a*R^4/20 := by positivity
  have hBcp : 0 <= n1p*R^4/20 := by positivity
  have hterm1 :
      32*(6*n1a+n3a)*(n5p/20)
        <= 32*(n1a*(6+R^2))*(n1p*R^4/20) := by
    gcongr
  have hterm2 :
      (n5a/20)*(12*n1p+8*n3p)
        <= (n1a*R^4/20)*(n1p*(12+8*R^2)) := by
    gcongr
  have hterm3 :
      (12*n1a+8*n3a)*(n5p/20)
        <= (n1a*(12+8*R^2))*(n1p*R^4/20) := by
    gcongr
  have hterm4 :
      32*(n5a/20)*(6*n1p+n3p)
        <= 32*(n1a*R^4/20)*(n1p*(6+R^2)) := by
    gcongr
  have hterm5 :
      64*(n5a/20)*(n5p/20)
        <= 64*(n1a*R^4/20)*(n1p*R^4/20) := by
    gcongr
  unfold determinantErrorConstant g21OddSupportPolynomial
  calc
    32 * (6 * n1a + n3a) * (n5p / 20) +
          (n5a / 20) * (12 * n1p + 8 * n3p) +
          (12 * n1a + 8 * n3a) * (n5p / 20) +
          32 * (n5a / 20) * (6 * n1p + n3p) +
          64 * (n5a / 20) * (n5p / 20)
      <= 32*(n1a*(6+R^2))*(n1p*R^4/20)
        + (n1a*R^4/20)*(n1p*(12+8*R^2))
        + (n1a*(12+8*R^2))*(n1p*R^4/20)
        + 32*(n1a*R^4/20)*(n1p*(6+R^2))
        + 64*(n1a*R^4/20)*(n1p*R^4/20) := by
          linarith
    _ = (n1a*n1p/25) * (510*R^4 + 100*R^6 + 4*R^8) := by ring

end Synthesis
