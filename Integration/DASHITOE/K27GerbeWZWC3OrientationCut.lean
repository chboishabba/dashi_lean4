import Mathlib

/-!
# 26D SU2 flux / gerbe, WZW k+2, and signed-orientation no-promotion

PRIOR MATHEMATICS: SU(2) WZW level k, volume flux, affine Sugawara
central charge, and coprime-order homomorphism obstruction.

This module proves **coefficient identities** under externally supplied
geometric/current-algebra inputs. It does NOT construct a smooth S3
manifold, a U(1) gerbe, the affine integrable module, a K27 generator,
or the original three signed-zero trit phase as a physical orientation.
-/

namespace DASHIK27GerbeWZW

/-- The selected H=(2/r)vol_S3 integrates to 4π²r² on
    the round S3. Under source convention (4π²α')^{-1}∫H,
    r²=kα' has integer WZW flux k. The sphere integration
    itself is a sourced premise, not proved by this ring identity. -/
theorem fluxLevelNormalization (k alphaPrime : ℚ)
    (hAlpha : alphaPrime ≠ 0) :
    (k * alphaPrime) / alphaPrime = k := by
  field_simp
  ring

/-- All 23 noncompact free-boson degrees, including the spacelike
linear-dilaton boson, plus an SU2_k WZW matter sector. -/
theorem matterDimensionCount : 23 + 3 = 26 := by norm_num

/-- Bosonic SU2_k integrable highest weight with label ell=2j:
    h_j=j(j+1)/(k+2). Correct primary range ell=0..k is a separate
    representation/module input, not supplied by this equality. -/
theorem sugawaraHighestWeightIdentity
    (ell k : ℚ) (hk : k + 2 ≠ 0) :
    ((ell / 2) * (ell / 2 + 1)) / (k + 2) =
      ell * (ell + 2) / (4 * (k + 2)) := by
  field_simp
  ring

/-- Exact-source worldsheet charge at the quantum-corrected slope. -/
theorem correctedWorldsheetCentralCharge (k : ℚ)
    (hk : k + 2 ≠ 0) :
    23 + 6 / (k + 2) + 3 * k / (k + 2) = 26 := by
  field_simp
  ring

/-- A finite-level mismatched background: hold the semiclassical
    round-S3 radius r²=kα' but impose the c=26 dilaton slope
    alpha' V²=1/(k+2). The original two-derivative scalar EOM
    acquires a positive residual for every k>0. This is a
    quantum-correction NEED, not a contradiction of exact WZW. -/
theorem classicalDilatonMismatch (k : ℚ) (hk : k ≠ 0)
    (hkp : k + 2 ≠ 0) :
    6 / k - 4 / (k + 2) - 2 / k =
      8 / (k * (k + 2)) := by
  field_simp
  ring

theorem classicalDilatonMismatchPositive (k : ℚ) (hk : 0 < k) :
    0 < 8 / (k * (k + 2)) := by
  apply div_pos
  · norm_num
  · exact mul_pos hk (by linarith)

/-- An order-three phase cannot itself induce a nontrivial
    order-two duad-orientation sign by a homomorphism:
    simultaneously satisfying x²=1 and x³=1 forces x=1.
    This is the concrete group-law firewall between original
    C3 signed-neutral-phase rotation and Z2 oriented-duad line. -/
theorem threeCycleCannotBeOrientationFlip
    {G : Type*} [Group G] (x : G)
    (two : x ^ 2 = 1) (three : x ^ 3 = 1) : x = 1 := by
  calc
    x = x ^ 2 * x := by rw [two]; simp
    _ = x ^ 3 := by group
    _ = 1 := three

end DASHIK27GerbeWZW
