import Integration.RationalAlbertCubicNormStructure
import Mathlib

/-!
# Nondegeneracy of the native rational Albert trace pairing

The bilinear trace form on `H₃(O_Q)` is positive definite in the chosen compact
rational coordinate model.  This gives the uniqueness principle needed to turn
cubic-gradient equality into equality of adjoints.
-/

namespace Integration.RationalAlbertTracePairNondegenerate

open Integration.RationalCayleyDicksonOctonion
open Integration.RationalAlbertNative
open Integration.RationalAlbertCubicNormStructure
open RationalQuaternion RationalOctonion RationalAlbertNative.RationalAlbert

abbrev A27 := RationalAlbertNative.RationalAlbert

/-- The octonion pairing used by the Albert trace form is positive definite. -/
theorem innerO_self_nonneg (x : RationalOctonion) : 0 ≤ innerO x x := by
  rcases x with ⟨a,b⟩
  rcases a with ⟨a0,a1,a2,a3⟩
  rcases b with ⟨b0,b1,b2,b3⟩
  simp [innerO, RationalOctonion.mul, RationalOctonion.conj,
    RationalOctonion.realPart, RationalQuaternion.mul,
    RationalQuaternion.conj]
  positivity

/-- Vanishing self-pairing forces a rational octonion to vanish. -/
theorem innerO_self_zero {x : RationalOctonion} (h : innerO x x = 0) : x = 0 := by
  rcases x with ⟨a,b⟩
  rcases a with ⟨a0,a1,a2,a3⟩
  rcases b with ⟨b0,b1,b2,b3⟩
  have hs0 : 0 ≤ a0^2 := sq_nonneg a0
  have hs1 : 0 ≤ a1^2 := sq_nonneg a1
  have hs2 : 0 ≤ a2^2 := sq_nonneg a2
  have hs3 : 0 ≤ a3^2 := sq_nonneg a3
  have ht0 : 0 ≤ b0^2 := sq_nonneg b0
  have ht1 : 0 ≤ b1^2 := sq_nonneg b1
  have ht2 : 0 ≤ b2^2 := sq_nonneg b2
  have ht3 : 0 ≤ b3^2 := sq_nonneg b3
  simp [innerO, RationalOctonion.mul, RationalOctonion.conj,
    RationalOctonion.realPart, RationalQuaternion.mul,
    RationalQuaternion.conj] at h
  apply RationalOctonion.ext <;> apply RationalQuaternion.ext <;>
    simp <;> nlinarith

/-- Vanishing Albert self-pairing forces the complete 27-coordinate element to
vanish. -/
theorem tracePair_self_zero {X : A27} (h : tracePair X X = 0) : X = 0 := by
  rcases X with ⟨a,b,c,x,y,z⟩
  have hx : 0 ≤ innerO x x := innerO_self_nonneg x
  have hy : 0 ≤ innerO y y := innerO_self_nonneg y
  have hz : 0 ≤ innerO z z := innerO_self_nonneg z
  have ha : 0 ≤ a^2 := sq_nonneg a
  have hb : 0 ≤ b^2 := sq_nonneg b
  have hc : 0 ≤ c^2 := sq_nonneg c
  have hsum : a*a + b*b + c*c + 2*(innerO x x + innerO y y + innerO z z) = 0 := by
    simpa [tracePair] using h
  have az : a = 0 := by nlinarith
  have bz : b = 0 := by nlinarith
  have cz : c = 0 := by nlinarith
  have xx : innerO x x = 0 := by nlinarith
  have yy : innerO y y = 0 := by nlinarith
  have zz : innerO z z = 0 := by nlinarith
  have xz : x = 0 := innerO_self_zero xx
  have yz : y = 0 := innerO_self_zero yy
  have zz' : z = 0 := innerO_self_zero zz
  apply RationalAlbert.ext <;> simp [az,bz,cz,xz,yz,zz']

/-- Nondegeneracy in the form needed by the gradient/adjoint uniqueness proof. -/
theorem tracePair_nondegenerate (X : A27)
    (h : ∀ Y : A27, tracePair X Y = 0) : X = 0 :=
  tracePair_self_zero (h X)

structure Boundary where
  octonionPairingPositiveDefinite : Bool
  octonionPairingNondegenerate : Bool
  albertTracePairPositiveDefinite : Bool
  albertTracePairNondegenerate : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  octonionPairingPositiveDefinite := true
  octonionPairingNondegenerate := true
  albertTracePairPositiveDefinite := true
  albertTracePairNondegenerate := true

end Integration.RationalAlbertTracePairNondegenerate
