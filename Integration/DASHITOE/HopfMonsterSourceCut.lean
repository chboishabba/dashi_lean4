import Mathlib
import Integration.DASHITOE.Core
import Integration.DASHITOE.K27TransverseDuadCharacterCut
import Integration.DASHITOE.WittenCSWZWMonsterChiralCut

/-!
Source-matched algebraic leaves from Agda #1554 (P0AM–AO).
This is a companion to the existing K27 / Witten / TOE owners, not a
continuum Einstein solver or an actual Monster representation.
Source-written; no kernel receipt is asserted for this commit.
-/
namespace DASHITOE.HopfMonsterSourceCut

/-- The direct periodic Hopf seed has a common normal factor s = sqrt S.
The prescribed tangential derivative coefficient is 2*j/s. The result is
the scalar multiplier of the identity after contraction with H inverse. -/
theorem seedJumpMultiplier (s j : ℚ) (hs : s ≠ 0) :
    s / 2 * (2 * j / s) = j := by
  field_simp <;> ring

/-- Pure-tension scalar seam factor after the conformal change.
t is kappa*T, u is the positive conformal factor. -/
theorem conformalJumpMultiplier (u t : ℚ) (hu : u ≠ 0) :
    ((-t / 3) + (t / 3 * (u - u ^ 2)) / u) / u = -t / 3 := by
  field_simp <;> ring

/-- Exact algebra of the decaying lower and upper boundary barriers.
e is the chosen eta value, d is the small barrier amplitude. -/
theorem lowerBarrierResidual (t d e : ℚ) :
    -t*d*e/3 + t/3*((1-d*e)-(1-d*e)^2) = -t*d^2*e^2/3 := by ring

theorem upperBarrierResidual (t d e : ℚ) :
    t*d*e/3 + t/3*((1+d*e-2*d^2*e^2)-(1+d*e-2*d^2*e^2)^2) =
      t*d^2*e^2*(1+4*d*e-4*d^2*e^2)/3 := by ring

/-- Published M2 linear exterior carrier, half copy and natural parity.
These are exact arithmetic checks, not exterior action construction. -/
def halfEven : Nat := 4 * Nat.choose 24 2 + 4 * Nat.choose 24 4
def halfOdd : Nat := Nat.choose 24 1 + 6 * Nat.choose 24 3 + Nat.choose 24 5

theorem halfParity : halfEven = 43608 ∧ halfOdd = 54672 := by
  decide

theorem naturalFullParity :
    300 + 2 * halfEven = 87516 ∧ 24 + 2 * halfOdd = 109368 := by decide

theorem dressedFullParity :
    300 + halfEven + halfOdd = 98580 ∧
    24 + halfEven + halfOdd = 98304 := by decide

/-- Selected rank-eight block cycle with arbitrary real degree-preserving
order-three flavour mixing, not every C3 action or the full Monster. -/
theorem selectedTriadicCharacterNoGo (m : ℤ) : 96 - 24*m ≠ 54 := by omega

/-- On the chosen zero-KK tower the AdS3 dimension starts at three.
Arithmetic consequence of the source separated operator; no PDE proof. -/
theorem zeroKKMassPositive (n : Nat) : 3 ≤ (n+1)*(n+3) := by
  nlinarith [Nat.zero_le n]

/-- Reuse the original signed-duad and chiral CS/WZW negative controls. -/
theorem originalComparisonControls :
    (36 : ℤ) ≠ 20 ∧ (5 : ℕ) ≠ 1 :=
  ⟨DASHIK27Transverse.atlas2ACharacterMismatch,
   DASHIWittenCSWZW.noDirectChiralBlockIdentification⟩

/-- The original TOE grade rule forbids a coordinate-only donor
from promoting the physical Monster edge. -/
theorem coordinateDonorDoesNotPromote :
    composeGrade .sharedCarrier .conjecturalStructural = .conjecturalStructural := rfl

end DASHITOE.HopfMonsterSourceCut


namespace DASHITOE.HopfMonsterSourceCut

/-- Polynomial graph metric equality along the full chosen affine path.
The variables are scalar evaluations on two original tangents, not
an asserted Lorentzian manifold or integrated action. -/
theorem kkGraphPath (g dg a b da db f k df dk r dr t : ℚ) :
    g + t*dg + (r+t*dr)*((f+t*df)+(a+t*da))*((k+t*dk)+(b+t*db)) =
    g + t*dg + (r+t*dr)*((a+f)+t*(da+df))*((b+k)+t*(db+dk)) := by ring

/-- Original AK warp lapse equation, after selecting its first integral. -/
theorem periodicWarpLapse (c h b v : ℚ)
    (hv : v^2 = c^2*b^2-h^2) :
    b^2*(-12*h^2)-12*b^2*v^2+12*c^2*b^4 = 0 := by
  rw [hv]
  ring

/-- Warp variation of the same reduced EH density at unit normal lapse. -/
theorem periodicWarpEulerLagrange (c h b v w : ℚ)
    (hv : v^2 = c^2*b^2-h^2) (hw : w = c^2*b) :
    2*b*(-12*h^2)-24*b*v^2-24*b^2*w+48*c^2*b^3 = 0 := by
  rw [hv, hw]
  ring

/-- The boundary term obtained by varying the same warped EH action,
including the periodic pure-tension surface action. -/
theorem periodicWarpSeam (b t : ℚ) :
    -24*b^2*(-t*b/3)-8*t*b^3 = 0 := by ring

/-- Integrated bulk total derivative b^3 b' yields the supplied relation
between warp moments and tension. This lemma pays only its algebraic
consequence, not the integration or the continuum variation. -/
theorem periodicWarpReducedPotential (c h I2 I4 t : ℚ)
    (ht : t = 3*(4*c^2*I4-3*h^2*I2)) :
    24*c^2*I4-12*h^2*I2-2*t = 6*h^2*I2 := by
  rw [ht]
  ring

end DASHITOE.HopfMonsterSourceCut
