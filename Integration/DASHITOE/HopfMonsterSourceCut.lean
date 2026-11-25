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
