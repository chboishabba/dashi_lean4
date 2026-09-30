import Mathlib

/-!
# Actual Monster 3B weight-two spectral fingerprint (necessary, not sufficient)

External: the Moonshine series T_{3B} = q^(-1)+54 q-76 q²+...
(e.g. Conway–Norton, verified in OEIS A007244, and the Γ0(3)
Hauptmodul identity). In V_2^natural, dim=196884,
Tr(3B|V_2)=54. The 1-dimensional fixed vacuum/conformal line
contributes +1, so the actual 196883 constituent W has trace 53.

Since g^3=1 in char 0, eigenspaces for 1, omega, omega² exist.
The nonreal eigenvalues occur in equal multiplicities over the reals.
Writing a=dim W_1, b=dim W_omega=dim W_omega², we must have
a+2b=196883 and a-b=53.
Thus (a,b)=(65663,65610), with no independent choice.

This is an actual source-derived fingerprint for any *selected* 3B
action identification. Matching it is NECESSARY, never sufficient:
character equality alone cannot establish equality of operators.
-/

namespace Integration.Selected3BActualMonsterCharacterFingerprint

def actualWeightTwoDimension : ℕ := 196884
def actualWeightTwoThreeBTrace : ℤ := 54
def actualIrreducibleDimension : ℕ := 196883
def actualIrreducibleThreeBTrace : ℤ := 53

theorem vacuum_trace_removed :
    actualWeightTwoThreeBTrace - 1 = actualIrreducibleThreeBTrace := by
  decide

theorem actual_threeB_eigenmultiplicities :
    (65663 : ℕ) + 2 * 65610 = actualIrreducibleDimension ∧
    (65663 : ℤ) - 65610 = actualIrreducibleThreeBTrace := by
  constructor <;> decide

theorem eigenmultiplicity_profile_unique
    (a b : ℕ)
    (hrank : a + 2*b = actualIrreducibleDimension)
    (htrace : (a : ℤ) - b = actualIrreducibleThreeBTrace) :
    a = 65663 ∧ b = 65610 := by
  dsimp [actualIrreducibleDimension, actualIrreducibleThreeBTrace]
    at hrank htrace
  omega

theorem full_griess_threeB_eigenmultiplicities :
    (65664:ℕ) + 2*65610 = actualWeightTwoDimension ∧
    (65664:ℤ) - 65610 = actualWeightTwoThreeBTrace := by
  constructor <;> decide

/-- Test for ANY selected linear action presented by its two independent
real eigenmultiplicities. It is an exact source fingerprint, not an
operator equality against Monster action. -/
theorem selected_action_fingerprint
    (fixedPart complexPart : ℕ)
    (hrank : fixedPart + 2*complexPart = 196883)
    (htrace : (fixedPart : ℤ) - complexPart = 53) :
    fixedPart = 65663 ∧ complexPart = 65610 := by
  exact eigenmultiplicity_profile_unique fixedPart complexPart
    (by simpa [actualIrreducibleDimension] using hrank)
    (by simpa [actualIrreducibleThreeBTrace] using htrace)

end Integration.Selected3BActualMonsterCharacterFingerprint
