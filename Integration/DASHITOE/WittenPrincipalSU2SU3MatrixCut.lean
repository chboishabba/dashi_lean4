import Mathlib

/-!
# Principal sl₂ -> sl₃: selected source algebra for SU(2)_4 subset SU(3)_1

PRIOR AUTHORS: Dynkin's subalgebra index, Lacki and Zaugg (1989).
This is an explicit complexified rational Lie algebra basis. The
original affine embedding and WZW conformal-block extension are
external theorems; a successful finite matrix certificate does not
construct affine modes/OPEs or a physical colour gauge group.

The exact 3×3 SymPy regression in Agda #1249 checks these
commutators, Dynkin index 4 and adjoint spin1(3)+spin2(5).
Lean source has not been kernel/type checked in this environment.
-/

namespace DASHIWittenPrincipalSU2SU3

abbrev M3 := Matrix (Fin 3) (Fin 3) ℚ

def E (i j : Fin 3) : M3 :=
  fun r c => if r = i ∧ c = j then 1 else 0

def raise : M3 := E 0 1 + E 1 2
def lower : M3 := 2 • (E 1 0 + E 2 1)
def cartan : M3 := 2 • E 0 0 - 2 • E 2 2

def comm (a b : M3) : M3 := a * b - b * a

/-- Exact principal sl₂ structure relations within sl₃. -/
theorem principalLieBrackets :
    comm cartan raise = 2 • raise ∧
    comm cartan lower = -2 • lower ∧
    comm raise lower = cartan := by
  decide

/-- Lie algebra trace normalization: compared with the 2D
standard sl₂ doublet, the principal 3D representation has
trace of raise*lower equal to 4, yielding index four. -/
theorem principalIndexFour :
    Matrix.trace (raise * lower) = 4 := by
  decide

/-- Highest adjoint weight +4 generates a spin-two
five-dimensional module; this is the five extra currents
beside the sl₂ adjoint spin-one triplet. -/
theorem spinTwoHighestWeight :
    comm cartan (E 0 2) = 4 • E 0 2 ∧
    comm raise (E 0 2) = 0 := by
  decide

end DASHIWittenPrincipalSU2SU3
