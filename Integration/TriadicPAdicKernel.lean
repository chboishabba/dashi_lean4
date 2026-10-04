import Mathlib
import Integration.BalancedTernaryAntipodal369OrbitHierarchy

/-!
# Canonical finite triadic kernel

Minimal Lean mirror of the Agda TriadicPAdicCodec finite carrier:

  Kernel d = length-d balanced-ternary vectors.

This file intentionally contains only the finite carrier needed by the current
cross-pollination.
-/

namespace Integration.TriadicPAdicKernel

open Integration.BalancedTernaryAntipodal369OrbitHierarchy

abbrev Kernel (d : Nat) := Fin d → Trit

def origin (d : Nat) : Kernel d :=
  fun _ => .zero

def invert {d : Nat} (x : Kernel d) : Kernel d :=
  fun i => antipode (x i)

theorem invert_involutive {d : Nat} (x : Kernel d) :
    invert (invert x) = x := by
  funext i
  cases x i <;> rfl

abbrev Kernel2 := Kernel 2

def PuncturedKernel2 :=
  {x : Kernel2 // x ≠ origin 2}

theorem kernel2_cardinality :
    Fintype.card Kernel2 = 9 := by
  native_decide

theorem punctured_kernel2_cardinality :
    Fintype.card PuncturedKernel2 = 8 := by
  native_decide

end Integration.TriadicPAdicKernel
