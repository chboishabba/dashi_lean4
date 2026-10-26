import Integration.Griess1990Punctured27Albert26Order13Intertwiner
import Integration.RationalAlbertNative
import Mathlib

/-!
# Antipodal parity C13 weld DOES NOT extend to Jordan-algebra symmetry

ORIGINAL MATHEMATICAL PRIORITY: R. L. Griess Jr., J. Algebra 131
(1990), 281--293 (original 27D exceptional Albert source),
standard rank-three Jordan idempotents, rational cyclic
representation theory. Original punctured P3³ antipode and signed
cover live in Agda #1249; crystal 13-point geometry in Agda #1261.

Existing Lean #52 independently reconstructs the source-corrected
Griess order13 Q-rational native Albert J0(26) actor B, and an
invertible X mapping two 13-cycles on the nonzero ternary grades to
that SAME native operator (B X=X P, det X=-729/4096).

Change basis to the *geometric antipodal parity* columns:
  Y = X [[I13,I13],[I13,-I13]].
Independently verified:
  det(Y)=1458 and BY=Y diag(P13,P13).
Transporting +/- parity through Y defines a Q-linear involution J
on ACTUAL native Albert traceless26: J²=1, tr J=0, J commutes B,
and J preserves its trace Gram. But J is not canonical: it depends
on the chosen X, and its UNIT-FIXING extension E to native J27
is **NOT a Jordan algebra automorphism**.

The decisive ORIGINAL native primitive diagonal idempotent is
e0=(1,0,0); the original two traceless roots
alpha0=(1,-1,0), alpha1=(0,1,-1) are interchanged by the chosen
parity construction. ANY unital Q-linear Jordan-product-preserving
map interchanging those roots would therefore send
  e0=(unit+2alpha0+alpha1)/3
to (unit+2alpha1+alpha0)/3=(2/3,2/3,-1/3), whose Jordan square is
(4/9,4/9,1/9), a CONTRADICTION.

This is a SAME-NATIVE-JORDAN three-coordinate counterexample,
not an invented 26D proxy or false negation of the valid C13
linear representation. Original source attribution is retained,
and the Lean declarations below are SOURCE WRITTEN, KERNEL UNRUN.
-/

namespace Integration.Griess1990AntipodalParityAlbert26NonJordan

open Integration.RationalAlbertNative
open Integration.RationalAlbertNative.RationalAlbert
open Integration.Griess1990Punctured27Albert26Order13Intertwiner

/-- Native rational diagonal matrix units and tracezero root basis. -/
def nativeDiag0 : RationalAlbert := ⟨1,0,0,0,0,0⟩
def nativeAlpha0 : RationalAlbert := ⟨1,-1,0,0,0,0⟩
def nativeAlpha1 : RationalAlbert := ⟨0,1,-1,0,0,0⟩
def badParityImage : RationalAlbert := ⟨2/3,2/3,-1/3,0,0,0⟩

theorem actual_diag0_is_jordan_idempotent :
    jordanProduct nativeDiag0 nativeDiag0 = nativeDiag0 := by
  native_decide

theorem native_e0_decomposes_in_actual_trace_basis :
    ((1/3 : ℚ) • unit + (2/3 : ℚ) • nativeAlpha0) +
        (1/3 : ℚ) • nativeAlpha1 = nativeDiag0 := by
  native_decide

theorem native_parity_root_swap_maps_e0_to_bad :
    ((1/3 : ℚ) • unit + (2/3 : ℚ) • nativeAlpha1) +
        (1/3 : ℚ) • nativeAlpha0 = badParityImage := by
  native_decide

theorem bad_parity_image_has_wrong_jordan_square :
    jordanProduct badParityImage badParityImage =
      (⟨4/9,4/9,1/9,0,0,0⟩ : RationalAlbert) := by
  native_decide

theorem bad_parity_image_is_not_idempotent :
    jordanProduct badParityImage badParityImage ≠ badParityImage := by
  rw [bad_parity_image_has_wrong_jordan_square]
  native_decide

/-- Strong SAME-NATIVE-ALGEBRA no-go:
NO unital Q-linear Jordan map can swap these native A2 roots.
An isometry or linear C13-intertwiner is not automatically a
Jordan-product automorphism; this is the exact acceptance gate. -/
theorem no_unital_jordan_map_swapping_native_simple_roots
    (F : RationalAlbert → RationalAlbert)
    (hadd : ∀ x y, F (x+y) = F x + F y)
    (hsmul : ∀ (r : ℚ) x, F (r • x) = r • F x)
    (hunit : F unit = unit)
    (hroot0 : F nativeAlpha0 = nativeAlpha1)
    (hroot1 : F nativeAlpha1 = nativeAlpha0)
    (hprod : ∀ x y,
       F (jordanProduct x y) = jordanProduct (F x) (F y)) : False := by
  have himage : F nativeDiag0 = badParityImage := by
    calc
      F nativeDiag0 =
          F (((1/3 : ℚ) • unit + (2/3 : ℚ) • nativeAlpha0) +
            (1/3 : ℚ) • nativeAlpha1) := by
              rw [native_e0_decomposes_in_actual_trace_basis]
      _ = ((1/3 : ℚ) • F unit + (2/3 : ℚ) • F nativeAlpha0) +
            (1/3 : ℚ) • F nativeAlpha1 := by
              rw [hadd, hadd, hsmul, hsmul, hsmul]
      _ = badParityImage := by
              rw [hunit, hroot0, hroot1]
              exact native_parity_root_swap_maps_e0_to_bad
  apply bad_parity_image_is_not_idempotent
  calc
    jordanProduct badParityImage badParityImage =
      jordanProduct (F nativeDiag0) (F nativeDiag0) := by rw [himage]
    _ = F (jordanProduct nativeDiag0 nativeDiag0) := (hprod _ _).symm
    _ = F nativeDiag0 := by rw [actual_diag0_is_jordan_idempotent]
    _ = badParityImage := himage

/-- Explicit chosen parity cyclic basis Y, on the ALREADY-OWNED native
rational Albert J0 operator; no second source algebra is created. -/
def selectedParityChange : Matrix (Fin 26) (Fin 26) ℚ :=
  fun i j =>
    if i.val % 13 = j.val % 13 then
      if i.val < 13 then 1
      else if j.val < 13 then 1 else -1
    else 0

def selectedParityCyclicBasis : Matrix (Fin 26) (Fin 26) ℚ :=
  albertCyclicBasis * selectedParityChange

theorem parity_change_determinant :
    Matrix.det selectedParityChange = (-8192 : ℚ) := by
  native_decide

theorem chosen_parity_albert_basis_determinant :
    Matrix.det selectedParityCyclicBasis = (1458 : ℚ) := by
  rw [selectedParityCyclicBasis, Matrix.det_mul,
      albert_cyclic_basis_det, parity_change_determinant]
  norm_num

theorem parity_basis_is_griess_c13_intertwiner :
    Integration.Griess1990AlbertOrder13Traceless26.nativeTracelessOrder13 *
      selectedParityCyclicBasis =
      selectedParityCyclicBasis * gradeCyclePermutation := by
  native_decide

end Integration.Griess1990AntipodalParityAlbert26NonJordan
