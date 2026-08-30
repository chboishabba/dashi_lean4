import Mathlib

/-!
# A concrete, kernel-computable field with 27 elements

This file constructs the field `GF(27) = 𝔽₃[t]/(t³ - t - 1)` as a plain Lean structure of
three `ZMod 3` coordinates, so that *every* operation of the field reduces inside the Lean 4
kernel.  This is what makes the *proof by reflection* in `RequestProject/KernelReflection.lean`
possible: statements about this field can be checked by `decide`, i.e. by kernel computation.

Everything here is elementary:

* `GF27` : the carrier, `a + b·t + c·t²` with `t³ = t + 1` (`t³ - t - 1` is irreducible over `𝔽₃`).
* `GF27.instCommRing`, `GF27.instField` : the ring and field structures; the only genuinely
  finite verification, `x ≠ 0 → x ^ 26 = 1`, is discharged by the kernel (`decide`).
* `GF27.instCharP` : characteristic 3, and `GF27.card_eq` : `#GF27 = 3 ^ 3 = 27`.
* `GF27.mul'`, `GF27.pow'`, `GF27.enum` : *fast* kernel-friendly versions of multiplication,
  exponentiation and enumeration, together with the lemmas identifying them with the
  field operations.  These are the workhorses of the reflection proofs.
-/

set_option maxHeartbeats 1000000

/-- An element `c0 + c1·t + c2·t²` of `GF(27) = 𝔽₃[t]/(t³ - t - 1)`. -/
structure GF27 where
  c0 : ZMod 3
  c1 : ZMod 3
  c2 : ZMod 3
deriving DecidableEq, Fintype, Repr

namespace GF27

@[ext] theorem ext' {x y : GF27} (h0 : x.c0 = y.c0) (h1 : x.c1 = y.c1) (h2 : x.c2 = y.c2) :
    x = y := by
  cases x; cases y; simp_all

/-! ### Ring operations -/

instance : Zero GF27 := ⟨⟨0, 0, 0⟩⟩
instance : One GF27 := ⟨⟨1, 0, 0⟩⟩
instance : Add GF27 := ⟨fun x y => ⟨x.c0 + y.c0, x.c1 + y.c1, x.c2 + y.c2⟩⟩
instance : Neg GF27 := ⟨fun x => ⟨-x.c0, -x.c1, -x.c2⟩⟩
instance : Sub GF27 := ⟨fun x y => ⟨x.c0 - y.c0, x.c1 - y.c1, x.c2 - y.c2⟩⟩

/-- Multiplication: reduce the product of two polynomials modulo `t³ = t + 1`
(so `t⁴ = t² + t`). -/
instance : Mul GF27 := ⟨fun x y =>
  ⟨x.c0 * y.c0 + (x.c1 * y.c2 + x.c2 * y.c1),
   x.c0 * y.c1 + x.c1 * y.c0 + (x.c1 * y.c2 + x.c2 * y.c1) + x.c2 * y.c2,
   x.c0 * y.c2 + x.c1 * y.c1 + x.c2 * y.c0 + x.c2 * y.c2⟩⟩

@[simp] theorem zero_c0 : (0 : GF27).c0 = 0 := rfl
@[simp] theorem zero_c1 : (0 : GF27).c1 = 0 := rfl
@[simp] theorem zero_c2 : (0 : GF27).c2 = 0 := rfl
@[simp] theorem one_c0 : (1 : GF27).c0 = 1 := rfl
@[simp] theorem one_c1 : (1 : GF27).c1 = 0 := rfl
@[simp] theorem one_c2 : (1 : GF27).c2 = 0 := rfl
@[simp] theorem add_c0 (x y : GF27) : (x + y).c0 = x.c0 + y.c0 := rfl
@[simp] theorem add_c1 (x y : GF27) : (x + y).c1 = x.c1 + y.c1 := rfl
@[simp] theorem add_c2 (x y : GF27) : (x + y).c2 = x.c2 + y.c2 := rfl
@[simp] theorem neg_c0 (x : GF27) : (-x).c0 = -x.c0 := rfl
@[simp] theorem neg_c1 (x : GF27) : (-x).c1 = -x.c1 := rfl
@[simp] theorem neg_c2 (x : GF27) : (-x).c2 = -x.c2 := rfl
@[simp] theorem sub_c0 (x y : GF27) : (x - y).c0 = x.c0 - y.c0 := rfl
@[simp] theorem sub_c1 (x y : GF27) : (x - y).c1 = x.c1 - y.c1 := rfl
@[simp] theorem sub_c2 (x y : GF27) : (x - y).c2 = x.c2 - y.c2 := rfl
@[simp] theorem mul_c0 (x y : GF27) :
    (x * y).c0 = x.c0 * y.c0 + (x.c1 * y.c2 + x.c2 * y.c1) := rfl
@[simp] theorem mul_c1 (x y : GF27) :
    (x * y).c1 = x.c0 * y.c1 + x.c1 * y.c0 + (x.c1 * y.c2 + x.c2 * y.c1) + x.c2 * y.c2 := rfl
@[simp] theorem mul_c2 (x y : GF27) :
    (x * y).c2 = x.c0 * y.c2 + x.c1 * y.c1 + x.c2 * y.c0 + x.c2 * y.c2 := rfl

private theorem add_assoc' (x y z : GF27) : x + y + z = x + (y + z) := by ext <;> simp <;> ring
private theorem zero_add' (x : GF27) : 0 + x = x := by ext <;> simp
private theorem add_zero' (x : GF27) : x + 0 = x := by ext <;> simp
private theorem add_comm' (x y : GF27) : x + y = y + x := by ext <;> simp <;> ring
private theorem neg_add_cancel' (x : GF27) : -x + x = 0 := by ext <;> simp
private theorem mul_assoc' (x y z : GF27) : x * y * z = x * (y * z) := by ext <;> simp <;> ring
private theorem one_mul' (x : GF27) : 1 * x = x := by ext <;> simp
private theorem mul_one' (x : GF27) : x * 1 = x := by ext <;> simp
private theorem left_distrib' (x y z : GF27) : x * (y + z) = x * y + x * z := by
  ext <;> simp <;> ring
private theorem right_distrib' (x y z : GF27) : (x + y) * z = x * z + y * z := by
  ext <;> simp <;> ring
private theorem mul_comm' (x y : GF27) : x * y = y * x := by ext <;> simp <;> ring
private theorem sub_eq_add_neg' (x y : GF27) : x - y = x + -y := by ext <;> simp [sub_eq_add_neg]
private theorem zero_mul' (x : GF27) : 0 * x = 0 := by ext <;> simp
private theorem mul_zero' (x : GF27) : x * 0 = 0 := by ext <;> simp

instance instCommRing : CommRing GF27 where
  add_assoc := add_assoc'
  zero_add := zero_add'
  add_zero := add_zero'
  add_comm := add_comm'
  neg_add_cancel := neg_add_cancel'
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'
  left_distrib := left_distrib'
  right_distrib := right_distrib'
  mul_comm := mul_comm'
  sub_eq_add_neg := sub_eq_add_neg'
  zero_mul := zero_mul'
  mul_zero := mul_zero'
  nsmul := nsmulRec
  zsmul := zsmulRec

/-! ### Fast, kernel-friendly arithmetic

`Monoid.npow` unfolds through a tower of structure projections, which the kernel handles
slowly.  The following raw functions compute directly on coordinates and are the ones used in
the reflection proofs; the lemmas below identify them with the field operations. -/

/-- Multiplication, as a plain function (definitionally the field multiplication). -/
def mul' (x y : GF27) : GF27 := x * y

/-- Exponentiation by repeated multiplication, as a plain recursive function. -/
def pow' (x : GF27) : ℕ → GF27
  | 0 => 1
  | n + 1 => mul' (pow' x n) x

theorem mul'_eq (x y : GF27) : mul' x y = x * y := rfl

theorem pow'_eq (x : GF27) (n : ℕ) : pow' x n = x ^ n := by
  induction n with
  | zero => simp [pow']
  | succ n ih => simp [pow', mul'_eq, ih, pow_succ]

/-- The list of all `27` elements of `GF27`. -/
def enum : List GF27 :=
  (List.range 3).flatMap fun a => (List.range 3).flatMap fun b => (List.range 3).map fun c =>
    ⟨(a : ZMod 3), (b : ZMod 3), (c : ZMod 3)⟩

theorem mem_enum : ∀ x : GF27, x ∈ enum := by decide

theorem length_enum : enum.length = 27 := by decide

/-! ### The field structure -/

/-- Every nonzero element satisfies `x ^ 26 = 1`: a finite fact, checked by the kernel. -/
theorem pow_26_eq_one_of_ne_zero : ∀ x : GF27, x ≠ 0 → x ^ 26 = 1 := by decide

instance : Inv GF27 := ⟨fun x => pow' x 25⟩

theorem inv_def (x : GF27) : x⁻¹ = x ^ 25 := pow'_eq x 25

instance instField : Field GF27 where
  inv := fun x => x⁻¹
  exists_pair_ne := ⟨0, 1, by decide⟩
  mul_inv_cancel := by
    intro x hx
    have h : x * x ^ 25 = x ^ 26 := by ring
    rw [inv_def, h]
    exact pow_26_eq_one_of_ne_zero x hx
  inv_zero := by decide
  nnqsmul := _
  qsmul := _

theorem three_eq_zero : ((3 : ℕ) : GF27) = 0 := by decide

instance instCharP : CharP GF27 3 :=
  (CharP.charP_iff_prime_eq_zero (by norm_num)).2 three_eq_zero

theorem card_eq : Nat.card GF27 = 3 ^ 3 := by
  simp [Nat.card_eq_fintype_card]
  decide

end GF27
