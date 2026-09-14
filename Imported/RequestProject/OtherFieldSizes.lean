import RequestProject.WhyTwentySeven

/-!
# Trying other sizes concretely: `GF(9)` and `GF(8)`

`RequestProject/GF27.lean` builds `GF(27) = 𝔽₃[t]/(t³ - t - 1)` as a kernel-computable structure,
and `RequestProject/KernelReflection.lean` checks the Frobenius picture there by `decide`.
Here we do the same for the two nearest neighbours of `27`, so that the abstract criterion of
`RequestProject/WhyTwentySeven.lean` can be *seen* rather than only deduced:

* `GF9 = 𝔽₃[t]/(t² - t - 1)`, the field with `9` elements.  Frobenius is `x ↦ x³` and the orbit
  product is `N(x) = x · x³ = x⁴`.  It lands in `𝔽₃` and is onto `𝔽₃` (`GF9.norm_surjective`),
  but it does **not** fix `𝔽₃`: `N(2) = 1` (`GF9.norm_two`).  Equivalently `N` is not even
  idempotent (`GF9.norm_not_idempotent`) — in sharp contrast with `x ↦ x¹³` on `GF(27)`.
* `GF8 = 𝔽₂[t]/(t³ + t + 1)`, the field with `8` elements.  Frobenius is `x ↦ x²` and the orbit
  product is `N(x) = x · x² · x⁴ = x⁷`, which *is* a retraction onto `𝔽₂ = {0,1}`
  (`GF8.norm_retraction`) — but a degenerate one: it sends every nonzero element to `1`
  (`GF8.norm_eq_one_of_ne_zero`), so no information survives.

In both fields the Frobenius fixed points are exactly the prime subfield
(`GF9.fixedPoints_frobenius`, `GF8.fixedPoints_frobenius`): that part of the picture is
size-independent.  What distinguishes `27` is the orbit product.
-/

set_option maxHeartbeats 1000000

/-! ## `GF(9) = 𝔽₃[t]/(t² - t - 1)` -/

/-- An element `c0 + c1·t` of `GF(9) = 𝔽₃[t]/(t² - t - 1)`, i.e. with `t² = t + 1`. -/
structure GF9 where
  c0 : ZMod 3
  c1 : ZMod 3
deriving DecidableEq, Fintype, Repr

namespace GF9

@[ext] theorem ext' {x y : GF9} (h0 : x.c0 = y.c0) (h1 : x.c1 = y.c1) : x = y := by
  cases x; cases y; simp_all

instance : Zero GF9 := ⟨⟨0, 0⟩⟩
instance : One GF9 := ⟨⟨1, 0⟩⟩
instance : Add GF9 := ⟨fun x y => ⟨x.c0 + y.c0, x.c1 + y.c1⟩⟩
instance : Neg GF9 := ⟨fun x => ⟨-x.c0, -x.c1⟩⟩
instance : Sub GF9 := ⟨fun x y => ⟨x.c0 - y.c0, x.c1 - y.c1⟩⟩

/-- Multiplication modulo `t² = t + 1`. -/
instance : Mul GF9 := ⟨fun x y =>
  ⟨x.c0 * y.c0 + x.c1 * y.c1, x.c0 * y.c1 + x.c1 * y.c0 + x.c1 * y.c1⟩⟩

@[simp] theorem zero_c0 : (0 : GF9).c0 = 0 := rfl
@[simp] theorem zero_c1 : (0 : GF9).c1 = 0 := rfl
@[simp] theorem one_c0 : (1 : GF9).c0 = 1 := rfl
@[simp] theorem one_c1 : (1 : GF9).c1 = 0 := rfl
@[simp] theorem add_c0 (x y : GF9) : (x + y).c0 = x.c0 + y.c0 := rfl
@[simp] theorem add_c1 (x y : GF9) : (x + y).c1 = x.c1 + y.c1 := rfl
@[simp] theorem neg_c0 (x : GF9) : (-x).c0 = -x.c0 := rfl
@[simp] theorem neg_c1 (x : GF9) : (-x).c1 = -x.c1 := rfl
@[simp] theorem sub_c0 (x y : GF9) : (x - y).c0 = x.c0 - y.c0 := rfl
@[simp] theorem sub_c1 (x y : GF9) : (x - y).c1 = x.c1 - y.c1 := rfl
@[simp] theorem mul_c0 (x y : GF9) : (x * y).c0 = x.c0 * y.c0 + x.c1 * y.c1 := rfl
@[simp] theorem mul_c1 (x y : GF9) :
    (x * y).c1 = x.c0 * y.c1 + x.c1 * y.c0 + x.c1 * y.c1 := rfl

instance instCommRing : CommRing GF9 where
  add_assoc := by intro x y z; ext <;> simp <;> ring
  zero_add := by intro x; ext <;> simp
  add_zero := by intro x; ext <;> simp
  add_comm := by intro x y; ext <;> simp <;> ring
  neg_add_cancel := by intro x; ext <;> simp
  mul_assoc := by intro x y z; ext <;> simp <;> ring
  one_mul := by intro x; ext <;> simp
  mul_one := by intro x; ext <;> simp
  left_distrib := by intro x y z; ext <;> simp <;> ring
  right_distrib := by intro x y z; ext <;> simp <;> ring
  mul_comm := by intro x y; ext <;> simp <;> ring
  sub_eq_add_neg := by intro x y; ext <;> simp [sub_eq_add_neg]
  zero_mul := by intro x; ext <;> simp
  mul_zero := by intro x; ext <;> simp
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- Every nonzero element satisfies `x ^ 8 = 1`; checked by the kernel. -/
theorem pow_eight_eq_one_of_ne_zero : ∀ x : GF9, x ≠ 0 → x ^ 8 = 1 := by decide

instance : Inv GF9 := ⟨fun x => x ^ 7⟩

theorem inv_def (x : GF9) : x⁻¹ = x ^ 7 := rfl

instance instField : Field GF9 where
  inv := fun x => x⁻¹
  exists_pair_ne := ⟨0, 1, by decide⟩
  mul_inv_cancel := by
    intro x hx
    have h : x * x ^ 7 = x ^ 8 := by ring
    rw [inv_def, h]
    exact pow_eight_eq_one_of_ne_zero x hx
  inv_zero := by decide
  nnqsmul := _
  qsmul := _

theorem three_eq_zero : ((3 : ℕ) : GF9) = 0 := by decide

instance instCharP : CharP GF9 3 :=
  (CharP.charP_iff_prime_eq_zero (by norm_num)).2 three_eq_zero

theorem card_eq : Nat.card GF9 = 3 ^ 2 := by
  simp [Nat.card_eq_fintype_card]
  decide

/-! ### The Frobenius picture on `GF(9)` -/

/-- The Frobenius fixed points of `GF(9)` are exactly the three elements of the prime
subfield `𝔽₃ = {0, 1, 2}` (those with vanishing `t`-coordinate). -/
theorem fixedPoints_frobenius (x : GF9) : x ^ 3 = x ↔ x.c1 = 0 := by revert x; decide

/-- Every Frobenius orbit in `GF(9)` has length `1` or `2`, and the orbit product is `x ⬝ x³`. -/
theorem pow_nine_eq_self (x : GF9) : x ^ 9 = x := by revert x; decide

/-- The orbit product `N(x) = x · x³ = x⁴` lands in the prime subfield. -/
theorem norm_mem_primeSubfield (x : GF9) : (x ^ 4).c1 = 0 := by revert x; decide

/-- `N` is onto the prime subfield: it takes each of the values `0, 1, 2`. -/
theorem norm_surjective :
    (0 : GF9) ^ 4 = 0 ∧ (1 : GF9) ^ 4 = 1 ∧ (⟨0, 1⟩ : GF9) ^ 4 = ⟨2, 0⟩ := by decide

/-- **But `N` does not fix the prime subfield**: `N(2) = 2⁴ = 1 ≠ 2`.  This is the failure
predicted by `WhyTwentySeven.frobNorm_eq_self_on_primeSubfield_iff`, since `3 - 1 = 2` does not
divide `2 - 1 = 1`. -/
theorem norm_two : (⟨2, 0⟩ : GF9) ^ 4 = 1 ∧ (⟨2, 0⟩ : GF9) ≠ 1 := by decide

/-- Equivalently: on `GF(9)` the orbit product is not idempotent, so it is not a retraction
onto anything.  (On `GF(27)`, `x ↦ x¹³` *is* idempotent, see
`RetractiveCore.isIdempotent_norm`.) -/
theorem norm_not_idempotent : ¬ ∀ x : GF9, (x ^ 4) ^ 4 = x ^ 4 := by decide

end GF9

/-! ## `GF(8) = 𝔽₂[t]/(t³ + t + 1)` -/

/-- An element `c0 + c1·t + c2·t²` of `GF(8) = 𝔽₂[t]/(t³ + t + 1)`, i.e. with `t³ = t + 1`. -/
structure GF8 where
  c0 : ZMod 2
  c1 : ZMod 2
  c2 : ZMod 2
deriving DecidableEq, Fintype, Repr

namespace GF8

@[ext] theorem ext' {x y : GF8} (h0 : x.c0 = y.c0) (h1 : x.c1 = y.c1) (h2 : x.c2 = y.c2) :
    x = y := by
  cases x; cases y; simp_all

instance : Zero GF8 := ⟨⟨0, 0, 0⟩⟩
instance : One GF8 := ⟨⟨1, 0, 0⟩⟩
instance : Add GF8 := ⟨fun x y => ⟨x.c0 + y.c0, x.c1 + y.c1, x.c2 + y.c2⟩⟩
instance : Neg GF8 := ⟨fun x => ⟨-x.c0, -x.c1, -x.c2⟩⟩
instance : Sub GF8 := ⟨fun x y => ⟨x.c0 - y.c0, x.c1 - y.c1, x.c2 - y.c2⟩⟩

/-- Multiplication modulo `t³ = t + 1` (so `t⁴ = t² + t`), exactly as for `GF27`. -/
instance : Mul GF8 := ⟨fun x y =>
  ⟨x.c0 * y.c0 + (x.c1 * y.c2 + x.c2 * y.c1),
   x.c0 * y.c1 + x.c1 * y.c0 + (x.c1 * y.c2 + x.c2 * y.c1) + x.c2 * y.c2,
   x.c0 * y.c2 + x.c1 * y.c1 + x.c2 * y.c0 + x.c2 * y.c2⟩⟩

@[simp] theorem zero_c0 : (0 : GF8).c0 = 0 := rfl
@[simp] theorem zero_c1 : (0 : GF8).c1 = 0 := rfl
@[simp] theorem zero_c2 : (0 : GF8).c2 = 0 := rfl
@[simp] theorem one_c0 : (1 : GF8).c0 = 1 := rfl
@[simp] theorem one_c1 : (1 : GF8).c1 = 0 := rfl
@[simp] theorem one_c2 : (1 : GF8).c2 = 0 := rfl
@[simp] theorem add_c0 (x y : GF8) : (x + y).c0 = x.c0 + y.c0 := rfl
@[simp] theorem add_c1 (x y : GF8) : (x + y).c1 = x.c1 + y.c1 := rfl
@[simp] theorem add_c2 (x y : GF8) : (x + y).c2 = x.c2 + y.c2 := rfl
@[simp] theorem neg_c0 (x : GF8) : (-x).c0 = -x.c0 := rfl
@[simp] theorem neg_c1 (x : GF8) : (-x).c1 = -x.c1 := rfl
@[simp] theorem neg_c2 (x : GF8) : (-x).c2 = -x.c2 := rfl
@[simp] theorem sub_c0 (x y : GF8) : (x - y).c0 = x.c0 - y.c0 := rfl
@[simp] theorem sub_c1 (x y : GF8) : (x - y).c1 = x.c1 - y.c1 := rfl
@[simp] theorem sub_c2 (x y : GF8) : (x - y).c2 = x.c2 - y.c2 := rfl
@[simp] theorem mul_c0 (x y : GF8) :
    (x * y).c0 = x.c0 * y.c0 + (x.c1 * y.c2 + x.c2 * y.c1) := rfl
@[simp] theorem mul_c1 (x y : GF8) :
    (x * y).c1 = x.c0 * y.c1 + x.c1 * y.c0 + (x.c1 * y.c2 + x.c2 * y.c1) + x.c2 * y.c2 := rfl
@[simp] theorem mul_c2 (x y : GF8) :
    (x * y).c2 = x.c0 * y.c2 + x.c1 * y.c1 + x.c2 * y.c0 + x.c2 * y.c2 := rfl

private theorem zmod2_add_self : ∀ a : ZMod 2, a + a = 0 := by decide

instance instCommRing : CommRing GF8 where
  add_assoc := by intro x y z; ext <;> simp <;> ring
  zero_add := by intro x; ext <;> simp
  add_zero := by intro x; ext <;> simp
  add_comm := by intro x y; ext <;> simp <;> ring
  neg_add_cancel := by intro x; ext <;> simp <;> exact zmod2_add_self _
  mul_assoc := by intro x y z; ext <;> simp <;> ring
  one_mul := by intro x; ext <;> simp
  mul_one := by intro x; ext <;> simp
  left_distrib := by intro x y z; ext <;> simp <;> ring
  right_distrib := by intro x y z; ext <;> simp <;> ring
  mul_comm := by intro x y; ext <;> simp <;> ring
  sub_eq_add_neg := by intro x y; ext <;> simp [sub_eq_add_neg]
  zero_mul := by intro x; ext <;> simp
  mul_zero := by intro x; ext <;> simp
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- Every nonzero element satisfies `x ^ 7 = 1`; checked by the kernel. -/
theorem pow_seven_eq_one_of_ne_zero : ∀ x : GF8, x ≠ 0 → x ^ 7 = 1 := by decide

instance : Inv GF8 := ⟨fun x => x ^ 6⟩

theorem inv_def (x : GF8) : x⁻¹ = x ^ 6 := rfl

instance instField : Field GF8 where
  inv := fun x => x⁻¹
  exists_pair_ne := ⟨0, 1, by decide⟩
  mul_inv_cancel := by
    intro x hx
    have h : x * x ^ 6 = x ^ 7 := by ring
    rw [inv_def, h]
    exact pow_seven_eq_one_of_ne_zero x hx
  inv_zero := by decide
  nnqsmul := _
  qsmul := _

theorem two_eq_zero : ((2 : ℕ) : GF8) = 0 := by decide

instance instCharP : CharP GF8 2 :=
  (CharP.charP_iff_prime_eq_zero (by norm_num)).2 two_eq_zero

theorem card_eq : Nat.card GF8 = 2 ^ 3 := by
  simp [Nat.card_eq_fintype_card]
  decide

/-! ### The Frobenius picture on `GF(8)` -/

/-- The Frobenius fixed points of `GF(8)` are exactly the two elements of the prime subfield
`𝔽₂ = {0, 1}`. -/
theorem fixedPoints_frobenius (x : GF8) : x ^ 2 = x ↔ (x = 0 ∨ x = 1) := by revert x; decide

theorem pow_eight_eq_self (x : GF8) : x ^ 8 = x := by revert x; decide

/-- The orbit product `N(x) = x · x² · x⁴ = x⁷` **is** a retraction onto `𝔽₂`: it fixes `0`
and `1`. -/
theorem norm_retraction : (0 : GF8) ^ 7 = 0 ∧ (1 : GF8) ^ 7 = 1 := by decide

/-- …but a degenerate one: every nonzero element has orbit product `1`, because `𝔽₂ˣ` is
trivial.  This is why characteristic `2` does not give an interesting example. -/
theorem norm_eq_one_of_ne_zero : ∀ x : GF8, x ≠ 0 → x ^ 7 = 1 :=
  pow_seven_eq_one_of_ne_zero

/-- On `GF(8)` the orbit product *is* idempotent (unlike on `GF(9)`). -/
theorem norm_idempotent : ∀ x : GF8, (x ^ 7) ^ 7 = x ^ 7 := by decide

end GF8

/-! ## Matching the concrete computations with the general criterion -/

section Compare

open FrobeniusPrimeSubfield

/-- On `GF(9)` the general orbit product is the concrete map `x ↦ x⁴`. -/
theorem GF9.frobNorm_eq (x : GF9) : frobNorm 3 2 x = x ^ 4 := by
  simp [frobNorm, Finset.prod_range_succ]
  ring

/-- On `GF(8)` the general orbit product is the concrete map `x ↦ x⁷`. -/
theorem GF8.frobNorm_eq (x : GF8) : frobNorm 2 3 x = x ^ 7 := by
  simp [frobNorm, Finset.prod_range_succ]
  ring

/-- `GF(9)`: the orbit product is **not** a retraction onto the prime subfield
(`3 - 1 = 2 ∤ 1 = 2 - 1`). -/
theorem GF9.not_retractive :
    ¬ ∀ a ∈ Set.range (primeSubfieldHom GF9 3), frobNorm 3 2 a = a := by
  rw [WhyTwentySeven.frobNorm_eq_self_on_primeSubfield_iff (by norm_num)]
  decide

/-- `GF(8)`: the orbit product **is** a retraction onto the prime subfield
(`2 - 1 = 1 ∣ 2 = 3 - 1`) — degenerately, by `GF8.norm_eq_one_of_ne_zero`. -/
theorem GF8.retractive :
    ∀ a ∈ Set.range (primeSubfieldHom GF8 2), frobNorm 2 3 a = a :=
  (WhyTwentySeven.frobNorm_eq_self_on_primeSubfield_iff (by norm_num)).2 (by norm_num)

end Compare
