import Mathlib
import RequestProject.GF27
import RequestProject.Frobenius
import RequestProject.CenterRetraction

/-!
# Reaching the retractions inside the Lean 4 kernel, by reflection

The two earlier files develop the retractions abstractly:

* `RequestProject/Frobenius.lean` — in a finite field `K` with `#K = p ^ n` the Frobenius orbit
  product `x ↦ ∏_{k<n} x ^ (p ^ k)` is multiplicative, lands in the prime subfield `𝔽_p`
  (= the fixed points of Frobenius), and, when `p - 1 ∣ n - 1`, fixes `𝔽_p` pointwise: a
  retraction of `Kˣ` onto `𝔽_pˣ`.
* `RequestProject/CenterRetraction.lean` — retractions of a group onto its center.

This file *reaches a concrete instance of each of those retractions inside the Lean 4 kernel*,
by **proof by reflection**: the mathematical statement is replaced by the evaluation of a
`Bool`-valued decision procedure, that Boolean is computed by the kernel itself
(`decide +kernel`, so the certificate really is a kernel computation and not an elaborator
one), and a reflection lemma transports the Boolean result back to the proposition.

The concrete field is `GF27 = 𝔽₃[t]/(t³ - t - 1)` from `RequestProject/GF27.lean`, whose every
operation reduces in the kernel.  Here `p = 3`, `n = 3`, `p - 1 = 2 ∣ 2 = n - 1`, so the orbit
product is `x ↦ x ^ (1 + 3 + 9) = x ^ 13` and it is a *genuine, nontrivial* retraction
`GF27ˣ ↠ 𝔽₃ˣ` (a group of order `26` onto a subgroup of order `2`).

* `reflect_forall` : the reflection principle used throughout.
* `GF27.pow_three_eq_self_iff` : the Frobenius fixed points of `GF27` are exactly `{0, 1, 2}`,
  i.e. the prime subfield `𝔽₃` — *checked by the kernel*.
* `GF27.norm_mul`, `GF27.norm_mem_prime`, `GF27.norm_fixes_prime`, `GF27.norm_ne_zero` :
  the defining properties of the retraction, each checked by the kernel.
* `GF27.frobNorm_retraction_kernel_verified` : the four properties packaged exactly as in the
  abstract theorem `FrobeniusPrimeSubfield.frobNorm_retraction_onto_primeSubfield`, but obtained
  by reflection; `GF27.frobNorm_retraction_abstract_eq_kernel` records that the abstract
  theorem, instantiated at `GF27`, says precisely the same thing.
* `GF27.normRetraction` : the retraction packaged as a group homomorphism
  `GF27ˣ →* primeUnits` together with `GF27.normRetraction_restrict`.
* `DihedralProd.hasCenterRetraction_kernel` : a concrete retraction onto the *center*
  of the group `DihedralGroup 3 × Multiplicative (ZMod 2)`, again verified by kernel
  computation via `hasCenterRetraction_of_check`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace KernelReflection

/-! ### The reflection principle

If `l` is a list containing every element of `α` and the kernel computes `l.all p = true`,
then `p a` holds for every `a : α`.  Every proposition below is proved through this lemma,
with the Boolean premise discharged by `decide +kernel`. -/

theorem reflect_forall {α : Type*} {l : List α} (hl : ∀ a, a ∈ l) {p : α → Bool}
    (h : l.all p = true) (a : α) : p a = true :=
  List.all_eq_true.1 h a (hl a)

end KernelReflection

namespace GF27

open KernelReflection

/-! ### The Boolean decision procedures

All of them use the fast kernel-friendly operations `GF27.mul'`, `GF27.pow'` and the
enumeration `GF27.enum` of the 27 elements. -/

/-- The prime subfield `𝔽₃ ⊆ GF27`, as a list. -/
def primeList : List GF27 := [0, 1, 2]

/-- Check: an element is fixed by the Frobenius `x ↦ x ^ 3` iff it lies in `𝔽₃`. -/
def frobFixedCheck : Bool :=
  enum.all fun x => (pow' x 3 == x) == primeList.contains x

/-- Check: the orbit product `x ↦ x ^ 13` is multiplicative. -/
def normMulCheck : Bool :=
  enum.all fun x => enum.all fun y => pow' (mul' x y) 13 == mul' (pow' x 13) (pow' y 13)

/-- Check: the orbit product lands in the prime subfield. -/
def normMemCheck : Bool := enum.all fun x => primeList.contains (pow' x 13)

/-- Check: the orbit product fixes the prime subfield pointwise. -/
def normFixCheck : Bool := primeList.all fun a => pow' a 13 == a

/-- Check: the orbit product of a nonzero element is nonzero. -/
def normNeZeroCheck : Bool := enum.all fun x => (x == 0) || !(pow' x 13 == 0)

theorem frobFixedCheck_eq_true : frobFixedCheck = true := by decide +kernel
theorem normMulCheck_eq_true : normMulCheck = true := by decide +kernel
theorem normMemCheck_eq_true : normMemCheck = true := by decide +kernel
theorem normFixCheck_eq_true : normFixCheck = true := by decide +kernel
theorem normNeZeroCheck_eq_true : normNeZeroCheck = true := by decide +kernel

/-! ### Transporting the kernel computations back to propositions -/

theorem mem_primeList_iff (x : GF27) : x ∈ primeList ↔ x = 0 ∨ x = 1 ∨ x = 2 := by
  simp [primeList]

/-- **Fixed points of the Frobenius, verified by the kernel.**
`x ^ 3 = x` exactly for the three elements of the prime subfield `𝔽₃`. -/
theorem pow_three_eq_self_iff (x : GF27) : x ^ 3 = x ↔ (x = 0 ∨ x = 1 ∨ x = 2) := by
  have h := reflect_forall mem_enum frobFixedCheck_eq_true x
  simp only [beq_iff_eq] at h
  rw [Bool.eq_iff_iff] at h
  simp only [beq_iff_eq, pow'_eq, List.contains_iff_mem] at h
  rw [← mem_primeList_iff]
  exact h

/-- **Multiplicativity of the orbit product, verified by the kernel.** -/
theorem norm_mul (x y : GF27) : (x * y) ^ 13 = x ^ 13 * y ^ 13 := by
  have h := reflect_forall mem_enum (reflect_forall mem_enum normMulCheck_eq_true x) y
  simpa [pow'_eq, mul'_eq] using h

/-- **The orbit product lands in the prime subfield, verified by the kernel.** -/
theorem norm_mem_prime (x : GF27) : x ^ 13 = 0 ∨ x ^ 13 = 1 ∨ x ^ 13 = 2 := by
  have h := reflect_forall mem_enum normMemCheck_eq_true x
  rw [← mem_primeList_iff]
  simpa [pow'_eq, List.contains_iff_mem] using h

/-- **The orbit product fixes the prime subfield pointwise, verified by the kernel.** -/
theorem norm_fixes_prime {a : GF27} (ha : a = 0 ∨ a = 1 ∨ a = 2) : a ^ 13 = a := by
  have h := List.all_eq_true.1 normFixCheck_eq_true a ((mem_primeList_iff a).2 ha)
  simpa [pow'_eq] using h

/-- **The orbit product of a nonzero element is nonzero, verified by the kernel.** -/
theorem norm_ne_zero {x : GF27} (hx : x ≠ 0) : x ^ 13 ≠ 0 := by
  have h := reflect_forall mem_enum normNeZeroCheck_eq_true x
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
    beq_eq_false_iff_ne, pow'_eq] at h
  tauto

/-! ### Identification with the abstract theory -/

open FrobeniusPrimeSubfield

/-- The Frobenius orbit product of `Frobenius.lean`, at `p = 3`, `n = 3`, is `x ↦ x ^ 13`. -/
theorem frobNorm_eq_pow_thirteen (x : GF27) : frobNorm 3 3 x = x ^ 13 := by
  rw [frobNorm_eq_pow]
  norm_num [Finset.sum_range_succ]

/-- The prime subfield of `GF27`, i.e. the image of `ZMod 3 → GF27`, is `{0, 1, 2}`;
its description as the Frobenius fixed points is the kernel-checked
`GF27.pow_three_eq_self_iff`. -/
theorem range_primeSubfieldHom :
    Set.range (primeSubfieldHom GF27 3) = ({0, 1, 2} : Set GF27) := by
  ext x
  rw [← pow_char_eq_self_iff_mem_range_zmod (K := GF27) (p := 3) x]
  simpa using pow_three_eq_self_iff x

/-- **A retraction onto the prime subfield, reached inside the Lean 4 kernel.**

For the concrete field `GF27 = 𝔽₃[t]/(t³ - t - 1)` the Frobenius orbit product
`x ↦ ∏_{k<3} x ^ (3 ^ k) = x ^ 13` is multiplicative, maps `GF27` into the prime subfield
`𝔽₃ = {0, 1, 2}`, is nonzero on nonzero elements, and restricts to the identity on `𝔽₃`.

Every one of the four clauses is discharged by a Boolean computation performed by the Lean 4
kernel (`decide +kernel`); none of them uses the general theory. -/
theorem frobNorm_retraction_kernel_verified :
    (∀ x y : GF27, frobNorm 3 3 (x * y) = frobNorm 3 3 x * frobNorm 3 3 y) ∧
      (∀ x : GF27, frobNorm 3 3 x ∈ ({0, 1, 2} : Set GF27)) ∧
      (∀ x : GF27, x ≠ 0 → frobNorm 3 3 x ≠ 0) ∧
      (∀ a ∈ ({0, 1, 2} : Set GF27), frobNorm 3 3 a = a) := by
  refine ⟨fun x y => ?_, fun x => ?_, fun x hx => ?_, fun a ha => ?_⟩
  · simp only [frobNorm_eq_pow_thirteen]; exact norm_mul x y
  · simpa [frobNorm_eq_pow_thirteen] using norm_mem_prime x
  · simpa [frobNorm_eq_pow_thirteen] using norm_ne_zero hx
  · simp only [frobNorm_eq_pow_thirteen]
    exact norm_fixes_prime (by simpa using ha)

/-- The general theorem of `Frobenius.lean`, instantiated at `GF27`, states exactly the
kernel-verified fact above: the two routes to the retraction agree. -/
theorem frobNorm_retraction_abstract_eq_kernel :
    ((∀ x y : GF27, frobNorm 3 3 (x * y) = frobNorm 3 3 x * frobNorm 3 3 y) ∧
      (∀ x : GF27, frobNorm 3 3 x ∈ Set.range (primeSubfieldHom GF27 3)) ∧
      (∀ x : GF27, x ≠ 0 → frobNorm 3 3 x ≠ 0) ∧
      (∀ a ∈ Set.range (primeSubfieldHom GF27 3), frobNorm 3 3 a = a)) ∧
    Set.range (primeSubfieldHom GF27 3) = ({0, 1, 2} : Set GF27) :=
  ⟨frobNorm_retraction_onto_primeSubfield (K := GF27) (p := 3) (n := 3) card_eq (by norm_num)
      (by norm_num),
    range_primeSubfieldHom⟩

/-! ### The retraction as a group homomorphism on units -/

/-- The units of the prime subfield, `𝔽₃ˣ = {1, -1} ≤ GF27ˣ`, described as the units fixed by
the Frobenius. -/
def primeUnits : Subgroup GF27ˣ where
  carrier := {u : GF27ˣ | u ^ 2 = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, mul_pow] at *
    rw [ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, inv_pow] at *
    rw [ha, inv_one]

/-- A unit lies in `𝔽₃ˣ` exactly when it is a fixed point of the Frobenius. -/
theorem mem_primeUnits_iff (u : GF27ˣ) : u ∈ primeUnits ↔ ((u : GF27)) ^ 3 = (u : GF27) := by
  show u ^ 2 = 1 ↔ _
  rw [← Units.val_eq_one, Units.val_pow_eq_pow_val]
  constructor
  · intro h
    calc (u : GF27) ^ 3 = (u : GF27) ^ 2 * (u : GF27) := by ring
      _ = (u : GF27) := by rw [h, one_mul]
  · intro h
    have hne : ((u : GF27)) ≠ 0 := u.ne_zero
    have hcalc : (u : GF27) ^ 2 * (u : GF27) = 1 * (u : GF27) := by
      rw [one_mul]
      calc (u : GF27) ^ 2 * (u : GF27) = (u : GF27) ^ 3 := by ring
        _ = (u : GF27) := h
    exact mul_right_cancel₀ hne hcalc

/-- The Frobenius orbit product as an endomorphism of the unit group `GF27ˣ`. -/
def normHom : GF27ˣ →* GF27ˣ := powMonoidHom 13

@[simp] theorem normHom_apply (u : GF27ˣ) : ((normHom u : GF27ˣ) : GF27) = (u : GF27) ^ 13 := by
  simp [normHom, powMonoidHom]

theorem normHom_mem_primeUnits (u : GF27ˣ) : normHom u ∈ primeUnits := by
  rw [mem_primeUnits_iff, normHom_apply]
  rcases norm_mem_prime (u : GF27) with h | h | h <;> rw [h] <;> decide +kernel

theorem normHom_eq_self_of_mem {u : GF27ˣ} (hu : u ∈ primeUnits) : normHom u = u := by
  apply Units.ext
  rw [normHom_apply]
  exact norm_fixes_prime ((pow_three_eq_self_iff _).1 ((mem_primeUnits_iff u).1 hu))

/-- **The retraction `GF27ˣ →* 𝔽₃ˣ`.** -/
def normRetraction : GF27ˣ →* primeUnits :=
  normHom.codRestrict primeUnits normHom_mem_primeUnits

/-- `normRetraction` is a retraction: it restricts to the identity on `𝔽₃ˣ`. -/
theorem normRetraction_restrict (u : primeUnits) : normRetraction (u : GF27ˣ) = u :=
  Subtype.ext (normHom_eq_self_of_mem u.2)

end GF27

/-! ### A retraction onto the *center* of a group, reached in the kernel -/

namespace CenterReflection

open Subgroup

/-- A retraction onto the center can be assembled from three checkable facts about a plain
function `f : G → G`: it lands in the center, it is multiplicative, and it fixes the center
pointwise.  For a concrete finite group all three are decidable, hence checkable by the
kernel. -/
theorem hasCenterRetraction_of_check {G : Type*} [Group G] (f : G → G)
    (hmem : ∀ g h : G, h * f g = f g * h)
    (hmul : ∀ g h : G, f (g * h) = f g * f h)
    (hfix : ∀ z : G, (∀ h : G, h * z = z * h) → f z = z) :
    HasCenterRetraction G := by
  refine ⟨⟨⟨fun g => ⟨f g, mem_center_iff.2 (hmem g)⟩, ?_⟩, ?_⟩, ?_⟩
  · have h1 : f 1 = 1 := by
      have h := hmul 1 1
      simp only [mul_one] at h
      exact mul_left_cancel (a := f 1) (by rw [mul_one]; exact h.symm)
    exact Subtype.ext h1
  · intro a b
    exact Subtype.ext (hmul a b)
  · intro z
    exact Subtype.ext (hfix (z : G) fun h => mem_center_iff.1 z.2 h)

end CenterReflection

namespace DihedralProd

open CenterReflection

/-- A concrete group with a nontrivial centre and a nontrivial centreless factor:
`D₃ × C₂`, of order `12`.  Its center is `1 × C₂`. -/
abbrev G : Type := DihedralGroup 3 × Multiplicative (ZMod 2)

/-- The candidate retraction: kill the (centreless) dihedral factor. -/
def r : G → G := fun x => (1, x.2)

theorem r_mem_center_check : ∀ g h : G, h * r g = r g * h := by decide +kernel

theorem r_mul_check : ∀ g h : G, r (g * h) = r g * r h := by decide +kernel

theorem r_fix_check : ∀ z : G, (∀ h : G, h * z = z * h) → r z = z := by decide +kernel

/-- **A retraction onto the center, reached inside the Lean 4 kernel.**
For `G = D₃ × C₂` the map `(d, c) ↦ (1, c)` is a group homomorphism onto the center which
fixes the center pointwise; all three requirements are checked by kernel computation. -/
theorem hasCenterRetraction_kernel : HasCenterRetraction G :=
  hasCenterRetraction_of_check r r_mem_center_check r_mul_check r_fix_check

end DihedralProd
