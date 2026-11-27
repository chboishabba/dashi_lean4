import Mathlib

/-!
# Coupled incidence on the original degree-seven Dickson cover

The five Kummer generators are e_i-e_6. A six-slot character annihilates
the rotation subgroup precisely when its coordinates are equal. This
retains both surviving signs at each nonzero relative embedding.
An independent quadratic-root involution, however, negates the primitive
orientation pairing. The quadratic equation below is the source chart
in the actual surface variable s. Geometric source and involution action
on the transcendental carrier are established separately in the roadmap.
-/

open scoped BigOperators

namespace DASHI.Hodge.DicksonCoupled

abbrev Address := Fin 6
abbrev Character := Address → ZMod 7

theorem rotation_generators_iff_diagonal (k : Character) :
    (∀ i : Address, k i - k 5 = 0) ↔
      ∀ i : Address, k i = k 5 := by
  constructor
  · intro h i
    exact sub_eq_zero.mp (h i)
  · intro h i
    exact sub_eq_zero.mpr (h i)

def signedCharacter (j : ZMod 7) (s : Bool) : ZMod 7 :=
  if s then j else -j

theorem signedCharacter_injective {j : ZMod 7} (hj : j ≠ 0) :
    Function.Injective (signedCharacter j) := by
  have hne : j ≠ -j := by
    intro h
    have hz : (2 : ZMod 7)*j = 0 := by linear_combination h
    exact (mul_ne_zero (by decide) hj) hz
  intro s t h
  cases s <;> cases t <;> simp_all [signedCharacter, hne, Ne.symm hne]

theorem signed_rotation_survival_iff {j : ZMod 7} (hj : j ≠ 0)
    (signs : Address → Bool) :
    (∀ i : Address,
      signedCharacter j (signs i) - signedCharacter j (signs 5) = 0) ↔
        ∀ i : Address, signs i = signs 5 := by
  constructor
  · intro h i
    exact signedCharacter_injective hj (sub_eq_zero.mp (h i))
  · intro h i
    rw [h i, sub_self]

/-- Quadratic root partner at the original fixed (alpha, y) address. -/
def rootPartner (A B s : ℚ) : ℚ := -B/A-s

theorem quadratic_root_partner (A B C s : ℚ) (ha : A ≠ 0) :
    A*(rootPartner A B s)^2+B*rootPartner A B s+C =
      A*s^2+B*s+C := by
  unfold rootPartner
  field_simp [ha] <;> ring

theorem rootPartner_involutive (A B s : ℚ) :
    rootPartner A B (rootPartner A B s) = s := by
  unfold rootPartner
  ring

theorem derivative_partner_sign (A B s : ℚ) (ha : A ≠ 0) :
    2*A*rootPartner A B s+B = -(2*A*s+B) := by
  unfold rootPartner
  field_simp [ha] <;> ring

/-- An actual cycle fixed by an involution acting by minus one on a
primitive input has zero coefficient. This does not assert that an
arbitrary sixfold is fixed by such an involution. -/
theorem fixed_cycle_odd_character_zero (c : ℚ) (h : c = -c) : c = 0 := by
  linarith


/-- Actual t=1 source polynomial (paper 140, Q0). -/
def dickson7 (X a : ℚ) : ℚ :=
  X^7-7*a*X^5+14*a^2*X^3-7*a^3*X

def Q0 (a s : ℚ) : ℚ :=
  -3*a^3-3*a^2*s-a^2+3*a*s+3*a-2*s^2+s+3

theorem dickson7_laurent (a v : ℚ) (hv : v ≠ 0) :
    dickson7 (v+a/v) a = v^7+(a/v)^7 := by
  unfold dickson7
  field_simp [hv] <;> ring

theorem Q0_partner (a s : ℚ) :
    Q0 a (rootPartner (-2) (-3*a^2+3*a+1) s) = Q0 a s := by
  unfold Q0 rootPartner
  ring

/-- The second coupled incidence fixes the product of the six visible
quadratic-root derivatives. Any odd subset of root changes moves the
candidate to the other signed locus; it is not a stabilizer. -/
theorem odd_flip_changes_product (d e : Address → ℚ)
    (hd : (∏ i, d i) = 1) (he : (∏ i, e i) = -1) :
    (∏ i, e i * d i) = -1 := by
  rw [Finset.prod_mul_distrib, he, hd, mul_one]

theorem odd_flip_leaves_positive_locus (d e : Address → ℚ)
    (hd : (∏ i, d i) = 1) (he : (∏ i, e i) = -1) :
    (∏ i, e i * d i) ≠ 1 := by
  rw [odd_flip_changes_product d e hd he]
  norm_num

end DASHI.Hodge.DicksonCoupled

