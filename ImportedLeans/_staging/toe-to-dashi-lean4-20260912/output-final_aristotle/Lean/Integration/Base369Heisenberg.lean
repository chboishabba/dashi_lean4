import Mathlib

/-!
# The finite Heisenberg group over `𝔽₃ⁿ`, closed at the theorem level

The Base369 lane's carrier is the finite Heisenberg group

```
H(n) = X × X* × 𝔽₃,     X = 𝔽₃ⁿ,
(x, y, z) · (x', y', z') = (x + x', y + y', z + z' + ⟨y, x'⟩),
```

with `X*` identified with `X` through the standard pairing `⟨y, x⟩ = Σᵢ yᵢ xᵢ`.
For `n = 6` this is the `729`-dimensional-Schrödinger-module carrier the lane is
interested in; nothing below depends on `n = 6`, so the results are stated for
all `n` and the case `n = 6` is recorded as `card_H6`.

## What is proved here

* `dot` is bilinear (`dot_add_left`, `dot_add_right`, and the negation forms).
* `heisenbergCocycle` — the multiplication rule's `𝔽₃`-valued cocycle
  `c(g, h) = ⟨y_g, x_h⟩` satisfies the 2-cocycle identity
  `c(a,b) + c(a·b, c) = c(b,c) + c(a, b·c)` at the level of the underlying
  additive group.
* A full `Group (H n)` instance: associativity, identity, inverse and the
  inverse laws are all proved from the cocycle, not postulated.
* `card_H` — `|H n| = 3 ^ (2n + 1)`, and `card_H6 = 3 ^ 13`.
* `commutator_eq` — the group commutator is central and equals the symplectic
  form: `[g, h] = (0, 0, ω(g, h))` with `ω(g,h) = ⟨y_g, x_h⟩ - ⟨y_h, x_g⟩`.
* `omega_alternating`, `omega_skew`, `omega_add_left`, `omega_add_right` — `ω`
  is an alternating bilinear form, and `omega_nondegenerate`: for `n ≥ 1`, any
  nonzero `(x, y)` is detected by some partner.
* `mem_center_iff` — the centre of `H n` is exactly `{(0, 0, z)}`, i.e. the
  `𝔽₃` factor, which is the group-theoretic content of nondegeneracy.
* `not_commutative` — for `n ≥ 1` the group is nonabelian, so the extension is
  not split off by the centre.

## What is *not* proved here

The Schrödinger module `V = X → ℚ(ζ₃)`, its coordinate Fourier projectors, the
delta-line argument, irreducibility, Stone–von Neumann uniqueness and any
Monster-related identification are **not** formalised in this file, and no
claim about them is made.  In particular this file does not assert, and must
not be read as asserting, that a dimension count identifies a representation.
-/

namespace Integration.Base369Heisenberg

open Finset

/-- The ternary field of the lane. -/
abbrev F3 := ZMod 3

/-- The coordinate space `X = 𝔽₃ⁿ`. -/
abbrev X (n : ℕ) : Type := Fin n → F3

variable {n : ℕ}

/-- The standard pairing identifying `X*` with `X`. -/
def dot (y x : X n) : F3 := ∑ i, y i * x i

@[simp] theorem dot_zero_left (x : X n) : dot 0 x = 0 := by simp [dot]

@[simp] theorem dot_zero_right (y : X n) : dot y 0 = 0 := by simp [dot]

theorem dot_add_left (y y' x : X n) : dot (y + y') x = dot y x + dot y' x := by
  simp [dot, add_mul, Finset.sum_add_distrib]

theorem dot_add_right (y x x' : X n) : dot y (x + x') = dot y x + dot y x' := by
  simp [dot, mul_add, Finset.sum_add_distrib]

theorem dot_neg_left (y x : X n) : dot (-y) x = - dot y x := by
  simp [dot, neg_mul, Finset.sum_neg_distrib]

theorem dot_neg_right (y x : X n) : dot y (-x) = - dot y x := by
  simp [dot, mul_neg, Finset.sum_neg_distrib]

/-! ## §1 The group -/

/-- The finite Heisenberg group `H(n) = X × X* × 𝔽₃`. -/
structure H (n : ℕ) where
  /-- The position coordinate. -/
  x : X n
  /-- The momentum (dual) coordinate. -/
  y : X n
  /-- The central coordinate. -/
  z : F3
  deriving DecidableEq

@[ext] theorem H.ext' {g h : H n} (hx : g.x = h.x) (hy : g.y = h.y) (hz : g.z = h.z) : g = h := by
  cases g; cases h; simp_all

/-- The `𝔽₃`-valued cocycle defining the extension. -/
def cocycle (g h : H n) : F3 := dot g.y h.x

instance : Mul (H n) :=
  ⟨fun g h => ⟨g.x + h.x, g.y + h.y, g.z + h.z + cocycle g h⟩⟩

instance : One (H n) := ⟨⟨0, 0, 0⟩⟩

instance : Inv (H n) := ⟨fun g => ⟨-g.x, -g.y, -g.z + dot g.y g.x⟩⟩

@[simp] theorem mul_x (g h : H n) : (g * h).x = g.x + h.x := rfl
@[simp] theorem mul_y (g h : H n) : (g * h).y = g.y + h.y := rfl
@[simp] theorem mul_z (g h : H n) : (g * h).z = g.z + h.z + dot g.y h.x := rfl
@[simp] theorem one_x : (1 : H n).x = 0 := rfl
@[simp] theorem one_y : (1 : H n).y = 0 := rfl
@[simp] theorem one_z : (1 : H n).z = 0 := rfl
@[simp] theorem inv_x (g : H n) : g⁻¹.x = -g.x := rfl
@[simp] theorem inv_y (g : H n) : g⁻¹.y = -g.y := rfl
@[simp] theorem inv_z (g : H n) : g⁻¹.z = -g.z + dot g.y g.x := rfl

/-- **The 2-cocycle identity.**  This is what makes the multiplication
associative. -/
theorem heisenbergCocycle (a b c : H n) :
    cocycle a b + cocycle (a * b) c = cocycle b c + cocycle a (b * c) := by
  simp [cocycle, dot_add_left, dot_add_right]
  ring

theorem H.mul_assoc' (a b c : H n) : a * b * c = a * (b * c) := by
  refine H.ext' ?_ ?_ ?_
  · simp [add_assoc]
  · simp [add_assoc]
  · simp only [mul_z, mul_x, mul_y, dot_add_left, dot_add_right]
    ring

theorem H.one_mul' (g : H n) : 1 * g = g := by
  refine H.ext' ?_ ?_ ?_ <;> simp

theorem H.inv_mul_cancel' (g : H n) : g⁻¹ * g = 1 := by
  refine H.ext' ?_ ?_ ?_ <;> simp [dot_neg_left]

instance : Group (H n) :=
  Group.ofLeftAxioms H.mul_assoc' H.one_mul' H.inv_mul_cancel'

/-! ## §2 Size -/

/-- `H n` as a product, for counting. -/
def equivProd : H n ≃ (X n × X n × F3) where
  toFun g := (g.x, g.y, g.z)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv g := by cases g; rfl
  right_inv p := by rfl

instance : Fintype (H n) := Fintype.ofEquiv _ equivProd.symm

theorem card_H (n : ℕ) : Fintype.card (H n) = 3 ^ (2 * n + 1) := by
  rw [Fintype.card_congr (equivProd (n := n))]
  simp [Fintype.card_prod, ZMod.card, pow_add, two_mul]
  ring

/-- The lane's carrier: `|H(6)| = 3¹³`. -/
theorem card_H6 : Fintype.card (H 6) = 3 ^ 13 := by
  rw [card_H]

/-! ## §3 The symplectic form and the centre -/

/-- The symplectic form on the quotient `H n / centre`. -/
def omega (g h : H n) : F3 := dot g.y h.x - dot h.y g.x

theorem omega_alternating (g : H n) : omega g g = 0 := by simp [omega]

theorem omega_skew (g h : H n) : omega g h = - omega h g := by simp [omega]

theorem omega_add_left (g h k : H n) : omega (g * h) k = omega g k + omega h k := by
  simp only [omega, mul_x, mul_y, dot_add_left, dot_add_right]
  ring

theorem omega_add_right (g h k : H n) : omega g (h * k) = omega g h + omega g k := by
  simp only [omega, mul_x, mul_y, dot_add_left, dot_add_right]
  ring

/-- **The commutator is central and is the symplectic form.** -/
theorem commutator_eq (g h : H n) :
    g * h * g⁻¹ * h⁻¹ = ⟨0, 0, omega g h⟩ := by
  refine H.ext' ?_ ?_ ?_
  · simp
  · simp
  · simp only [mul_z, mul_y, inv_x, inv_y, inv_z, omega, dot_add_left,
      dot_neg_left, dot_neg_right]
    ring

theorem mul_comm_iff (g h : H n) : g * h = h * g ↔ omega g h = 0 := by
  constructor
  · intro hc
    have : g * h * g⁻¹ * h⁻¹ = 1 := by
      rw [hc]
      group
    rw [commutator_eq] at this
    have := congrArg H.z this
    simpa using this
  · intro hw
    refine H.ext' ?_ ?_ ?_
    · simp [add_comm]
    · simp [add_comm]
    · have : dot g.y h.x = dot h.y g.x := by
        have := hw
        simp only [omega, sub_eq_zero] at this
        exact this
      simp [this, add_comm, add_assoc]

/-- The `i`-th standard basis vector of `X n`. -/
def e (i : Fin n) : X n := Pi.single i 1

theorem dot_e_right (y : X n) (i : Fin n) : dot y (e i) = y i := by
  simp [dot, e, Pi.single_apply, Finset.sum_ite_eq' Finset.univ i]

theorem dot_e_left (x : X n) (i : Fin n) : dot (e i) x = x i := by
  simp [dot, e, Pi.single_apply, Finset.sum_ite_eq' Finset.univ i]

/-- **Nondegeneracy.**  Any element with a nonzero `(x, y)` part fails to
commute with something. -/
theorem omega_nondegenerate {g : H n} (h : g.x ≠ 0 ∨ g.y ≠ 0) :
    ∃ k : H n, omega g k ≠ 0 := by
  rcases h with hx | hy
  · obtain ⟨i, hi⟩ : ∃ i, g.x i ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hx (funext hcon)
    refine ⟨⟨0, e i, 0⟩, ?_⟩
    simp only [omega, dot_zero_right, dot_e_left, zero_sub, neg_ne_zero]
    exact hi
  · obtain ⟨i, hi⟩ : ∃ i, g.y i ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hy (funext hcon)
    refine ⟨⟨e i, 0, 0⟩, ?_⟩
    simp only [omega, dot_e_right, dot_zero_left, sub_zero]
    exact hi

/-- **The centre is exactly the `𝔽₃` factor.** -/
theorem mem_center_iff (g : H n) : g ∈ Subgroup.center (H n) ↔ g.x = 0 ∧ g.y = 0 := by
  constructor
  · intro hg
    by_contra hcon
    have h : g.x ≠ 0 ∨ g.y ≠ 0 := by
      rcases Classical.em (g.x = 0) with hx | hx
      · exact Or.inr fun hy => hcon ⟨hx, hy⟩
      · exact Or.inl hx
    obtain ⟨k, hk⟩ := omega_nondegenerate h
    exact hk ((mul_comm_iff g k).1 (Subgroup.mem_center_iff.1 hg k).symm)
  · rintro ⟨hx, hy⟩
    rw [Subgroup.mem_center_iff]
    intro k
    refine H.ext' ?_ ?_ ?_
    · simp [hx, add_comm]
    · simp [hy, add_comm]
    · simp [hx, hy, add_comm]

/-- For `n ≥ 1` the Heisenberg group is nonabelian. -/
theorem not_commutative (hn : 0 < n) :
    ∃ g h : H n, g * h ≠ h * g := by
  have i : Fin n := ⟨0, hn⟩
  refine ⟨⟨0, e i, 0⟩, ⟨e i, 0, 0⟩, ?_⟩
  intro hc
  have hw : omega (⟨0, e i, 0⟩ : H n) ⟨e i, 0, 0⟩ = 0 := (mul_comm_iff _ _).1 hc
  rw [omega] at hw
  simp only [dot_zero_left, sub_zero] at hw
  rw [dot_e_right] at hw
  simp [e, Pi.single_eq_same] at hw

end Integration.Base369Heisenberg
