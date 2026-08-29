import Mathlib
import AgdaMirror.Ultrametric

/-!
# Lean mirror of `DASHI/Algebra/MonsterUltrametric15.agda` and
`MonsterProjection15.agda` (genuine ultrametric + contractive projection)

Faithful transcription of the *genuine* length-15 mask ultrametric (distinct
from the first-difference distance in `AgdaMirror.MonsterWalk`, which fails the
ultratriangle law).  Here the distance is

> `dMask x y = len x − lcpLen x y`

where `lcpLen` is the length of the longest common prefix.  This distance is a
*real* ultrametric (the `lcpLen` ultratriangle inequality holds), and we assemble
it into a genuine `AgdaMirror.Ultrametric` instance on the fixed-length carrier
`Mask15 = { m : List Bool // m.length = 15 }`.  We also mirror the key
order-theoretic facts and the contractivity of the constant projection:

* `dMask x y = 0 → x = y` on equal-length masks (`eq_of_dMask_zero`);
* the constant projection `projectTo target` collapses all distance to `0`, hence
  is strictly contractive on distinct masks (`proj_contractive`).

All proofs are by structural induction / case analysis; no `sorry`, axiom-clean.
-/

namespace AgdaMirror.MonsterProjection15

/-! ## Longest-common-prefix length and the mask distance over `List Bool` -/

/-- Length of the longest common prefix of two boolean lists. -/
def lcpLen : List Bool → List Bool → Nat
  | [], [] => 0
  | true :: xs, true :: ys => lcpLen xs ys + 1
  | false :: xs, false :: ys => lcpLen xs ys + 1
  | _, _ => 0

/-- The first-difference mask distance: `len x − lcpLen x y`. -/
def dMask (x y : List Bool) : Nat := x.length - lcpLen x y

/-- The common prefix with an empty left list is empty. -/
@[simp] theorem lcpLen_nil_left (y : List Bool) : lcpLen [] y = 0 := by
  cases y <;> rfl

/-- The common prefix with an empty right list is empty. -/
@[simp] theorem lcpLen_nil_right (x : List Bool) : lcpLen x [] = 0 := by
  cases x with
  | nil => rfl
  | cons b xs => cases b <;> rfl

/-- The common prefix of a list with itself is the whole list. -/
theorem lcpLen_self (m : List Bool) : lcpLen m m = m.length := by
  induction m with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [lcpLen, ih]

/-- The common prefix never exceeds the left length. -/
theorem lcpLen_le_left (x y : List Bool) : lcpLen x y ≤ x.length := by
  induction x generalizing y with
  | nil => simp
  | cons b xs ih =>
    cases y with
    | nil => simp
    | cons c ys =>
      have := ih ys
      cases b <;> cases c <;> simp only [lcpLen, List.length_cons] <;> omega

/-- The common prefix never exceeds the right length. -/
theorem lcpLen_le_right (x y : List Bool) : lcpLen x y ≤ y.length := by
  induction x generalizing y with
  | nil => simp
  | cons b xs ih =>
    cases y with
    | nil => simp
    | cons c ys =>
      have := ih ys
      cases b <;> cases c <;> simp only [lcpLen, List.length_cons] <;> omega

/-- `lcpLen` is symmetric. -/
theorem lcpLen_symm (x y : List Bool) : lcpLen x y = lcpLen y x := by
  induction x generalizing y with
  | nil => cases y <;> simp [lcpLen]
  | cons b xs ih =>
    cases y with
    | nil => cases b <;> simp [lcpLen]
    | cons c ys => cases b <;> cases c <;> simp [lcpLen, ih]

/-- Identity of indiscernibles: `dMask m m = 0`. -/
theorem dMask_id_zero (m : List Bool) : dMask m m = 0 := by
  simp [dMask, lcpLen_self]

/-- Symmetry of `dMask` on equal-length masks. -/
theorem dMask_symm {x y : List Bool} (h : x.length = y.length) :
    dMask x y = dMask y x := by
  simp [dMask, lcpLen_symm x y, h]

/-- Equal-length masks sharing a full-length common prefix are equal. -/
theorem eq_of_lcpLen_full :
    ∀ (x y : List Bool), x.length = y.length → lcpLen x y = x.length → x = y := by
  intro x
  induction x with
  | nil => intro y _ _; cases y with | nil => rfl | cons => simp_all
  | cons b xs ih =>
    intro y hlen hlcp
    cases y with
    | nil => simp at hlen
    | cons c ys =>
      have hlen' : xs.length = ys.length := by simpa using hlen
      cases b <;> cases c <;> simp only [lcpLen, List.length_cons] at hlcp ⊢ <;>
        first
          | (exfalso; omega)
          | (rw [ih ys hlen' (by omega)])

/-- Identity of indiscernibles (full): `dMask x y = 0` forces `x = y` on
equal-length masks. -/
theorem eq_of_dMask_zero {x y : List Bool} (h : x.length = y.length)
    (hd : dMask x y = 0) : x = y := by
  have hle : lcpLen x y ≤ x.length := lcpLen_le_left x y
  have : x.length ≤ lcpLen x y := by
    simp only [dMask] at hd; omega
  exact eq_of_lcpLen_full x y h (le_antisymm hle this)

/-- The genuine ultratriangle inequality for the common-prefix length. -/
theorem lcpLen_ultratriangle (x y z : List Bool) :
    min (lcpLen x y) (lcpLen y z) ≤ lcpLen x z := by
  induction x generalizing y z with
  | nil => simp
  | cons a xs ih =>
    cases y with
    | nil => simp
    | cons b ys =>
      cases z with
      | nil => simp
      | cons c zs =>
        have := ih ys zs
        cases a <;> cases b <;> cases c <;> simp only [lcpLen] <;> omega

/-! ## The fixed-length carrier and its genuine ultrametric -/

/-- Length-15 boolean masks. -/
def Mask15 : Type := { m : List Bool // m.length = 15 }

/-- The mask distance on the fixed-length carrier. -/
def d15 (x y : Mask15) : Nat := dMask x.val y.val

/-- `dMask` ultratriangle on equal-length masks (derived from `lcpLen`). -/
theorem dMask_ultratriangle {x y z : List Bool}
    (hxy : x.length = y.length) (hyz : y.length = z.length) :
    dMask x z ≤ max (dMask x y) (dMask y z) := by
  have hxz : x.length = z.length := hxy.trans hyz
  have hult := lcpLen_ultratriangle x y z
  have h1 : lcpLen x y ≤ x.length := lcpLen_le_left x y
  have h2 : lcpLen y z ≤ y.length := lcpLen_le_left y z
  have h3 : lcpLen x z ≤ x.length := lcpLen_le_left x z
  simp only [dMask]
  omega

/-- The genuine ultrametric on length-15 masks. -/
def UMask15 : AgdaMirror.Ultrametric Mask15 where
  d := d15
  id_zero := fun x => dMask_id_zero x.val
  symmetric := fun x y => dMask_symm (x.property.trans y.property.symm)
  ultratriangle := fun x y z =>
    dMask_ultratriangle (x.property.trans y.property.symm)
      (y.property.trans z.property.symm)

/-! ## The constant projection is strictly contractive on distinct masks -/

/-- A mask-operator kernel. -/
structure Kernel where
  K : Mask15 → Mask15

/-- Projection to a fixed target mask. -/
def projectTo (target : Mask15) : Kernel := ⟨fun _ => target⟩

/-- The constant projection collapses all distance to `0`, hence is strictly
contractive between any two distinct masks (mirrors `projContractive`). -/
theorem proj_contractive (target : Mask15) {x y : Mask15} (hxy : x ≠ y) :
    d15 ((projectTo target).K x) ((projectTo target).K y) < d15 x y := by
  have h0 : d15 ((projectTo target).K x) ((projectTo target).K y) = 0 := by
    simp [projectTo, d15, dMask_id_zero]
  rw [h0]
  rcases Nat.eq_zero_or_pos (d15 x y) with h | h
  · exact absurd (Subtype.ext (eq_of_dMask_zero (x.property.trans y.property.symm) h)) hxy
  · exact h

end AgdaMirror.MonsterProjection15
