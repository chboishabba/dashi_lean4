/-
# The relative-holonomy defect telescope

The Eq. (119) consumer needs a defect bound on the *relative* group element

  `U(Γ_{c,x}) U(c)⁻¹`,

not on an abstract transported object.  Written as a single closed word,
`Γ_{c,x} ∥ c⁻¹`, that element is an ordered product of at most
`24 + 13 + 24 + 13 = 74` oriented links, so a per-link budget telescopes
directly.

This module proves, with no proxy object anywhere:

* `defect_prod_le` — the telescope: an ordered product of `n` contractive
  factors with per-factor defect `≤ ε` has defect `≤ n ε`;
* `holonomy_append_reverse` — the same-object identity
  `Hol(Γ ∥ c⁻¹) · Hol(c) = Hol(Γ)`, i.e. the closed word really is the
  relative element;
* `l1defect_star` — the signed-link reduction: a negative traversal is the
  quaternion conjugate of a stored positive bond, and conjugation preserves the
  `ℓ¹` defect, so only *stored positive bonds* need an estimate;
* `relative_holonomy_defect_le` and `relative_holonomy_defect_lt_inv24` —
  the arithmetic `74 · (1/2048) = 37/1024 < 1/24`, on the literal relative
  holonomy of a signed word of stored bonds.

The last bound is exactly the principal-chart admission threshold, so the
chart step downstream consumes this theorem and nothing else.
-/
import Mathlib
import RequestProject.YangMills.SU2QuaternionOperatorNorm

namespace RequestProject.YangMills.RelativeHolonomyDefect

open Matrix
open scoped Matrix.Norms.L2Operator
open RequestProject.YangMills.SU2QuaternionOperatorNorm

/-! ## The abstract telescope -/

section Telescope

variable {A : Type*} [NormedRing A]

/-- The defect of a group element: its distance to the identity. -/
def defect (u : A) : ℝ := ‖u - 1‖

@[simp] theorem defect_one : defect (1 : A) = 0 := by simp [defect]

theorem defect_nonneg (u : A) : 0 ≤ defect u := norm_nonneg _

/-- One telescope step. -/
theorem defect_mul_le {u v : A} (hu : ‖u‖ ≤ 1) :
    defect (u * v) ≤ defect u + defect v := by
  have hrewrite : u * v - 1 = u * (v - 1) + (u - 1) := by noncomm_ring
  calc ‖u * v - 1‖ = ‖u * (v - 1) + (u - 1)‖ := by rw [hrewrite]
    _ ≤ ‖u * (v - 1)‖ + ‖u - 1‖ := norm_add_le _ _
    _ ≤ ‖u‖ * ‖v - 1‖ + ‖u - 1‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ 1 * ‖v - 1‖ + ‖u - 1‖ := by gcongr
    _ = defect u + defect v := by simp [defect, add_comm]

/-- **The telescope.**  An ordered product of contractive factors, each with
defect at most `ε`, has defect at most `(number of factors) · ε`. -/
theorem defect_prod_le (l : List A) {ε : ℝ}
    (hnorm : ∀ u ∈ l, ‖u‖ ≤ 1) (hdef : ∀ u ∈ l, defect u ≤ ε) :
    defect l.prod ≤ l.length * ε := by
  induction l with
  | nil => simp
  | cons u t ih =>
    have hu : ‖u‖ ≤ 1 := hnorm u (by simp)
    have hstep : defect (u * t.prod) ≤ defect u + defect t.prod := defect_mul_le hu
    have htail : defect t.prod ≤ t.length * ε :=
      ih (fun v hv => hnorm v (by simp [hv])) (fun v hv => hdef v (by simp [hv]))
    have hhead : defect u ≤ ε := hdef u (by simp)
    rw [List.prod_cons, List.length_cons]
    push_cast
    linarith

end Telescope

/-! ## Signed words of stored bonds -/

/-- The `ℓ¹` defect of a quaternionic link variable. -/
def l1defect (q : Quaternion ℝ) : ℝ :=
  |q.re - 1| + |q.imI| + |q.imJ| + |q.imK|

/-- **Signed-link reduction.**  A negative traversal of a stored bond is its
quaternion conjugate, and conjugation leaves the `ℓ¹` defect unchanged; hence
only stored positive bonds need a small-field estimate. -/
@[simp] theorem l1defect_star (q : Quaternion ℝ) : l1defect (star q) = l1defect q := by
  simp [l1defect, abs_neg]

/-- A quaternion is a unit quaternion. -/
def IsUnitQuaternion (q : Quaternion ℝ) : Prop :=
  q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 = 1

theorem isUnitQuaternion_star {q : Quaternion ℝ} (h : IsUnitQuaternion q) :
    IsUnitQuaternion (star q) := by
  simpa [IsUnitQuaternion] using h

theorem star_mul_self_of_unit {q : Quaternion ℝ} (h : IsUnitQuaternion q) :
    star q * q = 1 := by
  rw [Quaternion.star_mul_self, Quaternion.normSq_def', h]
  norm_num

/-- An oriented link: `true` traverses the stored positive bond, `false`
traverses it backwards. -/
def orientedLink : Bool × Quaternion ℝ → Quaternion ℝ
  | (true, q) => q
  | (false, q) => star q

theorem isUnitQuaternion_orientedLink {b : Bool × Quaternion ℝ}
    (h : IsUnitQuaternion b.2) : IsUnitQuaternion (orientedLink b) := by
  obtain ⟨s, q⟩ := b
  cases s
  · exact isUnitQuaternion_star h
  · exact h

theorem l1defect_orientedLink (b : Bool × Quaternion ℝ) :
    l1defect (orientedLink b) = l1defect b.2 := by
  obtain ⟨s, q⟩ := b
  cases s <;> simp [orientedLink]

theorem isUnitQuaternion_iff_normSq {q : Quaternion ℝ} :
    IsUnitQuaternion q ↔ Quaternion.normSq q = 1 := by
  simp [IsUnitQuaternion, Quaternion.normSq_def']

theorem isUnitQuaternion_mul {p q : Quaternion ℝ} (hp : IsUnitQuaternion p)
    (hq : IsUnitQuaternion q) : IsUnitQuaternion (p * q) := by
  rw [isUnitQuaternion_iff_normSq] at hp hq ⊢
  rw [MonoidWithZeroHom.map_mul Quaternion.normSq p q, hp, hq, one_mul]

theorem isUnitQuaternion_one : IsUnitQuaternion 1 := by
  simp [IsUnitQuaternion]

/-- The quaternionic holonomy of a signed word of stored bonds. -/
def qholonomy (w : List (Bool × Quaternion ℝ)) : Quaternion ℝ :=
  (w.map orientedLink).prod

theorem isUnitQuaternion_qholonomy {w : List (Bool × Quaternion ℝ)}
    (hu : ∀ b ∈ w, IsUnitQuaternion b.2) : IsUnitQuaternion (qholonomy w) := by
  induction w with
  | nil => simpa [qholonomy] using isUnitQuaternion_one
  | cons b t ih =>
    have hb : IsUnitQuaternion (orientedLink b) :=
      isUnitQuaternion_orientedLink (hu b (by simp))
    have ht := ih fun c hc => hu c (by simp [hc])
    simpa [qholonomy] using isUnitQuaternion_mul hb ht

/-- The holonomy of a signed word of stored bonds, as an ordered matrix
product. -/
noncomputable def holonomy (w : List (Bool × Quaternion ℝ)) : Matrix (Fin 2) (Fin 2) ℂ :=
  (w.map fun b => su2 (orientedLink b)).prod

@[simp] theorem holonomy_nil : holonomy [] = 1 := by simp [holonomy]

@[simp] theorem holonomy_cons (b : Bool × Quaternion ℝ) (w : List (Bool × Quaternion ℝ)) :
    holonomy (b :: w) = su2 (orientedLink b) * holonomy w := by
  simp [holonomy]

/-- Matrix holonomy and quaternion holonomy are the same object: the
representation is multiplicative. -/
theorem holonomy_eq_su2_qholonomy (w : List (Bool × Quaternion ℝ)) :
    holonomy w = su2 (qholonomy w) := by
  induction w with
  | nil => simp [qholonomy]
  | cons b t ih =>
    rw [holonomy_cons, ih, show qholonomy (b :: t) = orientedLink b * qholonomy t from rfl,
      su2_mul]

theorem holonomy_append (w w' : List (Bool × Quaternion ℝ)) :
    holonomy (w ++ w') = holonomy w * holonomy w' := by
  simp [holonomy, List.map_append, List.prod_append]

/-- The reversed word: traverse the same links in the opposite order with the
opposite orientation. -/
def reverseWord (w : List (Bool × Quaternion ℝ)) : List (Bool × Quaternion ℝ) :=
  (w.map fun b => (!b.1, b.2)).reverse

@[simp] theorem length_reverseWord (w : List (Bool × Quaternion ℝ)) :
    (reverseWord w).length = w.length := by simp [reverseWord]

theorem orientedLink_not (b : Bool × Quaternion ℝ) :
    orientedLink (!b.1, b.2) = star (orientedLink b) := by
  obtain ⟨s, q⟩ := b
  cases s <;> simp [orientedLink]

/-- Traversing a word backwards inverts its holonomy. -/
theorem holonomy_reverseWord_mul (w : List (Bool × Quaternion ℝ))
    (hu : ∀ b ∈ w, IsUnitQuaternion b.2) :
    holonomy (reverseWord w) * holonomy w = 1 := by
  induction w with
  | nil => simp [reverseWord]
  | cons b t ih =>
    have hb : IsUnitQuaternion b.2 := hu b (by simp)
    have ht : ∀ c ∈ t, IsUnitQuaternion c.2 := fun c hc => hu c (by simp [hc])
    have hstar : su2 (star (orientedLink b)) * su2 (orientedLink b) = 1 := by
      rw [← su2_mul, star_mul_self_of_unit (isUnitQuaternion_orientedLink hb), su2_one]
    have hrev : reverseWord (b :: t) = reverseWord t ++ [(!b.1, b.2)] := by
      simp [reverseWord]
    have h1 : holonomy [(!b.1, b.2)] = su2 (star (orientedLink b)) := by
      simp [holonomy, orientedLink_not]
    rw [hrev, holonomy_append, h1, holonomy_cons]
    calc holonomy (reverseWord t) * su2 (star (orientedLink b))
            * (su2 (orientedLink b) * holonomy t)
        = holonomy (reverseWord t)
            * ((su2 (star (orientedLink b)) * su2 (orientedLink b)) * holonomy t) := by
          simp [mul_assoc]
      _ = holonomy (reverseWord t) * holonomy t := by rw [hstar, one_mul]
      _ = 1 := ih ht

/-- **Same object.**  The closed word `Γ ∥ c⁻¹` has holonomy equal to the
relative element `Hol(Γ) · Hol(c)⁻¹`, stated without inverses: its product with
`Hol(c)` is `Hol(Γ)`. -/
theorem holonomy_relative (gamma c : List (Bool × Quaternion ℝ))
    (hc : ∀ b ∈ c, IsUnitQuaternion b.2) :
    holonomy (gamma ++ reverseWord c) * holonomy c = holonomy gamma := by
  rw [holonomy_append, mul_assoc, holonomy_reverseWord_mul c hc, mul_one]

/-! ## The literal defect estimate on the relative holonomy -/

theorem norm_su2_orientedLink {b : Bool × Quaternion ℝ} (h : IsUnitQuaternion b.2) :
    ‖su2 (orientedLink b)‖ = 1 :=
  su2_norm_eq_one (isUnitQuaternion_orientedLink h)

theorem defect_su2_orientedLink_le {b : Bool × Quaternion ℝ} {ε : ℝ}
    (h : l1defect b.2 ≤ ε) : defect (su2 (orientedLink b)) ≤ ε := by
  have := su2_defect_le_l1 (orientedLink b)
  rw [← l1defect] at this
  exact this.trans (by rw [l1defect_orientedLink]; exact h)

/-- **The literal telescope on the relative holonomy.**  A signed word of `n`
stored bonds, each a unit quaternion with `ℓ¹` defect at most `ε`, has
holonomy defect at most `n ε`. -/
theorem holonomy_defect_le (w : List (Bool × Quaternion ℝ)) {ε : ℝ}
    (hu : ∀ b ∈ w, IsUnitQuaternion b.2) (hd : ∀ b ∈ w, l1defect b.2 ≤ ε) :
    defect (holonomy w) ≤ w.length * ε := by
  have := defect_prod_le (l := w.map fun b => su2 (orientedLink b))
    (ε := ε)
    (by
      intro u hux
      simp only [List.mem_map] at hux
      obtain ⟨b, hb, rfl⟩ := hux
      exact le_of_eq (norm_su2_orientedLink (hu b hb)))
    (by
      intro u hux
      simp only [List.mem_map] at hux
      obtain ⟨b, hb, rfl⟩ := hux
      exact defect_su2_orientedLink_le (hd b hb))
  simpa [holonomy] using this

/-- **The canonical `74`-link budget.**  On the canonical `L = 13`, radius-`6`
lane the closed word `Γ_{c,x} ∥ c⁻¹` has at most `74` oriented links, and the
stored-bond budget `1/2048` gives the relative defect `37/1024`. -/
theorem relative_holonomy_defect_le (gamma c : List (Bool × Quaternion ℝ))
    (hlen : gamma.length + c.length ≤ 74)
    (hu : ∀ b ∈ gamma ++ reverseWord c, IsUnitQuaternion b.2)
    (hd : ∀ b ∈ gamma ++ reverseWord c, l1defect b.2 ≤ 1 / 2048) :
    defect (holonomy (gamma ++ reverseWord c)) ≤ 37 / 1024 := by
  have hlen' : ((gamma ++ reverseWord c).length : ℝ) ≤ 74 := by
    have : (gamma ++ reverseWord c).length ≤ 74 := by
      simpa [List.length_append] using hlen
    exact_mod_cast this
  have hbase := holonomy_defect_le (gamma ++ reverseWord c) hu hd
  have : ((gamma ++ reverseWord c).length : ℝ) * (1 / 2048) ≤ 74 * (1 / 2048) := by
    gcongr
  linarith [hbase, this]

/-- The bound is strictly inside the principal-chart admission threshold. -/
theorem relative_holonomy_defect_lt_inv24 (gamma c : List (Bool × Quaternion ℝ))
    (hlen : gamma.length + c.length ≤ 74)
    (hu : ∀ b ∈ gamma ++ reverseWord c, IsUnitQuaternion b.2)
    (hd : ∀ b ∈ gamma ++ reverseWord c, l1defect b.2 ≤ 1 / 2048) :
    defect (holonomy (gamma ++ reverseWord c)) < 1 / 24 :=
  lt_of_le_of_lt (relative_holonomy_defect_le gamma c hlen hu hd) (by norm_num)

end RequestProject.YangMills.RelativeHolonomyDefect
