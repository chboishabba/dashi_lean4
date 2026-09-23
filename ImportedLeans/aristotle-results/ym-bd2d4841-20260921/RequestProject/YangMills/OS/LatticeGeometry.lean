/-
# The time reflection of the periodic four-dimensional lattice

The Wilson lattice of `Lattice/Wilson.lean` has `n+1` sites in every direction
and periodic boundary conditions.  When the time extent is even, `n + 1 = 2L`,
the reflection of the time coordinate

```
  t ↦ -t
```

is an involution of the lattice with two fixed time slices, `t = 0` and `t = L`.
This file builds the corresponding reflection of the links and shows that it is
a `LinkReflectionData`:

* `siteRefl` — the reflection of sites, with the behaviour of the shifts by unit
  lattice vectors (`siteRefl_add_spatial`, `siteRefl_add_time`);
* `tval` — the time coordinate as a natural number, and its values on reflected
  sites (`tval_siteRefl`, `tval_siteRefl_sub_time`);
* `linkRefl` — the reflection of links: spatial links are reflected, and a
  temporal link is carried to the temporal link traversed in the opposite
  direction;
* `wilsonReflData` — the resulting reflection data, whose plane links are the
  spatial links at `t = 0` and `t = L`, whose positive links are the spatial
  links with `0 < t < L` and the temporal links with `t < L`, and whose inverted
  links are the temporal ones.

Everything is proved from the arithmetic of `ZMod (n+1)`.
-/
import Mathlib
import RequestProject.YangMills.Lattice.Wilson
import RequestProject.YangMills.OS.LinkReflection

namespace RequestProject.YangMills.OS

open RequestProject.YangMills.Lattice

variable {n L : ℕ}

/-! ## Arithmetic of the reflected time coordinate -/

theorem neg_sub_one_val (a : ZMod (n + 1)) : (-a - 1).val = n - a.val := by
  have hlt : a.val < n + 1 := ZMod.val_lt a
  have key : (-a - 1) = ((n - a.val : ℕ) : ZMod (n + 1)) := by
    have h0 : ((n - a.val : ℕ) : ZMod (n + 1)) + (a + 1) = 0 := by
      have h1 : ((n - a.val : ℕ) : ZMod (n + 1)) + ((a.val : ℕ) : ZMod (n + 1)) + 1
          = ((n - a.val + a.val + 1 : ℕ) : ZMod (n + 1)) := by push_cast; ring
      rw [ZMod.natCast_val, ZMod.cast_id] at h1
      rw [← add_assoc, h1, show n - a.val + a.val + 1 = n + 1 by omega]
      simp
    linear_combination -h0
  rw [key, ZMod.val_natCast_of_lt (by omega)]

theorem neg_val' (a : ZMod (n + 1)) :
    (-a).val = if a.val = 0 then 0 else (n + 1) - a.val := by
  rw [ZMod.neg_val]
  by_cases h : a = 0
  · simp [h]
  · have hv : a.val ≠ 0 := fun hc => h ((ZMod.val_eq_zero a).1 hc)
    simp [h, hv]

/-! ## Reflection of sites -/

/-- The reflection of a lattice site in the time direction. -/
def siteRefl (x : Site n) : Site n := fun d => if d = 0 then -(x d) else x d

@[simp] theorem siteRefl_time (x : Site n) : siteRefl x 0 = -(x 0) := by simp [siteRefl]

@[simp] theorem siteRefl_space (x : Site n) {d : Fin 4} (hd : d ≠ 0) :
    siteRefl x d = x d := by simp [siteRefl, hd]

theorem siteRefl_involutive (x : Site n) : siteRefl (siteRefl x) = x := by
  funext d
  by_cases hd : d = 0 <;> simp [siteRefl, hd]

theorem unitVec_apply (d e : Fin 4) :
    (unitVec n d) e = if e = d then 1 else 0 := by
  simp [unitVec, Pi.single_apply]

/-- Reflection commutes with a shift in a spatial direction. -/
theorem siteRefl_add_spatial (x : Site n) {d : Fin 4} (hd : d ≠ 0) :
    siteRefl (x + unitVec n d) = siteRefl x + unitVec n d := by
  funext e
  by_cases he : e = 0
  · subst he
    have : (unitVec n d) 0 = 0 := by simp [unitVec_apply, Ne.symm hd]
    simp [siteRefl, this]
  · simp [siteRefl, he]

/-- Reflection turns a shift in the time direction into the opposite shift. -/
theorem siteRefl_add_time (x : Site n) :
    siteRefl (x + unitVec n 0) = siteRefl x - unitVec n 0 := by
  funext e
  by_cases he : e = 0
  · subst he
    have h1 : (unitVec n 0) 0 = 1 := by simp [unitVec_apply]
    simp [siteRefl, h1]
    ring
  · have h2 : (unitVec n 0) e = 0 := by simp [unitVec_apply, he]
    simp [siteRefl, he, h2]

/-- The time coordinate of a site, as a natural number in `[0, n+1)`. -/
def tval (x : Site n) : ℕ := (x 0).val

theorem tval_lt (x : Site n) : tval x < n + 1 := ZMod.val_lt _

theorem tval_siteRefl (x : Site n) :
    tval (siteRefl x) = if tval x = 0 then 0 else (n + 1) - tval x := by
  simp [tval, neg_val']

theorem tval_siteRefl_sub_time (x : Site n) :
    tval (siteRefl x - unitVec n 0) = n - tval x := by
  have h1 : (siteRefl x - unitVec n 0) 0 = -(x 0) - 1 := by
    have : (unitVec n 0) 0 = 1 := by simp [unitVec_apply]
    simp [siteRefl, this]
  simp only [tval, h1]
  exact neg_sub_one_val (x 0)

/-! ## Reflection of links -/

/-- The reflection of a link: a spatial link is reflected, and the temporal link
starting at `x` is carried to the temporal link ending at the reflection of
`x`. -/
def linkRefl (l : Link n) : Link n :=
  if l.2 = 0 then (siteRefl l.1 - unitVec n 0, l.2) else (siteRefl l.1, l.2)

@[simp] theorem linkRefl_snd (l : Link n) : (linkRefl l).2 = l.2 := by
  unfold linkRefl; split <;> rfl

theorem linkRefl_involutive (l : Link n) : linkRefl (linkRefl l) = l := by
  obtain ⟨x, d⟩ := l
  by_cases hd : d = 0
  · subst hd
    have h1 : siteRefl (siteRefl x - unitVec n 0) = x + unitVec n 0 := by
      have := siteRefl_add_time (n := n) (siteRefl x - unitVec n 0)
      calc siteRefl (siteRefl x - unitVec n 0)
          = siteRefl (siteRefl x - unitVec n 0 + unitVec n 0) + unitVec n 0 := by
            rw [siteRefl_add_time]; abel
        _ = x + unitVec n 0 := by rw [sub_add_cancel, siteRefl_involutive]
    simp [linkRefl, h1]
  · simp [linkRefl, hd, siteRefl_involutive]

/-- The reflection of links as a permutation. -/
def linkReflPerm : Equiv.Perm (Link n) :=
  Function.Involutive.toPerm linkRefl linkRefl_involutive

@[simp] theorem linkReflPerm_apply (l : Link n) : linkReflPerm l = linkRefl l := rfl

/-! ## The reflection data of the Wilson lattice -/

variable (n L)

/-- The spatial links in the two reflection planes `t = 0` and `t = L`. -/
def planeLinks : Finset (Link n) :=
  Finset.univ.filter fun l => l.2 ≠ 0 ∧ (tval l.1 = 0 ∨ tval l.1 = L)

/-- The links strictly on the positive side: the spatial links with
`0 < t < L` and the temporal links with `t < L`. -/
def posLinks : Finset (Link n) :=
  Finset.univ.filter fun l =>
    if l.2 = 0 then tval l.1 < L else (0 < tval l.1 ∧ tval l.1 < L)

/-- The temporal links, whose variables the reflection inverts. -/
def temporalLinks : Finset (Link n) := Finset.univ.filter fun l => l.2 = 0

variable {n L}

@[simp] theorem mem_planeLinks {l : Link n} :
    l ∈ planeLinks n L ↔ (l.2 ≠ 0 ∧ (tval l.1 = 0 ∨ tval l.1 = L)) := by
  simp [planeLinks]

@[simp] theorem mem_posLinks {l : Link n} :
    l ∈ posLinks n L ↔
      (if l.2 = 0 then tval l.1 < L else (0 < tval l.1 ∧ tval l.1 < L)) := by
  simp [posLinks]

@[simp] theorem mem_temporalLinks {l : Link n} : l ∈ temporalLinks n ↔ l.2 = 0 := by
  simp [temporalLinks]

theorem tval_linkRefl_time {l : Link n} (hl : l.2 = 0) :
    tval (linkRefl l).1 = n - tval l.1 := by
  simp only [linkRefl, hl]
  exact tval_siteRefl_sub_time l.1

theorem tval_linkRefl_space {l : Link n} (hl : l.2 ≠ 0) :
    tval (linkRefl l).1 = if tval l.1 = 0 then 0 else (n + 1) - tval l.1 := by
  simp only [linkRefl, if_neg hl]
  exact tval_siteRefl (n := n) l.1

/-- A site in a reflection plane is fixed by the reflection. -/
theorem siteRefl_eq_self (hN : n + 1 = 2 * L) {x : Site n}
    (hx : tval x = 0 ∨ tval x = L) : siteRefl x = x := by
  funext d
  by_cases hd : d = 0
  · subst hd
    simp only [siteRefl_time]
    rcases hx with hx | hx
    · have : x 0 = 0 := (ZMod.val_eq_zero (x 0)).1 hx
      simp [this]
    · have hxL : x 0 = ((L : ℕ) : ZMod (n + 1)) := by
        calc x 0 = ((tval x : ℕ) : ZMod (n + 1)) := by
              simp [tval, ZMod.natCast_val, ZMod.cast_id]
          _ = ((L : ℕ) : ZMod (n + 1)) := by rw [hx]
      have h2 : ((L : ℕ) : ZMod (n + 1)) + ((L : ℕ) : ZMod (n + 1)) = 0 := by
        have : ((L + L : ℕ) : ZMod (n + 1)) = ((n + 1 : ℕ) : ZMod (n + 1)) := by
          congr 1; omega
        simpa using this
      rw [hxL]
      linear_combination -h2
  · simp [siteRefl, hd]

/-- **The reflection data of the periodic Wilson lattice with even time
extent.** -/
noncomputable def wilsonReflData (hN : n + 1 = 2 * L) :
    LinkReflectionData (Link n) where
  r := linkReflPerm
  plane := planeLinks n L
  pos := posLinks n L
  inverted := temporalLinks n
  r_involutive := by
    intro l; simpa using linkRefl_involutive l
  plane_not_pos := by
    intro l hl hpos
    rw [mem_planeLinks] at hl
    rw [mem_posLinks, if_neg hl.1] at hpos
    rcases hl.2 with h | h <;> omega
  r_plane := by
    intro l hl
    rw [mem_planeLinks] at hl
    obtain ⟨x, d⟩ := l
    simp only at hl
    simp [linkRefl, hl.1, siteRefl_eq_self hN hl.2]
  r_pos_not_plane := by
    intro l hl
    simp only [linkReflPerm_apply]
    rw [mem_posLinks] at hl
    by_cases hd : l.2 = 0
    · rw [mem_planeLinks]
      simp [linkRefl_snd, hd]
    · rw [if_neg hd] at hl
      rw [mem_planeLinks]
      rintro ⟨-, hcase⟩
      rw [tval_linkRefl_space hd] at hcase
      have hlt := tval_lt l.1
      rw [if_neg (by omega : ¬ tval l.1 = 0)] at hcase
      omega
  r_pos_not_pos := by
    intro l hl
    simp only [linkReflPerm_apply]
    rw [mem_posLinks] at hl
    by_cases hd : l.2 = 0
    · rw [if_pos hd] at hl
      rw [mem_posLinks, linkRefl_snd, if_pos hd, tval_linkRefl_time hd]
      have hlt := tval_lt l.1
      omega
    · rw [if_neg hd] at hl
      rw [mem_posLinks, linkRefl_snd, if_neg hd, tval_linkRefl_space hd,
        if_neg (by omega : ¬ tval l.1 = 0)]
      have hlt := tval_lt l.1
      omega
  r_neg := by
    intro l hplane hpos
    simp only [linkReflPerm_apply]
    rw [mem_planeLinks] at hplane
    rw [mem_posLinks] at hpos
    by_cases hd : l.2 = 0
    · rw [if_pos hd] at hpos
      rw [mem_posLinks, linkRefl_snd, if_pos hd, tval_linkRefl_time hd]
      have hlt := tval_lt l.1
      omega
    · rw [if_neg hd] at hpos
      have hne : ¬ (tval l.1 = 0 ∨ tval l.1 = L) := fun hc => hplane ⟨hd, hc⟩
      rw [mem_posLinks, linkRefl_snd, if_neg hd, tval_linkRefl_space hd,
        if_neg (by omega : ¬ tval l.1 = 0)]
      have hlt := tval_lt l.1
      omega
  inverted_not_plane := by
    intro l hl
    rw [mem_temporalLinks] at hl
    rw [mem_planeLinks]
    simp [hl]
  inverted_r := by
    intro l
    simp only [linkReflPerm_apply, mem_temporalLinks, linkRefl_snd]

@[simp] theorem wilsonReflData_r (hN : n + 1 = 2 * L) (l : Link n) :
    (wilsonReflData hN).r l = linkRefl l := rfl

@[simp] theorem wilsonReflData_plane (hN : n + 1 = 2 * L) :
    (wilsonReflData hN).plane = planeLinks n L := rfl

@[simp] theorem wilsonReflData_pos (hN : n + 1 = 2 * L) :
    (wilsonReflData hN).pos = posLinks n L := rfl

@[simp] theorem wilsonReflData_inverted (hN : n + 1 = 2 * L) :
    (wilsonReflData hN).inverted = temporalLinks n := rfl

end RequestProject.YangMills.OS

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.OS

#print axioms siteRefl_involutive
#print axioms linkRefl_involutive
#print axioms wilsonReflData

end Audit
