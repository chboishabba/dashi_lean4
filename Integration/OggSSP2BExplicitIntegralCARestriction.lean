import Mathlib

/-!
# An explicit rank-three integral C4 module and its restricted 2B Tate classes

This file constructs an ACTUAL integral lattice (not a toy prime-address
carrier): Z^3 with generator
  g(a,b,c) = (c,a-c,b+c)
and h=g^2:
  h(a,b,c) = (b+c,-b,a+b).
It arises as the quotient of the regular permutation C4 lattice by its
alternating sign line. The character table is rank=3, tr(g)=1, tr(h)=-1,
matching the SOURCE C^A family of the Carnahan–Urano 4A(2B) decomposition.

The source-theorem identity of this particular quotient presentation
with the named indecomposable C^A still needs a cited integral
classification isomorphism. The following C2 Tate *computation* of the
displayed Z^3 action is unconditional.

For h acting on this lattice, Hhat0=0; Hhat1=Z/2, with the mod-two
obstruction represented by the middle coordinate b. The basis-free
cokernel/quotient equivalence is a separate library integration task.
-/

namespace Integration.OggSSP2BExplicitIntegralCARestriction

structure Lattice3 where
  a : ℤ
  b : ℤ
  c : ℤ
  deriving Repr, DecidableEq

def generator4 (v : Lattice3) : Lattice3 :=
  ⟨v.c, v.a - v.c, v.b + v.c⟩

def involution2 (v : Lattice3) : Lattice3 :=
  ⟨v.b + v.c, -v.b, v.a + v.b⟩

def norm2 (v : Lattice3) : Lattice3 :=
  ⟨v.a + v.b + v.c, 0, v.a + v.b + v.c⟩

def diff2 (v : Lattice3) : Lattice3 :=
  ⟨v.b + v.c - v.a, -2*v.b, v.a + v.b - v.c⟩

def oddClass : Lattice3 := ⟨0, 1, -1⟩

theorem generator_square_is_actual_involution (v : Lattice3) :
    generator4 (generator4 v) = involution2 v := by
  cases v with
  | mk a b c =>
    simp [generator4, involution2]
    <;> ring

theorem involution_square (v : Lattice3) :
    involution2 (involution2 v) = v := by
  cases v with
  | mk a b c =>
    simp [involution2]
    <;> ring

theorem generator_fourth_is_identity (v : Lattice3) :
    generator4 (generator4 (generator4 (generator4 v))) = v := by
  rw [generator_square_is_actual_involution]
  rw [generator_square_is_actual_involution]
  exact involution_square v

theorem norm2_zero_iff (v : Lattice3) :
    norm2 v = ⟨0,0,0⟩ ↔ v.a + v.b + v.c = 0 := by
  constructor
  · intro h
    have ha := congrArg Lattice3.a h
    simpa [norm2] using ha
  · intro h
    cases v with
    | mk a b c =>
      simp only [Lattice3.a, Lattice3.b, Lattice3.c] at h
      simp [norm2, h]

theorem fixed_iff (v : Lattice3) :
    involution2 v = v ↔ v.b = 0 ∧ v.a = v.c := by
  constructor
  · intro h
    have ha := congrArg Lattice3.a h
    have hb := congrArg Lattice3.b h
    have hc := congrArg Lattice3.c h
    simp only [involution2] at ha hb hc
    constructor <;> omega
  · rintro ⟨hb, hac⟩
    cases v with
    | mk a b c =>
      simp only [Lattice3.a, Lattice3.b, Lattice3.c] at hb hac
      simp [involution2, hb, hac]

theorem fixed_is_an_actual_norm
    (v : Lattice3) (hfix : involution2 v = v) :
    ∃ u : Lattice3, norm2 u = v := by
  have ⟨hb,hac⟩ := (fixed_iff v).mp hfix
  refine ⟨⟨v.a,0,0⟩, ?_⟩
  cases v with
  | mk a b c =>
    simp only [Lattice3.a, Lattice3.b, Lattice3.c] at hb hac
    simp [norm2, hb, hac]

theorem diff2_has_even_middle (v : Lattice3) :
    (diff2 v).b = 2 * (-v.b) := by
  simp [diff2]
  ring

theorem norm2_of_diff2_zero (v : Lattice3) :
    norm2 (diff2 v) = ⟨0,0,0⟩ := by
  cases v with
  | mk a b c =>
    simp [norm2, diff2]
    <;> ring

theorem even_middle_kernel_is_diff
    (v : Lattice3)
    (hker : norm2 v = ⟨0,0,0⟩)
    (k : ℤ) (heven : v.b = 2*k) :
    ∃ u : Lattice3, diff2 u = v := by
  have hs : v.a + v.b + v.c = 0 :=
    (norm2_zero_iff v).mp hker
  refine ⟨⟨0,-k,v.a+k⟩, ?_⟩
  cases v with
  | mk a b c =>
    simp only [Lattice3.a, Lattice3.b, Lattice3.c] at hs heven
    simp [diff2]
    <;> omega

theorem odd_class_is_a_cocycle :
    norm2 oddClass = ⟨0,0,0⟩ := by
  decide

theorem odd_class_not_a_coboundary :
    ¬ ∃ u : Lattice3, diff2 u = oddClass := by
  rintro ⟨u, hu⟩
  have hmid := congrArg Lattice3.b hu
  simp [diff2, oddClass] at hmid
  omega

theorem kernel_has_exactly_two_coboundary_coset_forms
    (v : Lattice3) (hker : norm2 v = ⟨0,0,0⟩) :
    (∃ u, diff2 u = v) ∨
    (∃ u, (diff2 u).a = v.a ∧
          (diff2 u).b + 1 = v.b ∧
          (diff2 u).c - 1 = v.c) := by
  have hs : v.a + v.b + v.c = 0 :=
    (norm2_zero_iff v).mp hker
  obtain ⟨k, hk | hk⟩ :
      ∃ k : ℤ, v.b = 2*k ∨ v.b = 2*k+1 := by omega
  · left
    exact even_middle_kernel_is_diff v hker k hk
  · right
    refine ⟨⟨0,-k,v.a+k⟩, ?_⟩
    simp [diff2]
    constructor
    · omega
    constructor <;> omega

end Integration.OggSSP2BExplicitIntegralCARestriction
