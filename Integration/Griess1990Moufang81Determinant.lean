import Mathlib

/-!
# Griess 1990 order-81 Moufang loop: associator is the F₃³ determinant

EXTERNAL PRIMARY ROOT:
Robert L. Griess Jr., "A Moufang loop, the exceptional Jordan algebra,
and a cubic form in 27 variables", Journal of Algebra 131 (1990),
281–293, DOI 10.1016/0021-8693(90)90176-O.

The source-selected phase polynomial is
g(x,y) = -x₀x₁y₂ - x₂y₀y₁ + x₁x₂y₀ + x₀y₁y₂.
It defines a central-extension loop on F₃³ × F₃, 81 elements.
Its ASSOCIATOR equals det(x,y,z) in F₃; thus its nonassociativity is
literally an alternating three-form, not a numerological echo of 888.

Provenance is a source formula translated into Lean. The derivation and
all 19,683 grade triples were checked independently in local exact
Python; this Lean module is SOURCE-WRITTEN, NOT kernel-checked in the
authoring environment. It does not identify the separate Monster 3B
group, its Vnatural weight-two Griess mode, or physical space.
-/

namespace Integration.Griess1990Moufang81Determinant

abbrev Grade := Fin 3 → ZMod 3

/-- Griess's source phase polynomial: no artificial cocycle selected. -/
def g (x y : Grade) : ZMod 3 :=
  -(x 0)*(x 1)*(y 2) - (x 2)*(y 0)*(y 1)
    + (x 1)*(x 2)*(y 0) + (x 0)*(y 1)*(y 2)

def det3 (x y z : Grade) : ZMod 3 :=
  x 0 * (y 1*z 2 - y 2*z 1)
    - x 1 * (y 0*z 2 - y 2*z 0)
    + x 2 * (y 0*z 1 - y 1*z 0)

def associator (x y z : Grade) : ZMod 3 :=
  g x y + g (x + y) z - g y z - g x (y + z)

/-- The exact integral-polynomial difference is
3*y₁*(-x₀*z₂ + x₂*z₀), hence zero in characteristic three. -/
theorem associator_eq_determinant (x y z : Grade) :
    associator x y z = det3 x y z := by
  have hthree : (3 : ZMod 3) = 0 := by decide
  calc
    associator x y z =
      det3 x y z + (3 : ZMod 3) * y 1 *
        (-(x 0)*(z 2) + (x 2)*(z 0)) := by
          simp only [associator, g, det3, Pi.add_apply]
          ring
    _ = det3 x y z := by simp [hthree]

theorem phase_is_symmetric (x y : Grade) : g x y = g y x := by
  simp only [g]
  ring

/-- A loop element is a 3-vector grade plus its central phase. -/
structure Loop81 where
  grade : Grade
  central : ZMod 3
  deriving DecidableEq, Fintype

def multiply (a b : Loop81) : Loop81 :=
  ⟨a.grade + b.grade, a.central + b.central + g a.grade b.grade⟩

def identity : Loop81 := ⟨0, 0⟩

/-- Griess's source quotient is COMMUTATIVE but NONASSOCIATIVE. -/
theorem multiplication_commutative (a b : Loop81) :
    multiply a b = multiply b a := by
  cases a with
  | mk x c =>
    cases b with
    | mk y d =>
      simp only [multiply, Loop81.mk.injEq]
      constructor
      · exact add_comm x y
      · rw [phase_is_symmetric]
        ring

theorem g_zero_left (x : Grade) : g 0 x = 0 := by
  simp [g]
theorem g_zero_right (x : Grade) : g x 0 = 0 := by
  simp [g]

theorem identity_left (a : Loop81) : multiply identity a = a := by
  cases a
  simp [multiply, identity, g_zero_left]

theorem identity_right (a : Loop81) : multiply a identity = a := by
  cases a
  simp [multiply, identity, g_zero_right]

/-- The characteristic-three Moufang phase identity reduces to
an integer polynomial with factor 3:
3*(-x₀*y₁*z₂ - x₀*y₂*z₁ + x₂*y₀*z₁ + x₂*y₁*z₀). -/
theorem phase_moufang (x y z : Grade) :
    g x y + g z x + g (x+y) (z+x) =
      g y z + g (y+z) x + g x (y+z+x) := by
  have hthree : (3 : ZMod 3) = 0 := by decide
  have heq :
      g x y + g z x + g (x+y) (z+x) =
      g y z + g (y+z) x + g x (y+z+x) +
        (3 : ZMod 3) *
        (-(x 0)*(y 1)*(z 2) - (x 0)*(y 2)*(z 1)
          + (x 2)*(y 0)*(z 1) + (x 2)*(y 1)*(z 0)) := by
      simp only [g, Pi.add_apply]
      ring
  simpa [hthree] using heq

/-- Actual grade-phase Moufang law for the entire 81-element loop.
This is a finite algebra law, NOT a physical/VOA statement. -/
theorem moufang_identity (a b c : Loop81) :
    multiply (multiply a b) (multiply c a) =
    multiply a (multiply (multiply b c) a) := by
  cases a with
  | mk x p =>
    cases b with
    | mk y q =>
      cases c with
      | mk z r =>
        simp only [multiply, Loop81.mk.injEq]
        constructor
        · simp only [Pi.add_apply]
          ext i
          simp only [Pi.add_apply]
          abel
        · simp only [Pi.add_apply]
          rw [phase_moufang]
          ring

end Integration.Griess1990Moufang81Determinant
