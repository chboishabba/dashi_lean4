import Integration.Base369Heisenberg
import Integration.Base369Schrodinger

/-!
# Centre-preserving shear / centre-inverting reflection on repo-native H(n)

The actual source group is Base369Heisenberg.H n, whose multiplication uses
cocycle dot(y_g,x_h). In this UNSYMMETRIZED convention the upper shear
(x,y) -> (x+y,y) requires central correction 2*dot(y,y).
The relative-F2 reflection (x,y)->(x,-y) inverts the centre.
Both lift to group endomorphisms.

This is a finite-coordinate theorem, not a proof that actual E(F4) carries
this pairing or that its unproved P,Q chart is an additive equivalence.
-/

namespace Integration.OggSSPP2TernaryHeisenbergAction

open Integration.Base369Heisenberg

variable {n : ℕ}

theorem dot_comm (a b : X n) :
    dot a b = dot b a := by
  simp [dot, mul_comm]

theorem quadratic_shear_cocycle (y y' : X n) :
    (2 : F3) * dot (y+y') (y+y') =
      2*dot y y + 2*dot y' y' + dot y y' := by
  have hfour : (4 : F3) = 1 := by decide
  calc
    (2 : F3) * dot (y+y') (y+y')
        = 2*dot y y + 2*dot y' y'
            + 4*dot y y' := by
          rw [dot_add_left, dot_add_right, dot_add_right,
            dot_comm y' y]
          ring
    _ = 2*dot y y + 2*dot y' y' + dot y y' := by
          rw [hfour]
          ring

def shearLift (g : H n) : H n :=
  ⟨g.x+g.y, g.y, g.z + 2*dot g.y g.y⟩

def reflectionLift (g : H n) : H n :=
  ⟨g.x, -g.y, -g.z⟩

def central (z : F3) : H n := ⟨0,0,z⟩

theorem shearLift_mul (g h : H n) :
    shearLift (g*h) = shearLift g * shearLift h := by
  refine H.ext' ?_ ?_ ?_
  · change (g.x+h.x)+(g.y+h.y) =
      (g.x+g.y)+(h.x+h.y)
    abel
  · rfl
  · change
      g.z+h.z+dot g.y h.x
        + 2*dot (g.y+h.y) (g.y+h.y)
      =
      (g.z+2*dot g.y g.y)
        + (h.z+2*dot h.y h.y)
        + dot g.y (h.x+h.y)
    rw [quadratic_shear_cocycle, dot_add_right]
    ring

theorem reflectionLift_mul (g h : H n) :
    reflectionLift (g*h) =
      reflectionLift g * reflectionLift h := by
  refine H.ext' ?_ ?_ ?_
  · rfl
  · change -(g.y+h.y) = -g.y + -h.y
    abel
  · change
      -(g.z+h.z+dot g.y h.x)
        = -g.z + -h.z + dot (-g.y) h.x
    rw [dot_neg_left]
    ring

theorem shearLift_central (z : F3) :
    shearLift (central (n:=n) z) = central z := by
  simp [shearLift,central]

theorem reflectionLift_central (z : F3) :
    reflectionLift (central (n:=n) z) = central (-z) := by
  simp [reflectionLift,central]

theorem reflectionLift_square (g : H n) :
    reflectionLift (reflectionLift g) = g := by
  cases g
  simp [reflectionLift]

theorem rankOne_card :
    Fintype.card (H 1) = 27 := by
  rw [card_H]
  norm_num

theorem rankOne_schrodinger_dim :
    Module.finrank ℂ (X 1 → ℂ) = 3 := by
  rw [Integration.Base369Schrodinger.finrank_V]
  norm_num

theorem rankOne_schrodinger_irreducible
    {W : Submodule ℂ (X 1 → ℂ)}
    (hW : Integration.Base369Schrodinger.Invariant W)
    (hne : W ≠ ⊥) :
    W = ⊤ :=
  Integration.Base369Schrodinger.schrodinger_irreducible hW hne

def actualEllipticPairingTransportPaid : Bool := false


/-- Coordinate shear iterated three times is the identity in characteristic 3,
including its quadratic central correction. -/
theorem shearLift_cube (g : H n) :
    shearLift (shearLift (shearLift g)) = g := by
  have h3 : (3 : F3) = 0 := by decide
  refine H.ext' ?_ ?_ ?_
  · change ((g.x+g.y)+g.y)+g.y = g.x
    have h : g.y+g.y+g.y = (3 : F3) • g.y := by
      simp [three_nsmul]
    calc
      ((g.x+g.y)+g.y)+g.y =
          g.x + ((3 : F3) • g.y) := by
            rw [← h]
            abel
      _ = g.x := by
          have hzero : (3 : ℕ) • g.y = 0 := by
            ext i
            simp [three_nsmul, h3]
          simpa using congrArg (fun a => g.x+a) hzero
  · rfl
  · change (g.z + 2*dot g.y g.y)
      + 2*dot g.y g.y + 2*dot g.y g.y = g.z
    have htwo : (6 : F3) = 0 := by decide
    calc
      (g.z + 2*dot g.y g.y) + 2*dot g.y g.y
         + 2*dot g.y g.y = g.z + (6:F3)*dot g.y g.y := by ring
      _ = g.z := by rw [htwo]; ring

/-- Reflection reverses the complex phase of the existing Schrödinger
central character.  This is stronger than observing a determinant sign. -/
theorem reflection_conjugates_central_phase (z : F3) :
    Integration.Base369Schrodinger.chi
        ((reflectionLift (central (n:=1) z)).z)
      * Integration.Base369Schrodinger.chi z = 1 := by
  change Integration.Base369Schrodinger.chi (-z)
    * Integration.Base369Schrodinger.chi z = 1
  rw [← Integration.Base369Schrodinger.chi_add]
  simp [Integration.Base369Schrodinger.chi_zero]

end Integration.OggSSPP2TernaryHeisenbergAction
