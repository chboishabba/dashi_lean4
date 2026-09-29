import Mathlib

/-!
The ternary Heisenberg model for a symplectic basis of F₃².

NOT an identification with E(F₄), nor a construction of the actual Weil
pairing: both of those genuine arithmetic obligations remain open in
OggSSPP2F4ActualGroupGenerators.  This provides the exact finite target in
which to test the proposed shear and relative-F₂-Frobenius reflection.

The alternating group cocycle is 2ω(v,w), since 2=1/2 over F₃.
-/

namespace Integration.OggSSPP2TernaryHeisenbergAction

abbrev F3 := ZMod 3

structure Plane where
  x : F3
  y : F3
  deriving DecidableEq, Fintype

def vadd (a b : Plane) : Plane := ⟨a.x+b.x,a.y+b.y⟩
def omega (a b : Plane) : F3 := a.x*b.y-a.y*b.x
def shear (a : Plane) : Plane := ⟨a.x+a.y,a.y⟩
def reflection (a : Plane) : Plane := ⟨a.x,-a.y⟩

theorem omega_shear (a b : Plane) :
    omega (shear a) (shear b) = omega a b := by
  simp only [omega,shear]
  ring

theorem omega_reflection (a b : Plane) :
    omega (reflection a) (reflection b) = -omega a b := by
  simp only [omega,reflection]
  ring

structure Heisenberg27 where
  z : F3
  v : Plane
  deriving DecidableEq, Fintype

def mulH (a b : Heisenberg27) : Heisenberg27 :=
  ⟨a.z+b.z+2*omega a.v b.v,vadd a.v b.v⟩
def unitH : Heisenberg27 := ⟨0,⟨0,0⟩⟩
def center (z : F3) : Heisenberg27 := ⟨z,⟨0,0⟩⟩
def liftShear (a : Heisenberg27) : Heisenberg27 :=
  ⟨a.z,shear a.v⟩
def liftReflection (a : Heisenberg27) : Heisenberg27 :=
  ⟨-a.z,reflection a.v⟩

theorem mulH_assoc (a b c : Heisenberg27) :
    mulH (mulH a b) c = mulH a (mulH b c) := by
  cases a with | mk za ⟨xa,ya⟩ =>
  cases b with | mk zb ⟨xb,yb⟩ =>
  cases c with | mk zc ⟨xc,yc⟩ =>
  simp only [mulH,vadd,omega,Heisenberg27.mk.injEq,Plane.mk.injEq]
  constructor
  · ring
  · constructor <;> ring

theorem mulH_unit (a : Heisenberg27) :
    mulH a unitH = a := by
  cases a with | mk z ⟨x,y⟩ =>
  simp [mulH,unitH,vadd,omega]

theorem unit_mulH (a : Heisenberg27) :
    mulH unitH a = a := by
  cases a with | mk z ⟨x,y⟩ =>
  simp [mulH,unitH,vadd,omega]

theorem liftShear_mulH (a b : Heisenberg27) :
    liftShear (mulH a b) = mulH (liftShear a) (liftShear b) := by
  cases a with | mk z ⟨x,y⟩ =>
  cases b with | mk w ⟨u,v⟩ =>
  simp only [liftShear,mulH,shear,vadd,omega,
    Heisenberg27.mk.injEq,Plane.mk.injEq]
  constructor
  · ring
  · constructor <;> ring

theorem liftReflection_mulH (a b : Heisenberg27) :
    liftReflection (mulH a b) =
      mulH (liftReflection a) (liftReflection b) := by
  cases a with | mk z ⟨x,y⟩ =>
  cases b with | mk w ⟨u,v⟩ =>
  simp only [liftReflection,mulH,reflection,vadd,omega,
    Heisenberg27.mk.injEq,Plane.mk.injEq]
  constructor
  · ring
  · constructor <;> ring

theorem shear_preserves_center (z : F3) :
    liftShear (center z) = center z := by
  simp [liftShear,center,shear]

theorem reflection_inverts_center (z : F3) :
    liftReflection (center z) = center (-z) := by
  simp [liftReflection,center,reflection]

theorem reflection_squared (a : Heisenberg27) :
    liftReflection (liftReflection a) = a := by
  cases a with | mk z ⟨x,y⟩ =>
  simp [liftReflection,reflection]

theorem carrier_cardinality :
    Fintype.card Heisenberg27 = 27 := by decide

/-- A selected primitive third-root central character is exchanged with its
inverse by relative F₂-Frobenius, not fixed as by the shear. -/
theorem reflection_nontrivial_center :
    liftReflection (center 1) = center (2 : F3) := by
  simpa [show (-1 : F3) = 2 by decide] using
    reflection_inverts_center (1 : F3)

/-- The arithmetic transport to Mathlib's genuine E[3] remains unproved. -/
def actualEllipticTorsionTransportPaid : Bool := false

end Integration.OggSSPP2TernaryHeisenbergAction
