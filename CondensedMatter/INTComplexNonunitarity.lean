import Mathlib

namespace CondensedMatter
namespace INT

open Complex

/-- Three-component complex triplet d-vector / eta carrier. -/
structure CVec3 where
  x : ℂ
  y : ℂ
  z : ℂ
  deriving Repr

namespace CVec3

def conj (v : CVec3) : CVec3 :=
  ⟨starRingEnd ℂ v.x, starRingEnd ℂ v.y, starRingEnd ℂ v.z⟩

def cross (u v : CVec3) : CVec3 :=
  ⟨u.y * v.z - u.z * v.y,
   u.z * v.x - u.x * v.z,
   u.x * v.y - u.y * v.x⟩

def smul (a : ℂ) (v : CVec3) : CVec3 :=
  ⟨a * v.x, a * v.y, a * v.z⟩

@[ext]
theorem ext {u v : CVec3}
    (hx : u.x = v.x)
    (hy : u.y = v.y)
    (hz : u.z = v.z) :
    u = v := by
  cases u
  cases v
  simp_all

end CVec3

/--
The nonunitarity vector q = i (eta × eta*), exactly as used for the
internally antisymmetric nonunitary triplet state.
-/
def qVector (eta : CVec3) : CVec3 :=
  CVec3.smul I (CVec3.cross eta (CVec3.conj eta))

/--
A canonical chiral/nonunitary triplet representative.  This is not yet the
paper's normalized YbSb2 surface-state choice; it is an exact algebraic witness
for the reusable theorem.
-/
def canonicalEta : CVec3 :=
  ⟨1, I, 0⟩

def canonicalQ : CVec3 :=
  ⟨0, 0, 2⟩

theorem canonical_q_calculation :
    qVector canonicalEta = canonicalQ := by
  apply CVec3.ext <;>
    simp [qVector, canonicalEta, canonicalQ, CVec3.smul, CVec3.cross,
      CVec3.conj]

theorem canonical_q_nonzero :
    qVector canonicalEta ≠ ⟨0, 0, 0⟩ := by
  rw [canonical_q_calculation]
  intro h
  have hz := congrArg CVec3.z h
  norm_num at hz

/--
Complex conjugation reverses the canonical nonunitarity orientation.
For the canonical eta, the z component changes from +2 to -2.
-/
theorem conjugate_canonical_q_z :
    (qVector (CVec3.conj canonicalEta)).z = -2 := by
  simp [qVector, canonicalEta, CVec3.smul, CVec3.cross, CVec3.conj]

end INT
end CondensedMatter
