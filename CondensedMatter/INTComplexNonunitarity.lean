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

/-!
Paper-specific YbSb₂ witness.

Kataria et al. use
  η = (1/√2) (1, exp(iπ/4), 0)
for the displayed surface calculation.  We represent
  exp(iπ/4) = (1/√2)(1+i)
exactly, avoiding transcendental normalization machinery.
-/

def invSqrtTwo : ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

def paperPhasePiOverFour : ℂ :=
  invSqrtTwo * (1 + I)

def paperEta : CVec3 :=
  ⟨invSqrtTwo, invSqrtTwo * paperPhasePiOverFour, 0⟩

theorem invSqrtTwo_ne_zero :
    invSqrtTwo ≠ 0 := by
  have hsqrt : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hcast : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hsqrt
  exact inv_ne_zero hcast

/--
The exact paper-selected η has a nonzero z-directed nonunitarity vector.
Before reducing √2 powers, the literal value is 2 (1/√2)^3.
-/
theorem paper_q_z_formula :
    (qVector paperEta).z = 2 * invSqrtTwo ^ 3 := by
  simp [qVector, paperEta, paperPhasePiOverFour, invSqrtTwo,
    CVec3.smul, CVec3.cross, CVec3.conj]
  ring

theorem paper_q_nonzero :
    qVector paperEta ≠ ⟨0, 0, 0⟩ := by
  intro h
  have hz : (qVector paperEta).z = 0 := congrArg CVec3.z h
  rw [paper_q_z_formula] at hz
  have hpow : invSqrtTwo ^ 3 ≠ 0 :=
    pow_ne_zero 3 invSqrtTwo_ne_zero
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  exact (mul_ne_zero htwo hpow) hz

end INT
end CondensedMatter
