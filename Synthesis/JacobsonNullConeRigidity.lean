import Mathlib

namespace Synthesis.JacobsonNullConeRigidity

/-- Concrete coordinates for the flat 1+3 Lorentzian carrier. -/
@[ext] structure Vec4 where
  t : ℝ
  x : ℝ
  y : ℝ
  z : ℝ

/-- Symmetric rank-two tensor, stored by its ten independent components. -/
@[ext] structure SymTensor4 where
  tt : ℝ
  tx : ℝ
  ty : ℝ
  tz : ℝ
  xx : ℝ
  xy : ℝ
  xz : ℝ
  yy : ℝ
  yz : ℝ
  zz : ℝ

/-- Minkowski quadratic form with signature (-,+,+,+). -/
def minkowskiQuad (v : Vec4) : ℝ :=
  -(v.t * v.t) + v.x * v.x + v.y * v.y + v.z * v.z

/-- Quadratic contraction T_ab v^a v^b for a symmetric tensor. -/
def contract (T : SymTensor4) (v : Vec4) : ℝ :=
  T.tt * v.t * v.t
    + 2 * T.tx * v.t * v.x
    + 2 * T.ty * v.t * v.y
    + 2 * T.tz * v.t * v.z
    + T.xx * v.x * v.x
    + 2 * T.xy * v.x * v.y
    + 2 * T.xz * v.x * v.z
    + T.yy * v.y * v.y
    + 2 * T.yz * v.y * v.z
    + T.zz * v.z * v.z

/-- Scalar multiple λ η_ab of the Minkowski metric. -/
def metricMultiple (λ : ℝ) : SymTensor4 where
  tt := -λ
  tx := 0
  ty := 0
  tz := 0
  xx := λ
  xy := 0
  xz := 0
  yy := λ
  yz := 0
  zz := λ

/-- Finite algebraic null-cone rigidity in flat 3+1 dimensions.

If a symmetric tensor has zero quadratic contraction on every Minkowski-null
vector, then it is a scalar multiple of the Minkowski metric.  The proof only
needs the six coordinate null directions (1,±1,0,0), etc., plus the rational
3-4-5 null directions (5,3,4,0) and permutations to eliminate spatial cross
terms. -/
theorem nullConeRigidity
    (T : SymTensor4)
    (h : ∀ v : Vec4, minkowskiQuad v = 0 → contract T v = 0) :
    ∃ λ : ℝ, T = metricMultiple λ := by
  have hxP := h ⟨1, 1, 0, 0⟩ (by norm_num [minkowskiQuad])
  have hxM := h ⟨1, -1, 0, 0⟩ (by norm_num [minkowskiQuad])
  have hyP := h ⟨1, 0, 1, 0⟩ (by norm_num [minkowskiQuad])
  have hyM := h ⟨1, 0, -1, 0⟩ (by norm_num [minkowskiQuad])
  have hzP := h ⟨1, 0, 0, 1⟩ (by norm_num [minkowskiQuad])
  have hzM := h ⟨1, 0, 0, -1⟩ (by norm_num [minkowskiQuad])
  norm_num [contract] at hxP hxM hyP hyM hzP hzM

  have htx : T.tx = 0 := by linarith [hxP, hxM]
  have hty : T.ty = 0 := by linarith [hyP, hyM]
  have htz : T.tz = 0 := by linarith [hzP, hzM]
  have hxx : T.xx = -T.tt := by linarith [hxP, hxM]
  have hyy : T.yy = -T.tt := by linarith [hyP, hyM]
  have hzz : T.zz = -T.tt := by linarith [hzP, hzM]

  have hxy0 := h ⟨5, 3, 4, 0⟩ (by norm_num [minkowskiQuad])
  have hxz0 := h ⟨5, 3, 0, 4⟩ (by norm_num [minkowskiQuad])
  have hyz0 := h ⟨5, 0, 3, 4⟩ (by norm_num [minkowskiQuad])
  norm_num [contract] at hxy0 hxz0 hyz0

  have hxy : T.xy = 0 := by
    rw [htx, hty, hxx, hyy] at hxy0
    linarith
  have hxz : T.xz = 0 := by
    rw [htx, htz, hxx, hzz] at hxz0
    linarith
  have hyz : T.yz = 0 := by
    rw [hty, htz, hyy, hzz] at hyz0
    linarith

  refine ⟨-T.tt, ?_⟩
  ext <;> simp [metricMultiple, htx, hty, htz, hxx, hyy, hzz, hxy, hxz, hyz]

/-- The concrete theorem pays the algebraic 3+1 rigidity leaf; applying it
pointwise to a smooth Lorentzian manifold still requires a same-carrier
continuum/fibrewise bridge. -/
def finiteLorentzianNullConeRigidityOwned : Bool := true

def continuumFibrewiseTransportStillRequired : Bool := true

def curvatureOrStressEnergyNotConstructedHere : Bool := true

end Synthesis.JacobsonNullConeRigidity
