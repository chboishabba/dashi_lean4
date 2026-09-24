import Synthesis.MillenniumHodgeCP1SingularTransport
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.Tactic

/-!
# Degree-two homology of the tetrahedral simplicial 2-sphere

The boundary of the standard 3-simplex is the canonical finite simplicial
model of S^2.  We compute its top chain homology explicitly over Q.

With oriented faces 012,013,023,123 and edges 01,02,03,12,13,23,
the boundary equations force every 2-cycle to be a unique multiple of

  -[012] + [013] - [023] + [123].

There are no nondegenerate 3-simplices in the boundary, so there are no
degree-three boundaries.  Thus the finite normalized model has H_2 = Q.

The remaining topological same-object theorem is geometric realization /
singular comparison for the actual sphere carrier.
-/

namespace Synthesis.Millennium.Hodge

open CategoryTheory
open scoped Simplicial

/-- The actual mathlib simplicial boundary whose realization is the tetrahedral 2-sphere. -/
abbrev TetrahedralSphereSSet := (SSet.boundary 3 : SSet)

instance tetrahedralSphere_dimensionLTThree :
    SSet.HasDimensionLT (SSet.boundary 3) 3 := inferInstance

structure TetraC2 where
  f012 : ℚ
  f013 : ℚ
  f023 : ℚ
  f123 : ℚ
deriving DecidableEq

structure TetraC1 where
  e01 : ℚ
  e02 : ℚ
  e03 : ℚ
  e12 : ℚ
  e13 : ℚ
  e23 : ℚ
deriving DecidableEq

def tetraD2 (c : TetraC2) : TetraC1 where
  e01 := c.f012 + c.f013
  e02 := -c.f012 + c.f023
  e03 := -c.f013 - c.f023
  e12 := c.f012 + c.f123
  e13 := c.f013 - c.f123
  e23 := c.f023 + c.f123

def tetraFundamentalCycle : TetraC2 where
  f012 := -1
  f013 := 1
  f023 := -1
  f123 := 1

theorem tetraFundamentalCycle_boundary_zero :
    tetraD2 tetraFundamentalCycle =
      { e01 := 0, e02 := 0, e03 := 0, e12 := 0, e13 := 0, e23 := 0 } := by
  ext <;> norm_num [tetraD2, tetraFundamentalCycle]

def TetraTwoCycle (c : TetraC2) : Prop :=
  tetraD2 c =
    { e01 := 0, e02 := 0, e03 := 0, e12 := 0, e13 := 0, e23 := 0 }

theorem tetraTwoCycle_coordinates
    {c : TetraC2} (hc : TetraTwoCycle c) :
    c.f012 = -c.f123 ∧
    c.f013 = c.f123 ∧
    c.f023 = -c.f123 := by
  have h01 := congrArg TetraC1.e01 hc
  have h02 := congrArg TetraC1.e02 hc
  have h12 := congrArg TetraC1.e12 hc
  have h13 := congrArg TetraC1.e13 hc
  have h23 := congrArg TetraC1.e23 hc
  simp [TetraTwoCycle, tetraD2] at h01 h02 h12 h13 h23
  constructor
  · linarith
  constructor <;> linarith

def scaleTetraC2 (q : ℚ) (c : TetraC2) : TetraC2 where
  f012 := q * c.f012
  f013 := q * c.f013
  f023 := q * c.f023
  f123 := q * c.f123

theorem tetraTwoCycle_eq_fundamental_multiple
    {c : TetraC2} (hc : TetraTwoCycle c) :
    c = scaleTetraC2 c.f123 tetraFundamentalCycle := by
  rcases tetraTwoCycle_coordinates hc with ⟨h012, h013, h023⟩
  ext <;> simp [scaleTetraC2, tetraFundamentalCycle, h012, h013, h023] <;> ring

theorem fundamental_multiple_is_cycle (q : ℚ) :
    TetraTwoCycle (scaleTetraC2 q tetraFundamentalCycle) := by
  unfold TetraTwoCycle tetraD2 scaleTetraC2 tetraFundamentalCycle
  ext <;> simp <;> ring

/-- Top-degree boundaries vanish because ∂Δ[3] has dimension < 3. -/
def TetraC3 := PUnit

def tetraD3 (_ : TetraC3) : TetraC2 where
  f012 := 0
  f013 := 0
  f023 := 0
  f123 := 0

theorem tetraD3_zero (c : TetraC3) :
    tetraD3 c = { f012 := 0, f013 := 0, f023 := 0, f123 := 0 } := rfl

structure TetraH2Class where
  chain : TetraC2
  cycle : TetraTwoCycle chain

def tetraH2ToQ (h : TetraH2Class) : ℚ :=
  h.chain.f123

def qToTetraH2 (q : ℚ) : TetraH2Class where
  chain := scaleTetraC2 q tetraFundamentalCycle
  cycle := fundamental_multiple_is_cycle q

theorem qToTetraH2_toQ (q : ℚ) :
    tetraH2ToQ (qToTetraH2 q) = q := by
  simp [tetraH2ToQ, qToTetraH2, scaleTetraC2, tetraFundamentalCycle]

theorem tetraH2_toQ_roundTrip (h : TetraH2Class) :
    qToTetraH2 (tetraH2ToQ h) = h := by
  cases h with
  | mk chain cycle =>
      simp only [tetraH2ToQ, qToTetraH2]
      have hc := tetraTwoCycle_eq_fundamental_multiple cycle
      subst chain
      rfl

noncomputable def tetrahedralSphereH2EquivQ :
    TetraH2Class ≃ ℚ where
  toFun := tetraH2ToQ
  invFun := qToTetraH2
  left_inv := tetraH2_toQ_roundTrip
  right_inv := qToTetraH2_toQ

theorem tetrahedralSphere_fundamental_generator :
    tetraH2ToQ (qToTetraH2 1) = 1 := by simp [qToTetraH2_toQ]

/--
The precise remaining bridge: identify the explicit normalized chains above with
the normalized chain complex of mathlib's actual `∂Δ[3]`, and then with singular
chains of its geometric realization / `UnitSphere2`.
-/
structure TetrahedralToSingularSphereComparison where
  toSingular : TetraH2Class → sphere2SingularH2
  fromSingular : sphere2SingularH2 → TetraH2Class
  leftInverse : Function.LeftInverse fromSingular toSingular
  rightInverse : Function.RightInverse fromSingular toSingular

/--
The exact remaining same-object bridge, stated without smuggling in linearity:
an equivalence from the explicit top homology of the tetrahedral simplicial
sphere to the actual singular H₂ of the topological 2-sphere.
-/
noncomputable def tetrahedralH2EquivSphereSingularH2
    (comparison : TetrahedralToSingularSphereComparison) :
    TetraH2Class ≃ sphere2SingularH2 where
  toFun := comparison.toSingular
  invFun := comparison.fromSingular
  left_inv := comparison.leftInverse
  right_inv := comparison.rightInverse

theorem sphereSingularH2_equiv_Q_of_tetrahedralComparison
    (comparison : TetrahedralToSingularSphereComparison) :
    Nonempty (sphere2SingularH2 ≃ ℚ) := by
  exact ⟨(tetrahedralH2EquivSphereSingularH2 comparison).symm.trans
    tetrahedralSphereH2EquivQ⟩

end Synthesis.Millennium.Hodge
