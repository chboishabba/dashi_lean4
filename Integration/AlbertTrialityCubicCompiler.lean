import Mathlib

/-!
# Triality compiler for the Albert cubic

At the coordinate level the Albert/Freudenthal determinant has the shape

  a*b*c - a*q(x) - b*q(y) - c*q(z) + 2*t(x,y,z),

where the three eight-dimensional sectors carry quadratic norms and a triality
trilinear form.  This file isolates the elementary algebra: any triple of
linear maps preserving the three quadratic terms and the triality form
preserves the cubic automatically.

This is deliberately independent of octonions.  The remaining same-object task
is to instantiate `TrialityCubicData` with the donor's actual octonion norm and
real triple product, then provide the concrete D4/triality maps.
-/

namespace Integration.AlbertTrialityCubicCompiler

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Coordinate carrier `3 + 8 + 8 + 8` with three copies of the same underlying
8-dimensional module. -/
structure TrialityCoordinates (V : Type*) where
  d0 : ℝ
  d1 : ℝ
  d2 : ℝ
  x0 : V
  x1 : V
  x2 : V

/-- Quadratic/trilinear data entering the Albert cubic. -/
structure TrialityCubicData (V : Type*) where
  q0 : V → ℝ
  q1 : V → ℝ
  q2 : V → ℝ
  tri : V → V → V → ℝ

/-- Freudenthal-shaped cubic in triality coordinates. -/
def cubic (D : TrialityCubicData V) (x : TrialityCoordinates V) : ℝ :=
  x.d0 * x.d1 * x.d2
    - x.d0 * D.q0 x.x0
    - x.d1 * D.q1 x.x1
    - x.d2 * D.q2 x.x2
    + 2 * D.tri x.x0 x.x1 x.x2

/-- A D4/triality symmetry acts independently on the three 8-dimensional
sectors while fixing the three diagonal scalar coordinates. -/
structure TrialitySymmetry (D : TrialityCubicData V) where
  g0 : V ≃ₗ[ℝ] V
  g1 : V ≃ₗ[ℝ] V
  g2 : V ≃ₗ[ℝ] V
  q0_preserved : ∀ x, D.q0 (g0 x) = D.q0 x
  q1_preserved : ∀ x, D.q1 (g1 x) = D.q1 x
  q2_preserved : ∀ x, D.q2 (g2 x) = D.q2 x
  triality_preserved : ∀ x y z,
    D.tri (g0 x) (g1 y) (g2 z) = D.tri x y z

/-- Action of a triality symmetry on coordinates. -/
def TrialitySymmetry.act (D : TrialityCubicData V)
    (g : TrialitySymmetry D) (x : TrialityCoordinates V) : TrialityCoordinates V where
  d0 := x.d0
  d1 := x.d1
  d2 := x.d2
  x0 := g.g0 x.x0
  x1 := g.g1 x.x1
  x2 := g.g2 x.x2

/-- Norm + triality preservation compiles directly to cubic preservation. -/
theorem TrialitySymmetry.cubic_preserved
    (D : TrialityCubicData V) (g : TrialitySymmetry D) :
    ∀ x, cubic D (g.act D x) = cubic D x := by
  intro x
  simp [cubic, TrialitySymmetry.act, g.q0_preserved, g.q1_preserved,
    g.q2_preserved, g.triality_preserved]

/-- Exact remaining octonionic realization seam. -/
structure OctonionicTrialityRealization (D : TrialityCubicData V) : Prop where
  octonionNormMatchesQ0 : Prop
  octonionNormMatchesQ1 : Prop
  octonionNormMatchesQ2 : Prop
  realTripleProductMatchesTriality : Prop
  d4GeneratorsSupplyTrialitySymmetries : Prop

structure Boundary where
  freudenthalCoordinateCubicTyped : Bool
  d4TrialitySymmetryTyped : Bool
  trialityImpliesCubicPreservationPaid : Bool
  actualOctonionNormRealizationPaidHere : Bool
  actualOctonionTrialityMapsPaidHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  freudenthalCoordinateCubicTyped := true
  d4TrialitySymmetryTyped := true
  trialityImpliesCubicPreservationPaid := true
  actualOctonionNormRealizationPaidHere := false
  actualOctonionTrialityMapsPaidHere := false

end Integration.AlbertTrialityCubicCompiler
