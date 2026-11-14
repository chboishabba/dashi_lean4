import Mathlib

/-!
# Exact sqrt(3) x sqrt(3) R30 reciprocal folding geometry

Mechanism-neutral exact lattice algebra for the conventional oriented
hexagonal basis.

Real-space supercell columns:
  A₁ = (1, 1)
  A₂ = (-1, 2)

with determinant 3.

Reciprocal numerator columns:
  N₁ = (2, 1)
  N₂ = (-1, 1)

satisfy Mᵀ N = 3 I, so the reciprocal transform is (1/3)N.
-/

namespace Integration.CondensedMatterSqrt3R30

abbrev Z2 := ℤ × ℤ

def primitiveA1 : Z2 := (1, 0)
def primitiveA2 : Z2 := (0, 1)
def superA1 : Z2 := (1, 1)
def superA2 : Z2 := (-1, 2)
def reciprocalNumeratorB1 : Z2 := (2, 1)
def reciprocalNumeratorB2 : Z2 := (-1, 1)

def det2 (u v : Z2) : ℤ :=
  u.1 * v.2 - u.2 * v.1

theorem supercell_determinant_three :
    det2 superA1 superA2 = 3 := by
  norm_num [det2, superA1, superA2]

theorem primitive_to_super_positive_orientation :
    det2 primitiveA1 superA1 = 1 := by
  norm_num [det2, primitiveA1, superA1]

/-- Integral Gram form for an equal-length 60-degree hexagonal basis. -/
def hexDot (u v : Z2) : ℤ :=
  2 * u.1 * v.1 + u.1 * v.2 + u.2 * v.1 + 2 * u.2 * v.2

def hexNormSq (u : Z2) : ℤ := hexDot u u

theorem primitiveA1_norm_sq_two :
    hexNormSq primitiveA1 = 2 := by
  norm_num [hexNormSq, hexDot, primitiveA1]

theorem primitiveA2_norm_sq_two :
    hexNormSq primitiveA2 = 2 := by
  norm_num [hexNormSq, hexDot, primitiveA2]

theorem primitive_dot_one :
    hexDot primitiveA1 primitiveA2 = 1 := by
  norm_num [hexDot, primitiveA1, primitiveA2]

theorem superA1_norm_sq_six :
    hexNormSq superA1 = 6 := by
  norm_num [hexNormSq, hexDot, superA1]

theorem superA2_norm_sq_six :
    hexNormSq superA2 = 6 := by
  norm_num [hexNormSq, hexDot, superA2]

theorem super_mutual_dot_three :
    hexDot superA1 superA2 = 3 := by
  norm_num [hexDot, superA1, superA2]

theorem sqrt3_scale_certificate :
    hexNormSq superA1 = 3 * hexNormSq primitiveA1 := by
  norm_num [hexNormSq, hexDot, superA1, primitiveA1]

theorem super_sixty_degree_metric_certificate :
    2 * hexDot superA1 superA2 = hexNormSq superA1 := by
  norm_num [hexNormSq, hexDot, superA1, superA2]

theorem primitive_to_super_dot_three :
    hexDot primitiveA1 superA1 = 3 := by
  norm_num [hexDot, primitiveA1, superA1]

theorem r30_metric_square_certificate :
    4 * (hexDot primitiveA1 superA1)^2 =
      3 * hexNormSq primitiveA1 * hexNormSq superA1 := by
  norm_num [hexNormSq, hexDot, primitiveA1, superA1]

def coordDot (u v : Z2) : ℤ := u.1 * v.1 + u.2 * v.2

theorem mtN11 : coordDot superA1 reciprocalNumeratorB1 = 3 := by
  norm_num [coordDot, superA1, reciprocalNumeratorB1]

theorem mtN12 : coordDot superA1 reciprocalNumeratorB2 = 0 := by
  norm_num [coordDot, superA1, reciprocalNumeratorB2]

theorem mtN21 : coordDot superA2 reciprocalNumeratorB1 = 0 := by
  norm_num [coordDot, superA2, reciprocalNumeratorB1]

theorem mtN22 : coordDot superA2 reciprocalNumeratorB2 = 3 := by
  norm_num [coordDot, superA2, reciprocalNumeratorB2]

abbrev Torus3x3 := ZMod 3 × ZMod 3

def foldClass (p : Torus3x3) : ZMod 3 := p.1 - p.2

def translateSuperA1 (p : Torus3x3) : Torus3x3 :=
  (p.1 + 1, p.2 + 1)

def translateSuperA2 (p : Torus3x3) : Torus3x3 :=
  (p.1 - 1, p.2 - 1)

theorem foldClass_invariant_A1 (p : Torus3x3) :
    foldClass (translateSuperA1 p) = foldClass p := by
  simp [foldClass, translateSuperA1]

theorem foldClass_invariant_A2 (p : Torus3x3) :
    foldClass (translateSuperA2 p) = foldClass p := by
  simp [foldClass, translateSuperA2]

def rep0 : Torus3x3 := (0, 0)
def rep1 : Torus3x3 := (1, 0)
def rep2 : Torus3x3 := (2, 0)

theorem representative_classes :
    foldClass rep0 = 0 ∧ foldClass rep1 = 1 ∧ foldClass rep2 = 2 := by
  norm_num [foldClass, rep0, rep1, rep2]

structure Boundary where
  determinantThreeProved : Bool
  sqrt3MetricScaleProved : Bool
  r30MetricCertificateProved : Bool
  reciprocalTransformProved : Bool
  threeClassFoldingInvariantProved : Bool
  finiteTorusClaimedAsEntireInfiniteCrystal : Bool
  arpesIntensityDerivedFromGeometry : Bool
  microscopicHamiltonianDerivedFromGeometry : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  determinantThreeProved := true
  sqrt3MetricScaleProved := true
  r30MetricCertificateProved := true
  reciprocalTransformProved := true
  threeClassFoldingInvariantProved := true
  finiteTorusClaimedAsEntireInfiniteCrystal := false
  arpesIntensityDerivedFromGeometry := false
  microscopicHamiltonianDerivedFromGeometry := false

end Integration.CondensedMatterSqrt3R30
