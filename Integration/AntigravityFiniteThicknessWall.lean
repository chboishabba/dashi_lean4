import Integration.AntigravitySourceGeometryWeld

namespace Integration.AntigravityFiniteThicknessWall

open Integration.GRQFTPostMergeLocalization
open Integration.AntigravitySourceGeometryWeld

/-!
Finite-thickness effective wall source.

This is deliberately weaker than a scalar-field domain-wall solution.  It
removes the distributional "zero thickness" source at the stress-profile level
by smearing the exact Nambu-Goto surface source uniformly across a positive
proper thickness.

For surface energy sigma and thickness delta,

  rho_wall = sigma / delta
  p_t      = -sigma / delta

so integrating across the slab returns sigma and -sigma exactly.

The remaining hard problem is to solve the full finite-thickness Einstein/TOV
transition with this (or a source-native scalar) profile.  No such solution is
claimed here.
-/

def slabEnergyDensity (surfaceEnergy thickness : Rat) : Rat :=
  surfaceEnergy / thickness

def slabTangentialPressure (surfaceEnergy thickness : Rat) : Rat :=
  - slabEnergyDensity surfaceEnergy thickness

def slabIntegratedEnergy (surfaceEnergy thickness : Rat) : Rat :=
  thickness * slabEnergyDensity surfaceEnergy thickness

def slabIntegratedTangentialPressure
    (surfaceEnergy thickness : Rat) : Rat :=
  thickness * slabTangentialPressure surfaceEnergy thickness

theorem slab_integrated_energy
    (surfaceEnergy thickness : Rat)
    (hThickness : thickness ≠ 0) :
    slabIntegratedEnergy surfaceEnergy thickness = surfaceEnergy := by
  field_simp [slabIntegratedEnergy, slabEnergyDensity, hThickness]

theorem slab_integrated_tangential_pressure
    (surfaceEnergy thickness : Rat)
    (hThickness : thickness ≠ 0) :
    slabIntegratedTangentialPressure surfaceEnergy thickness
      = -surfaceEnergy := by
  field_simp [slabIntegratedTangentialPressure, slabTangentialPressure,
    slabEnergyDensity, hThickness]

theorem slab_energy_density_positive
    {surfaceEnergy thickness : Rat}
    (hSurface : 0 < surfaceEnergy)
    (hThickness : 0 < thickness) :
    0 < slabEnergyDensity surfaceEnergy thickness := by
  unfold slabEnergyDensity
  positivity

theorem slab_tangential_pressure_negative
    {surfaceEnergy thickness : Rat}
    (hSurface : 0 < surfaceEnergy)
    (hThickness : 0 < thickness) :
    slabTangentialPressure surfaceEnergy thickness < 0 := by
  unfold slabTangentialPressure
  have h := slab_energy_density_positive hSurface hThickness
  linarith

structure FiniteThicknessEffectiveWallProfile where
  thickness : Rat
  thicknessPositive : 0 < thickness
  surfaceEnergy8Pi : Rat
  surfaceEnergyPositive : 0 < surfaceEnergy8Pi
  integratedEnergy :
    slabIntegratedEnergy surfaceEnergy8Pi thickness = surfaceEnergy8Pi
  integratedTangentialPressure :
    slabIntegratedTangentialPressure surfaceEnergy8Pi thickness
      = -surfaceEnergy8Pi
  localEnergyDensityPositive :
    0 < slabEnergyDensity surfaceEnergy8Pi thickness
  localTangentialPressureNegative :
    slabTangentialPressure surfaceEnergy8Pi thickness < 0

theorem effective_wall_profile
    (surfaceEnergy thickness : Rat)
    (hSurface : 0 < surfaceEnergy)
    (hThickness : 0 < thickness) :
    FiniteThicknessEffectiveWallProfile := by
  exact {
    thickness := thickness
    thicknessPositive := hThickness
    surfaceEnergy8Pi := surfaceEnergy
    surfaceEnergyPositive := hSurface
    integratedEnergy :=
      slab_integrated_energy surfaceEnergy thickness (ne_of_gt hThickness)
    integratedTangentialPressure :=
      slab_integrated_tangential_pressure
        surfaceEnergy thickness (ne_of_gt hThickness)
    localEnergyDensityPositive :=
      slab_energy_density_positive hSurface hThickness
    localTangentialPressureNegative :=
      slab_tangential_pressure_negative hSurface hThickness
  }

theorem nambu_bubble_finite_thickness_effective_wall
    (thickness : Rat)
    (hThickness : 0 < thickness) :
    FiniteThicknessEffectiveWallProfile := by
  exact effective_wall_profile
    nambuBubbleSurfaceTension8Pi thickness
    (by norm_num [nambuBubbleSurfaceTension8Pi])
    hThickness

def finiteThicknessEffectiveSourceCompiled : Bool := true
def finiteThicknessEinsteinSolutionDerived : Bool := false
def sourceNativeScalarWallDerived : Bool := false
def thinWallDistributionRequiredAtSourceLevel : Bool := false

end Integration.AntigravityFiniteThicknessWall
