import Mathlib
import Integration.DASHITOE.HornSelectedWSpectralCubicCut

/-!
# Finite Hopf-link metrically short meridians are NOT Hatcher's F₂ source

Mathematical original sources:
- Hatcher, Algebraic Topology Example 2B.2, pp171-172: local
  punctured-torus free group F₂, with incoming annulus generator
  mapped to nontrivial [α₁,α₂].
- Classical Hopf link exterior S³ minus H ≅ T²×(-1,1),
  fundamental group ℤ×ℤ (e.g. Friedl, Knot Theory 2024,
  Lemma 3.13). This is a DIFFERENT based π₁ source.
- Agda horn owner PR #1244 owns the explicit linked two-circle
  prototype C1=(2cos t,2sin t,0), C2=(1,1+cos t,sin t),
  C3 placement, linking ±1. The new exact meridian metric
  and isotopy audit is in Agda hyperfabric PR #1249.
- Agda neutrino PR #1247 owns original selected W. Previous
  Agda #1249 / Lean #84 owns ||W-I||²>517/250.

Classical ALGEBRAIC consequence:
  If a link complement group is abelian (Hopf: ℤ²), then every
  homomorphism into an arbitrary group sends its meridian
  commutator to 1. Therefore such a finite Hopf clasp can NEVER
  inhabit the Hatcher relative source parent-commutator W
  with the selected positive norm gap.

This Lean code formalises only the ABELIAN GROUP DISCRIMINATOR,
and a conditional source-spectral contradiction. It does NOT
prove the 3D Hopf diffeomorphism, the Hatcher wild source
relative π₁ equivalence, Euclidean length or a kernel receipt.
-/

namespace DASHIHornHopfClaspNoGo

variable {G : Type*} [Group G]

def comm (a b : G) : G := a * b * a⁻¹ * b⁻¹

theorem commutingMeridiansCommOne (a b : G)
    (hab : a*b=b*a) : comm a b = 1 := by
  unfold comm
  rw [hab]
  group

theorem anyAbelianSourceCommVanishes
    {H : Type*} [CommGroup H]
    (rho : H →* G) (a b : H) :
    comm (rho a) (rho b) = 1 := by
  apply commutingMeridiansCommOne
  calc
    rho a * rho b = rho (a*b) := (rho.map_mul a b).symm
    _ = rho (b*a) := by rw [mul_comm]
    _ = rho b * rho a := rho.map_mul b a

/-- One authentic Hopf-complement monodromy cannot generate
a chosen nontrivial SU3 W by Hatcher's parent-commutator
rule: the SOURCE π₁ has commuting meridians. -/
theorem noNontrivialHatcherRootFromHopf
    {H : Type*} [CommGroup H]
    (rho : H →* G) (a b : H)
    (selectedW : G)
    (hW : selectedW = comm (rho a) (rho b))
    (hWnontrivial : selectedW ≠ 1) : False := by
  have hzero := anyAbelianSourceCommVanishes rho a b
  exact hWnontrivial (hW.trans hzero)

/-- The existing exact selected-W norm certificate is a source
premise. A nontrivial squared norm excludes the Hopf replacement,
even though it has genuine nonzero *pairwise linking* and small
Euclidean meridian circles. -/
theorem selectedSpectrumRejectsHopf
    {H : Type*} [CommGroup H]
    (rho : H →* G) (a b : H)
    (selectedW : G)
    (gap : G → ℚ) (hOneGap : gap 1 = 0)
    (hOriginalRootSq :
      DASHIHornSelectedWSpectralCubic.selectedRootSqThreshold
        < (gap selectedW)^2)
    (hWrongSource :
      selectedW = comm (rho a) (rho b)) : False := by
  have hwid : selectedW = 1 :=
    hWrongSource.trans (anyAbelianSourceCommVanishes rho a b)
  rw [hwid, hOneGap] at hOriginalRootSq
  norm_num [DASHIHornSelectedWSpectralCubic.selectedRootSqThreshold]
    at hOriginalRootSq

/-- Any abelian receiver kills commutators of the REAL source too;
this is exactly why linking number and abelianised finite group
certificates cannot substitute for the Hatcher F₂ meridian map. -/
theorem anyAbelianDetectorKillsCommutator
    {A : Type*} [CommGroup A]
    (chi : G →* A) (a b : G) :
    chi (comm a b) = 1 := by
  have mapped : chi (comm a b) =
      (chi a)*(chi b)*(chi a)⁻¹*(chi b)⁻¹ := by
    simp [comm, map_mul]
  rw [mapped]
  rw [mul_comm (chi a) (chi b)]
  group

end DASHIHornHopfClaspNoGo
