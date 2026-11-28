import BSDCohomology.EllipticKummerCocycleAlgebraExact
import Synthesis.MillenniumBSDCMOriginalGeometricKummerGroupExact
import Synthesis.MillenniumBSDCMGeometricKummerContinuousH1Exact
import Mathlib.FieldTheory.KrullTopology
import Mathlib.Topology.Order
import Mathlib.Tactic

/-! Degree-one Kummer exactness on the original geometric point action.
Use the existing point carrier and Kummer differences, not a replacement
H1 object. The two exactness assertions below hold at representatives.
The comparison with the general Mathlib homogeneous-cochain quotient,
completion maps, and the analytic rank theorem remain separate. -/

namespace BSDCohomology

open WeierstrassCurve
open scoped Topology
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- The actual crossed-cocycle equation for the existing point action. -/
def IsPointCrossed (c : Field.absoluteGaloisGroup K → GeometricPoint W) : Prop :=
  ∀ σ τ, c (σ * τ) = c σ + galoisPointMap W σ (c τ)

theorem kummerDifference_crossed (Q : GeometricPoint W) :
    IsPointCrossed W (kummerDifference W Q) := by
  intro σ τ
  unfold kummerDifference
  rw [galoisPointMap_mul, map_sub]
  abel

theorem kummerDifference_double (Q : GeometricPoint W)
    (σ : Field.absoluteGaloisGroup K) :
    (2 : ℕ) • kummerDifference W Q σ =
      kummerDifference W ((2 : ℕ) • Q) σ := by
  unfold kummerDifference
  rw [nsmul_sub, galoisPointMap_double]

/-- For nontrivial E[2] action, the two choices need not agree pointwise:
their difference is precisely the actual two-torsion coboundary. -/
theorem half_change_is_coboundary
    {P : GeometricPoint W} (hP : IsGaloisFixedPoint W P)
    (Q₁ Q₂ : GeometricHalfData W P) (σ : Field.absoluteGaloisGroup K) :
    (kummerCocycleValue W hP Q₂ σ).1 -
      (kummerCocycleValue W hP Q₁ σ).1 =
        kummerDifference W (halfDifferenceTwoTorsion W Q₁ Q₂).1 σ := by
  simp only [kummerCocycleValue_coe]
  change (galoisPointMap W σ Q₂.half - Q₂.half) -
    (galoisPointMap W σ Q₁.half - Q₁.half) =
      galoisPointMap W σ (Q₂.half-Q₁.half) - (Q₂.half-Q₁.half)
  rw [map_sub]
  abel

/-- If a literal E[2]-valued cocycle is an Ebar-coboundary,
the double of its coboundary witness is genuinely Galois-fixed. -/
theorem fixed_double_of_torsion_coboundary
    (c : Field.absoluteGaloisGroup K → EllipticTwoTorsion W)
    (Q : GeometricPoint W)
    (h : ∀ σ, (c σ).1 = kummerDifference W Q σ) :
    IsGaloisFixedPoint W ((2 : ℕ) • Q) := by
  intro σ
  have ht := (mem_ellipticTwoTorsion_iff W (c σ).1).mp (c σ).2
  rw [h σ, kummerDifference_double] at ht
  exact sub_eq_zero.mp ht

/-- Literal kernel of H1 inclusion at cocycle representatives:
E[2]-valued coboundaries in Ebar are exactly geometric Kummer values. -/
theorem torsion_coboundary_iff_kummer
    (c : Field.absoluteGaloisGroup K → EllipticTwoTorsion W) :
    (∃ Q : GeometricPoint W, ∀ σ, (c σ).1 = kummerDifference W Q σ) ↔
      ∃ P : GeometricPoint W, ∃ hP : IsGaloisFixedPoint W P,
        ∃ Q : GeometricHalfData W P, ∀ σ, c σ = kummerCocycleValue W hP Q σ := by
  constructor
  · rintro ⟨Q,hQ⟩
    let P := (2 : ℕ) • Q
    have hP : IsGaloisFixedPoint W P :=
      fixed_double_of_torsion_coboundary W c Q hQ
    refine ⟨P,hP,⟨Q,rfl⟩,fun σ => ?_⟩
    apply Subtype.ext
    exact hQ σ
  · rintro ⟨P,hP,Q,hQ⟩
    exact ⟨Q.half,fun σ => congrArg Subtype.val (hQ σ)⟩

/-- Remove the actual half-coboundary from a cocycle whose double is
a coboundary. This is the reverse solve for the H1[2] lift. -/
def removeHalfCoboundary
    (c : Field.absoluteGaloisGroup K → GeometricPoint W)
    (Q : GeometricPoint W) (σ : Field.absoluteGaloisGroup K) :
    GeometricPoint W :=
  c σ - kummerDifference W Q σ

theorem removeHalf_crossed
    (c : Field.absoluteGaloisGroup K → GeometricPoint W)
    (hc : IsPointCrossed W c) (Q : GeometricPoint W) :
    IsPointCrossed W (removeHalfCoboundary W c Q) := by
  intro σ τ
  unfold removeHalfCoboundary
  rw [hc σ τ, kummerDifference_crossed W Q σ τ, map_sub]
  abel

theorem removeHalf_is_torsion
    (c : Field.absoluteGaloisGroup K → GeometricPoint W)
    (P Q : GeometricPoint W) (hQ : (2 : ℕ) • Q = P)
    (h : ∀ σ, (2 : ℕ) • c σ = kummerDifference W P σ)
    (σ : Field.absoluteGaloisGroup K) :
    removeHalfCoboundary W c Q σ ∈ EllipticTwoTorsion W := by
  rw [mem_ellipticTwoTorsion_iff]
  unfold removeHalfCoboundary
  rw [nsmul_sub, h σ, kummerDifference_double, hQ, sub_self]

/-- The lifted function lives in the existing literal E[2] subgroup. -/
def liftDoubleCoboundary
    (c : Field.absoluteGaloisGroup K → GeometricPoint W)
    (P Q : GeometricPoint W) (hQ : (2 : ℕ) • Q = P)
    (h : ∀ σ, (2 : ℕ) • c σ = kummerDifference W P σ)
    (σ : Field.absoluteGaloisGroup K) : EllipticTwoTorsion W :=
  ⟨removeHalfCoboundary W c Q σ,removeHalf_is_torsion W c P Q hQ h σ⟩

theorem liftDouble_crossed
    (c : Field.absoluteGaloisGroup K → GeometricPoint W)
    (hc : IsPointCrossed W c)
    (P Q : GeometricPoint W) (hQ : (2 : ℕ) • Q = P)
    (h : ∀ σ, (2 : ℕ) • c σ = kummerDifference W P σ)
    (σ τ : Field.absoluteGaloisGroup K) :
    liftDoubleCoboundary W c P Q hQ h (σ*τ) =
      liftDoubleCoboundary W c P Q hQ h σ +
      galoisTwoTorsionMap W σ (liftDoubleCoboundary W c P Q hQ h τ) := by
  apply Subtype.ext
  exact removeHalf_crossed W c hc Q σ τ

/-- Exactness at the point-cohomology two-kernel, on representatives,
using the actual geometric surjectivity hypothesis. -/
theorem double_coboundary_iff_torsion_lift
    (hs : Function.Surjective (fun Q : GeometricPoint W => (2 : ℕ) • Q))
    (c : Field.absoluteGaloisGroup K → GeometricPoint W)
    (hc : IsPointCrossed W c) :
    (∃ P : GeometricPoint W, ∀ σ, (2 : ℕ) • c σ = kummerDifference W P σ) ↔
      ∃ d : Field.absoluteGaloisGroup K → EllipticTwoTorsion W,
        (∀ σ τ, d (σ*τ) = d σ + galoisTwoTorsionMap W σ (d τ)) ∧
        ∃ Q : GeometricPoint W, ∀ σ, c σ = (d σ).1 + kummerDifference W Q σ := by
  constructor
  · rintro ⟨P,h⟩
    obtain ⟨Q,hQ⟩ := hs P
    refine ⟨liftDoubleCoboundary W c P Q hQ h,
      liftDouble_crossed W c hc P Q hQ h,Q,fun σ => ?_⟩
    change c σ = c σ - kummerDifference W Q σ + kummerDifference W Q σ
    abel
  · rintro ⟨d,hd,Q,hQ⟩
    refine ⟨(2 : ℕ) • Q,fun σ => ?_⟩
    rw [hQ σ,nsmul_add,(mem_ellipticTwoTorsion_iff W (d σ).1).mp (d σ).2,
      zero_add,kummerDifference_double]


section ContinuousRepresentatives
local instance : TopologicalSpace (GeometricPoint W) := ⊥
local instance : DiscreteTopology (GeometricPoint W) := discreteTopology_bot _
local instance : TopologicalSpace (EllipticTwoTorsion W) := ⊥
local instance : DiscreteTopology (EllipticTwoTorsion W) := discreteTopology_bot _

/-- Krull continuity for the actual point orbit, without assuming trivial
Galois action on the two-torsion. The two affine coordinate stabilizers
suffice, as in the existing selected CM character implementation. -/
theorem originalPointOrbit_continuous (Q : GeometricPoint W) :
    Continuous (fun σ : Field.absoluteGaloisGroup K => galoisPointMap W σ Q) := by
  rw [continuous_iff_continuousAt]
  intro σ
  rw [ContinuousAt, nhds_discrete, tendsto_pure]
  cases hQ : Q with
  | zero =>
    exact Filter.Eventually.of_forall (fun τ => by simp [hQ])
  | some x y hxy =>
    let Hx := MulAction.stabilizer (Field.absoluteGaloisGroup K) x
    let Hy := MulAction.stabilizer (Field.absoluteGaloisGroup K) y
    have hxOpen : IsOpen (Hx : Set (Field.absoluteGaloisGroup K)) :=
      stabilizer_isOpen_of_isIntegral x
    have hyOpen : IsOpen (Hy : Set (Field.absoluteGaloisGroup K)) :=
      stabilizer_isOpen_of_isIntegral y
    let f : Field.absoluteGaloisGroup K → Field.absoluteGaloisGroup K :=
      fun τ => σ⁻¹ * τ
    have hf : Continuous f := continuous_const.mul continuous_id
    have hopen : IsOpen (f ⁻¹' ((Hx : Set _) ∩ (Hy : Set _))) :=
      (hxOpen.inter hyOpen).preimage hf
    have hmem : σ ∈ f ⁻¹' ((Hx : Set _) ∩ (Hy : Set _)) := by
      simp [f, Hx, Hy]
    filter_upwards [hopen.mem_nhds hmem] with τ hτ
    have hx : (σ⁻¹ * τ) x = x := hτ.1
    have hy : (σ⁻¹ * τ) y = y := hτ.2
    have hfix : galoisPointMap W (σ⁻¹ * τ) Q = Q := by
      rw [hQ]
      simp [galoisPointMap, hx, hy]
    calc
      galoisPointMap W τ Q =
          galoisPointMap W σ (galoisPointMap W (σ⁻¹ * τ) Q) := by
            rw [← galoisPointMap_mul]
            congr 1
            group
      _ = galoisPointMap W σ Q := by rw [hfix]

theorem originalKummerDifference_continuous (Q : GeometricPoint W) :
    Continuous (kummerDifference W Q) :=
  (originalPointOrbit_continuous W Q).sub continuous_const

/-- A continuous point cocycle gives a continuous literal torsion lift;
no topological quotient is replaced by a discrete finite proxy. -/
theorem liftDoubleCoboundary_continuous
    (c : Field.absoluteGaloisGroup K → GeometricPoint W)
    (hc : Continuous c)
    (P Q : GeometricPoint W) (hQ : (2 : ℕ) • Q = P)
    (h : ∀ σ, (2 : ℕ) • c σ = kummerDifference W P σ) :
    Continuous (liftDoubleCoboundary W c P Q hQ h) := by
  have hsub : Continuous (removeHalfCoboundary W c Q) :=
    hc.sub (originalKummerDifference_continuous W Q)
  -- Both topologies are discrete; every fibre is open by the
  -- continuous map to the original geometric point group.
  rw [continuous_def]
  intro s hs
  let t : Set (GeometricPoint W) := {v | ∃ h : v ∈ EllipticTwoTorsion W,
    (⟨v,h⟩ : EllipticTwoTorsion W) ∈ s}
  have ht : IsOpen t := isOpen_discrete t
  have he : liftDoubleCoboundary W c P Q hQ h ⁻¹' s =
      removeHalfCoboundary W c Q ⁻¹' t := by
    ext σ
    constructor
    · intro hσ
      exact ⟨(liftDoubleCoboundary W c P Q hQ h σ).2,hσ⟩
    · rintro ⟨hm,hs'⟩
      exact hs'
  rw [he]
  exact ht.preimage hsub

end ContinuousRepresentatives

end
end BSDCohomology

namespace Synthesis.Millennium.BSD
open BSDCohomology
noncomputable section

/-- Instantiate the reverse lift on the existing actual selected curve.
No divisibility premise remains on this curve. -/
theorem cmOriginalDoubleCoboundary_iff_torsion_lift
    (c : Field.absoluteGaloisGroup ℚ → GeometricPoint cmWeierstrass)
    (hc : IsPointCrossed cmWeierstrass c) :
    (∃ P : GeometricPoint cmWeierstrass,
      ∀ σ, (2 : ℕ) • c σ = kummerDifference cmWeierstrass P σ) ↔
      ∃ d : Field.absoluteGaloisGroup ℚ → EllipticTwoTorsion cmWeierstrass,
        (∀ σ τ, d (σ*τ) = d σ + galoisTwoTorsionMap cmWeierstrass σ (d τ)) ∧
        ∃ Q : GeometricPoint cmWeierstrass,
          ∀ σ, c σ = (d σ).1 + kummerDifference cmWeierstrass Q σ :=
  double_coboundary_iff_torsion_lift cmWeierstrass
    cmSelectedGeometricDoubling_onto c hc

end
end Synthesis.Millennium.BSD
