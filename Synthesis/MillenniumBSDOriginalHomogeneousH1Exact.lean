import Synthesis.MillenniumBSDOriginalKummerCocycleExactness
import BSDCohomology.EllipticShaTarget
import Mathlib.RepresentationTheory.Homological.ContCohomology.LowDegree
import Mathlib.Topology.CompactOpen
import Mathlib.Tactic

/-!
Actual homogeneous cochains on the existing TopRep coefficient object.
Unlike the selected trivial-action character donor, this construction
keeps the Galois action. The degree-one class is the existing homology
projection, not an independently defined H1 carrier.
-/

namespace DASHI.BSD.OriginalH1
open CategoryTheory ContRepresentation ContinuousCohomology TopRep
open scoped Topology
noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [LocallyCompactSpace G]
variable (X : TopRep ℤ G)

def Crossed (c : C(G, X)) : Prop :=
  ∀ g h, c (g*h) = c g + X.ρ g (c h)

theorem crossed_one (c : C(G,X)) (hc : Crossed X c) : c 1 = 0 := by
  have h := hc 1 1
  simp at h
  exact add_left_cancel (show c 1 + c 1 = c 1 + 0 by simpa using h.symm)

def homogeneousRaw (c : C(G,X)) : C(G × G,X) where
  toFun p := c p.2 - c p.1
  continuous_toFun := (c.continuous.comp continuous_snd).sub
    (c.continuous.comp continuous_fst)

def homogeneousMap (c : C(G,X)) : C(G,C(G,X)) :=
  (homogeneousRaw X c).curry

@[simp] theorem homogeneousMap_apply (c : C(G,X)) (g h : G) :
    homogeneousMap X c g h = c h - c g := rfl

theorem homogeneousMap_invariant (c : C(G,X)) (hc : Crossed X c) :
    homogeneousMap X c ∈ ((TopRep.resolution' X).X 1).ρ.invariants := by
  intro g
  ext x y
  simp only [coind₁_apply_apply, homogeneousMap_apply, map_sub]
  have hx := hc g (g⁻¹*x)
  have hy := hc g (g⁻¹*y)
  rw [← mul_assoc, mul_inv_cancel, one_mul] at hx hy
  rw [show X.ρ g (c (g⁻¹*x)) = c x - c g by rw [hx]; abel,
      show X.ρ g (c (g⁻¹*y)) = c y - c g by rw [hy]; abel]
  abel

abbrev KernelOne :=
  ↧(((TopRep.homogeneousCochains X).d 1 2).hom.ker)

def toKernelOne (c : C(G,X)) (hc : Crossed X c) : KernelOne X := by
  let σ : (TopRep.homogeneousCochains X).X 1 :=
    ⟨homogeneousMap X c, homogeneousMap_invariant X c hc⟩
  refine ⟨σ, ?_⟩
  rw [LinearMap.mem_ker]
  apply Subtype.ext
  ext x y z
  rw [TopRep.homogeneousCochains.d_apply]
  simp only [Nat.reduceAdd, TopRep.d_succ, TopRep.d_zero,
    ConcreteCategory.hom_ofHom, hom_sub, ContIntertwiningMap.sub_apply,
    coind₁ι_toFun, coind₁Map_toFun, ContinuousMap.const_apply,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk, ZeroMemClass.coe_zero]
  change (c z-c y)-((c z-c x)-(c y-c x))=0
  abel

/-- Actual homogeneous cycles are recovered by evaluation at (1,g). -/
def normalize (σ : KernelOne X) : C(G,X) := σ.1.1 1

theorem kernelOne_relation (σ : KernelOne X) (x y z : G) :
    σ.1.1 y z = σ.1.1 x z - σ.1.1 x y := by
  have hσ := σ.2
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    Subtype.ext_iff, TopRep.homogeneousCochains.d_apply] at hσ
  replace hσ := DFunLike.ext_iff.1
    (DFunLike.ext_iff.1 (DFunLike.ext_iff.1 hσ x) y) z
  simp only [Nat.reduceAdd, TopRep.d_succ, TopRep.d_zero,
    ConcreteCategory.hom_ofHom, hom_sub, ContIntertwiningMap.sub_apply,
    coind₁ι_toFun, coind₁Map_toFun, ContinuousMap.const_apply,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk, ZeroMemClass.coe_zero] at hσ
  simpa only [sub_eq_zero] using hσ

theorem kernelOne_equivariant (σ : KernelOne X) (g x y : G) :
    σ.1.1 (g*x) (g*y) = X.ρ g (σ.1.1 x y) := by
  have h := σ.1.2 g
  replace h := DFunLike.ext_iff.1 (DFunLike.ext_iff.1 h (g*x)) (g*y)
  simp only [coind₁_apply_apply] at h
  simpa [mul_assoc] using h.symm

theorem normalize_crossed (σ : KernelOne X) : Crossed X (normalize X σ) := by
  intro g h
  have h1 := kernelOne_relation X σ 1 g (g*h)
  have h2 := kernelOne_equivariant X σ g 1 h
  rw [mul_one] at h2
  change σ.1.1 1 (g*h) = σ.1.1 1 g + X.ρ g (σ.1.1 1 h)
  rw [← h2, h1]
  abel

theorem normalize_toKernelOne (c : C(G,X)) (hc : Crossed X c) :
    normalize X (toKernelOne X c hc) = c := by
  ext g
  change c g-c 1=c g
  rw [crossed_one X c hc, sub_zero]

theorem toKernelOne_normalize (σ : KernelOne X) :
    toKernelOne X (normalize X σ) (normalize_crossed X σ) = σ := by
  apply Subtype.ext
  apply Subtype.ext
  ext x y
  change σ.1.1 1 y-σ.1.1 1 x=σ.1.1 x y
  exact (kernelOne_relation X σ 1 x y).symm

/-- Use the library's actual categorical cycles object. -/
abbrev actualCyclesIso : ContinuousCohomology.cocycles X 1 ≅ KernelOne X :=
  Limits.KernelFork.mapIsoOfIsLimit
    ((TopRep.homogeneousCochains X).cyclesIsKernel 1 2 (by simp))
    (TopModuleCat.isLimitKer _) (Iso.refl _)

def actualClass (c : C(G,X)) (hc : Crossed X c) :
    continuousCohomology 1 X :=
  (ContinuousCohomology.π X 1) ((actualCyclesIso X).inv (toKernelOne X c hc))

/-- The actual H1 is the cokernel of the incoming differential into cycles,
with the quotient topology. This is the literal Mathlib homology object,
not a second H1 definition. -/
def actualH1QuotientIso :
    continuousCohomology 1 X ≅
      TopModuleCat.coker ((TopRep.homogeneousCochains X).toCycles 0 1) :=
  ((TopRep.homogeneousCochains X).homologyIsCokernel
    (CochainComplex.prev_nat_succ 0)).coconePointUniqueUpToIso
      (TopModuleCat.isColimitCoker _)


/-- The actual quotient isomorphism intertwines the library's class map
with its literal quotient projection. -/
theorem actualH1QuotientIso_comm :
    (ContinuousCohomology.π X 1) ≫ (actualH1QuotientIso X).hom =
      TopModuleCat.cokerπ ((TopRep.homogeneousCochains X).toCycles 0 1) := by
  unfold actualH1QuotientIso
  exact Limits.IsColimit.comp_coconePointUniqueUpToIso_hom
    ((TopRep.homogeneousCochains X).homologyIsCokernel
      (CochainComplex.prev_nat_succ 0))
    (TopModuleCat.isColimitCoker _) Limits.WalkingParallelPair.one

/-- Every class has a representative in the actual categorical cycles,
not merely a point of an externally stipulated quotient. -/
theorem actualClassMap_surjective :
    Function.Surjective (ContinuousCohomology.π X 1) := by
  intro x
  obtain ⟨z,hz⟩ := TopModuleCat.cokerπ_surjective
    ((TopRep.homogeneousCochains X).toCycles 0 1) ((actualH1QuotientIso X).hom x)
  refine ⟨z, ?_⟩
  apply (actualH1QuotientIso X).toContinuousLinearEquiv.injective
  change (actualH1QuotientIso X).hom ((ContinuousCohomology.π X 1) z) =
    (actualH1QuotientIso X).hom x
  rw [← ConcreteCategory.comp_apply, actualH1QuotientIso_comm]
  exact hz

/-- At the literal cycles object the kernel is exactly the incoming
boundary map. This is the required quotient identification, not an
axiom asserting the long exact sequence. -/
theorem actualClassMap_zero_iff_boundary
    (z : ContinuousCohomology.cocycles X 1) :
    (ContinuousCohomology.π X 1) z = 0 ↔
      ∃ b : (TopRep.homogeneousCochains X).X 0,
        (TopRep.homogeneousCochains X).toCycles 0 1 b = z := by
  have hq : (actualH1QuotientIso X).hom ((ContinuousCohomology.π X 1) z) =
      TopModuleCat.cokerπ ((TopRep.homogeneousCochains X).toCycles 0 1) z := by
    rw [← ConcreteCategory.comp_apply, actualH1QuotientIso_comm]
  constructor
  · intro hz
    rw [hz, map_zero] at hq
    have hm : z ∈ ((TopRep.homogeneousCochains X).toCycles 0 1).hom.range := by
      have hzero := hq.symm
      change Submodule.mkQ _ z = 0 at hzero
      exact Submodule.Quotient.mk_eq_zero.mp hzero
    exact hm
  · rintro ⟨b,hb⟩
    rw [← hb, ← ConcreteCategory.comp_apply,
      HomologicalComplex.toCycles_comp_homologyπ]
    rfl

/-- Normalization of the actual incoming differential. For a homogeneous
zero-cochain b, invariance gives b(g)=ρ(g)b(1), so the normalized
boundary is the signed difference ρ(g)b(1)-b(1). -/
theorem zeroCochain_orbit (b : (TopRep.homogeneousCochains X).X 0) (g : G) :
    b.1 g = X.ρ g (b.1 1) := by
  have h := DFunLike.ext_iff.1 (b.2 g) g
  simpa only [coind₁_apply_apply, inv_mul_cancel] using h.symm

theorem incomingDifferential_normalized
    (b : (TopRep.homogeneousCochains X).X 0) (g : G) :
    (((TopRep.homogeneousCochains X).d 0 1).hom b).1 1 g =
      X.ρ g (b.1 1)-b.1 1 := by
  rw [TopRep.homogeneousCochains.d_apply]
  simp only [Nat.reduceAdd, TopRep.d_succ, TopRep.d_zero,
    ConcreteCategory.hom_ofHom, hom_sub, ContIntertwiningMap.sub_apply,
    coind₁ι_toFun, coind₁Map_toFun, ContinuousMap.const_apply,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  exact congrArg (fun v => v-b.1 1) (zeroCochain_orbit X b g)

end
end DASHI.BSD.OriginalH1


namespace BSDCohomology
open WeierstrassCurve DASHI.BSD.OriginalH1
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

local instance : TopologicalSpace (GeometricPoint W) := ⊥
local instance : DiscreteTopology (GeometricPoint W) := discreteTopology_bot _
local instance : TopologicalSpace (EllipticTwoTorsion W) := ⊥
local instance : DiscreteTopology (EllipticTwoTorsion W) := discreteTopology_bot _

/-- Exact original geometric point coefficient H1 consumer. -/
def originalPointH1Class
    (c : Field.absoluteGaloisGroup K → GeometricPoint W)
    (hc : Continuous c) (hcross : IsPointCrossed W c) :
    EllipticPointH1 W :=
  actualClass (geometricPointTopRep W) ⟨c,hc⟩ hcross

/-- Continuity of the actual torsion Kummer cocycle, even for a
nontrivial Galois action. Its inclusion is the continuous point difference. -/
theorem originalKummerCocycle_continuous
    {P : GeometricPoint W} (hP : IsGaloisFixedPoint W P)
    (Q : GeometricHalfData W P) :
    Continuous (kummerCocycleValue W hP Q) := by
  rw [continuous_def]
  intro s hs
  let t : Set (GeometricPoint W) := {v | ∃ h : v ∈ EllipticTwoTorsion W,
    (⟨v,h⟩ : EllipticTwoTorsion W) ∈ s}
  have ht : IsOpen t := isOpen_discrete t
  have he : kummerCocycleValue W hP Q ⁻¹' s =
      kummerDifference W Q.half ⁻¹' t := by
    ext σ
    constructor
    · intro hσ
      exact ⟨(kummerCocycleValue W hP Q σ).2,hσ⟩
    · rintro ⟨hm,hs'⟩
      exact hs'
  rw [he]
  exact ht.preimage (originalKummerDifference_continuous W Q.half)

/-- Direct Kummer class in the ORIGINAL generic E[2] continuous H1
object, not through the selected square-class equivalence. -/
def originalKummerH1Class
    {P : GeometricPoint W} (hP : IsGaloisFixedPoint W P)
    (Q : GeometricHalfData W P) : EllipticTwoTorsionH1 W :=
  actualClass (ellipticTwoTorsionTopRep W)
    ⟨kummerCocycleValue W hP Q,originalKummerCocycle_continuous W hP Q⟩
    (kummerCocycleValue_mul W hP Q)

end
end BSDCohomology
