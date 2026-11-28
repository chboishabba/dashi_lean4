import Synthesis.MillenniumBSDActualCompletionKummerExact
import Mathlib.NumberTheory.NumberField.FinitePlaces
import Mathlib.NumberTheory.NumberField.InfinitePlace.Completion

/-!
Original finite and infinite completions from the pinned Mathlib layout.
Local point H1 and torsion H1 use the SAME chosen closure embedding.
The exact Selmer/Sha comparison below is on those cohomology objects;
geometric doubling surjectivity remains explicit.
-/
namespace BSDCohomology
open WeierstrassCurve CategoryTheory DASHI.BSD.OriginalH1
noncomputable section

section LocalSquare
universe u v
variable {K : Type u} [Field K] [CharZero K]
variable {L : Type v} [Field L] [CharZero L]
variable [Algebra K L] [Algebra K (AlgebraicClosure L)]
variable [IsScalarTower K L (AlgebraicClosure L)]
variable (W : WeierstrassCurve K) [W.IsElliptic]

local instance : TopologicalSpace (GeometricPoint W) := ⊥
local instance : DiscreteTopology (GeometricPoint W) := discreteTopology_bot _
local instance : TopologicalSpace (GeometricPoint (W⁄L)) := ⊥
local instance : DiscreteTopology (GeometricPoint (W⁄L)) := discreteTopology_bot _
local instance : TopologicalSpace (EllipticTwoTorsion W) := ⊥
local instance : DiscreteTopology (EllipticTwoTorsion W) := discreteTopology_bot _
local instance : TopologicalSpace (EllipticTwoTorsion (W⁄L)) := ⊥
local instance : DiscreteTopology (EllipticTwoTorsion (W⁄L)) := discreteTopology_bot _

def completionPointRep :
    TopRep.res (continuousClosureRestriction (chooseClosureEmbedding (K:=K) (L:=L)))
      (geometricPointTopRep W) ⟶ geometricPointTopRep (W⁄L) :=
  TopRep.ofHom ⟨{
    __ := (completionPointMap (L:=L) W).toIntLinearMap
    cont := continuous_of_discreteTopology
  },by
    intro σ
    ext P
    exact completionPointMap_equivariant (L:=L) W σ P⟩

def completionPointH1 : EllipticPointH1 W ⟶ EllipticPointH1 (W⁄L) :=
  ContinuousCohomology.map
    (continuousClosureRestriction (chooseClosureEmbedding (K:=K) (L:=L)))
    (completionPointRep (L:=L) W) 1

def completionTorsionH1Hom : EllipticTwoTorsionH1 W →+ EllipticTwoTorsionH1 (W⁄L) :=
  (ContinuousCohomology.map
    (continuousClosureRestriction (chooseClosureEmbedding (K:=K) (L:=L)))
    (actualCompletionTorsionRep (L:=L) W) 1).hom.toAddMonoidHom

/-- On the original crossed cocycle, inclusion and localization have
identical values. Hence the same square commutes on actual H1. -/
theorem completion_inclusion_square (x : EllipticTwoTorsionH1 W) :
    completionPointH1 (L:=L) W (originalInclusionH1 W x) =
      originalInclusionH1 (W⁄L) (actualCompletionH1 (L:=L) W x) := by
  obtain ⟨c,hc,rfl⟩ := actualClass_surjective (torsionRep W) x
  unfold completionPointH1 originalInclusionH1 actualCompletionH1
  rw [actualClass_natural,actualClass_natural,actualClass_natural,actualClass_natural]
  have hcongr (c₁ c₂ : C(Field.absoluteGaloisGroup L,pointRep (W⁄L)))
      (h₁ : Crossed (pointRep (W⁄L)) c₁)
      (h₂ : Crossed (pointRep (W⁄L)) c₂) (h : c₁=c₂) :
      actualClass (pointRep (W⁄L)) c₁ h₁ =
        actualClass (pointRep (W⁄L)) c₂ h₂ := by
    subst c₂
    rfl
  apply hcongr
  apply ContinuousMap.ext
  intro σ
  rfl

end LocalSquare

section Places
universe u
variable (K : Type u) [Field K] [NumberField K]

/-- Height-one primes are the finite places. Use the original adic
completion directly, rather than choosing a representative of an
absolute-value equivalence class. -/
abbrev OriginalPlace :=
  IsDedekindDomain.HeightOneSpectrum (𝓞 K) ⊕ NumberField.InfinitePlace K

def placeField : OriginalPlace K → Type u
  | .inl v => v.adicCompletion K
  | .inr v => v.Completion

instance placeField_field (v : OriginalPlace K) : Field (placeField K v) := by
  cases v <;> unfold placeField <;> infer_instance

instance placeField_algebra (v : OriginalPlace K) : Algebra K (placeField K v) := by
  cases v <;> unfold placeField <;> infer_instance

instance placeField_charZero (v : OriginalPlace K) : CharZero (placeField K v) :=
  CharZero.of_injective (algebraMap K (placeField K v)) (RingHom.injective _)

instance placeClosureAlgebra (v : OriginalPlace K) :
    Algebra K (AlgebraicClosure (placeField K v)) :=
  ((algebraMap (placeField K v) (AlgebraicClosure (placeField K v))).comp
    (algebraMap K (placeField K v))).toAlgebra

instance placeClosureTower (v : OriginalPlace K) :
    IsScalarTower K (placeField K v) (AlgebraicClosure (placeField K v)) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

variable {K}
variable (W : WeierstrassCurve K) [W.IsElliptic]

def localCurve (v : OriginalPlace K) := W⁄(placeField K v)

instance localCurve_elliptic (v : OriginalPlace K) : (localCurve W v).IsElliptic := by
  unfold localCurve
  infer_instance

def placeTorsionLoc (v : OriginalPlace K) :
    EllipticTwoTorsionH1 W →+ EllipticTwoTorsionH1 (localCurve W v) :=
  completionTorsionH1Hom (L:=placeField K v) W

def placePointLoc (v : OriginalPlace K) :
    EllipticPointH1 W →+ EllipticPointH1 (localCurve W v) :=
  (completionPointH1 (L:=placeField K v) W).hom.toAddMonoidHom

def placeBasePoint (v : OriginalPlace K) :
    BasePoint W →+ BasePoint (localCurve W v) :=
  completionBasePointMap (L:=placeField K v) W

theorem place_inclusion_square (v : OriginalPlace K) (x : EllipticTwoTorsionH1 W) :
    placePointLoc W v (originalInclusionH1 W x) =
      originalInclusionH1 (localCurve W v) (placeTorsionLoc W v x) :=
  completion_inclusion_square (L:=placeField K v) W x

def originalSelmerTwo
    (hs : ∀ v : OriginalPlace K, Function.Surjective
      (fun Q : GeometricPoint (localCurve W v) => (2:ℕ) • Q)) :
    AddSubgroup (EllipticTwoTorsionH1 W) :=
  ⨅ v : OriginalPlace K,
    ((rationalKummerHom (localCurve W v) (hs v)).range).comap (placeTorsionLoc W v)

/-- Genuine local-triviality on the geometric POINT coefficient, not
Sha of the torsion coefficient. This is the subgroup killed by two
inside Sha(E), written on the original global H1 carrier. -/
def originalPointShaTwo : AddSubgroup (EllipticPointH1 W) :=
  (originalDoublingH1 W).hom.toAddMonoidHom.ker ⊓
    ⨅ v : OriginalPlace K, (placePointLoc W v).ker

theorem originalSelmerTwo_mem_iff
    (hs : ∀ v : OriginalPlace K, Function.Surjective
      (fun Q : GeometricPoint (localCurve W v) => (2:ℕ) • Q))
    (x : EllipticTwoTorsionH1 W) :
    x ∈ originalSelmerTwo W hs ↔
      ∀ v : OriginalPlace K, placePointLoc W v (originalInclusionH1 W x)=0 := by
  simp only [originalSelmerTwo,AddSubgroup.mem_iInf,AddSubgroup.mem_comap]
  constructor
  · intro h v
    rw [place_inclusion_square]
    exact (originalInclusionH1_zero_iff_rationalKummer (localCurve W v) (hs v) _).mpr
      (h v)
  · intro h v
    have hv := h v
    rw [place_inclusion_square] at hv
    exact (originalInclusionH1_zero_iff_rationalKummer (localCurve W v) (hs v) _).mp hv

/-- Global Kummer classes automatically satisfy every local condition
by the already-derived localization square on the actual curve. -/
theorem globalKummer_mem_selmer
    (hsK : Function.Surjective (fun Q : GeometricPoint W => (2:ℕ) • Q))
    (hs : ∀ v : OriginalPlace K, Function.Surjective
      (fun Q : GeometricPoint (localCurve W v) => (2:ℕ) • Q))
    (P : BasePoint W) : rationalKummerClass W hsK P ∈ originalSelmerTwo W hs := by
  apply (originalSelmerTwo_mem_iff W hs _).mpr
  have hz := (originalInclusionH1_zero_iff_rationalKummer W hsK _).mpr ⟨P,rfl⟩
  intro v
  rw [hz,map_zero]

def selmerToShaTwo
    (hsK : Function.Surjective (fun Q : GeometricPoint W => (2:ℕ) • Q))
    (hs : ∀ v : OriginalPlace K, Function.Surjective
      (fun Q : GeometricPoint (localCurve W v) => (2:ℕ) • Q)) :
    originalSelmerTwo W hs →+ originalPointShaTwo W where
  toFun x := ⟨originalInclusionH1 W x.1,by
    refine ⟨?_,?_⟩
    · exact (originalDoublingH1_zero_iff_inclusion W hsK _).mpr ⟨x.1,rfl⟩
    · exact AddSubgroup.mem_iInf.mpr
        ((originalSelmerTwo_mem_iff W hs x.1).mp x.2)⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)

theorem selmerToShaTwo_surjective
    (hsK : Function.Surjective (fun Q : GeometricPoint W => (2:ℕ) • Q))
    (hs : ∀ v : OriginalPlace K, Function.Surjective
      (fun Q : GeometricPoint (localCurve W v) => (2:ℕ) • Q)) :
    Function.Surjective (selmerToShaTwo W hsK hs) := by
  intro z
  obtain ⟨x,hx⟩ := (originalDoublingH1_zero_iff_inclusion W hsK z.1).mp z.2.1
  refine ⟨⟨x,(originalSelmerTwo_mem_iff W hs x).mpr ?_⟩,Subtype.ext hx⟩
  intro v
  rw [hx]
  exact (AddSubgroup.mem_iInf.mp z.2.2) v

theorem selmerToShaTwo_kernel_iff
    (hsK : Function.Surjective (fun Q : GeometricPoint W => (2:ℕ) • Q))
    (hs : ∀ v : OriginalPlace K, Function.Surjective
      (fun Q : GeometricPoint (localCurve W v) => (2:ℕ) • Q))
    (x : originalSelmerTwo W hs) :
    selmerToShaTwo W hsK hs x=0 ↔
      ∃ P : BasePoint W, rationalKummerClass W hsK P=x.1 := by
  constructor
  · intro h
    apply (originalInclusionH1_zero_iff_rationalKummer W hsK x.1).mp
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    exact (originalInclusionH1_zero_iff_rationalKummer W hsK x.1).mpr h

end Places
end
end BSDCohomology
