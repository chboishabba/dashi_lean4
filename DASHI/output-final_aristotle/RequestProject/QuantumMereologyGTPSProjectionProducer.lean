import RequestProject.QuantumMereologyGTPSShortTime2026
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Canonical finite Hilbert--Schmidt projectors for source-facing g-TPSs

The source short-time functional uses the Hilbert--Schmidt orthogonal projector
onto `A + A'`, and the source algebra distance uses the corresponding
projectors onto `A` and `B`.

In finite dimension these projectors are not additional physical data.  We
flatten an `n x n` complex matrix into the canonical Euclidean space indexed by
`Fin n x Fin n`, whose inner product is exactly the Hilbert--Schmidt product.
The relevant matrix subspaces are finite dimensional and therefore complete;
pinned mathlib's `Submodule.HasOrthogonalProjection.ofCompleteSpace` then
constructs their canonical orthogonal projections.

This pays the *finite mathematical projector producer*.  It does not identify a
particular physical operator algebra, Hamiltonian, or preferred subsystem with
a source g-TPS.
-/

namespace QuantumMereology
namespace GTPSProjectionProducer

open scoped BigOperators

abbrev HSSpace (n : Nat) := EuclideanSpace Complex (Fin n × Fin n)

/-- Flatten a matrix into the canonical finite L2/Euclidean carrier. -/
def toHS {n : Nat} (X : GTPSShortTime2026.MatrixSpace n) : HSSpace n :=
  WithLp.toLp 2 (fun p : Fin n × Fin n => X p.1 p.2)

/-- Unflatten the Euclidean carrier back to a matrix. -/
def fromHS {n : Nat} (x : HSSpace n) : GTPSShortTime2026.MatrixSpace n :=
  fun i j => WithLp.ofLp x (i, j)

@[simp] theorem fromHS_toHS {n : Nat}
    (X : GTPSShortTime2026.MatrixSpace n) :
    fromHS (toHS X) = X := by
  ext i j
  rfl

@[simp] theorem toHS_fromHS {n : Nat} (x : HSSpace n) :
    toHS (fromHS x) = x := by
  apply WithLp.toLp_injective 2
  funext p
  rfl

@[simp] theorem toHS_add {n : Nat}
    (X Y : GTPSShortTime2026.MatrixSpace n) :
    toHS (X + Y) = toHS X + toHS Y := by
  apply WithLp.toLp_injective 2
  funext p
  rfl

@[simp] theorem toHS_sub {n : Nat}
    (X Y : GTPSShortTime2026.MatrixSpace n) :
    toHS (X - Y) = toHS X - toHS Y := by
  apply WithLp.toLp_injective 2
  funext p
  rfl

@[simp] theorem toHS_smul {n : Nat} (c : Complex)
    (X : GTPSShortTime2026.MatrixSpace n) :
    toHS (c • X) = c • toHS X := by
  apply WithLp.toLp_injective 2
  funext p
  rfl

/-- The explicit DASHI finite Hilbert--Schmidt inner product agrees with the
native Euclidean-space inner product after flattening. -/
theorem hsInner_eq_inner_toHS {n : Nat}
    (X Y : GTPSShortTime2026.MatrixSpace n) :
    GTPSShortTime2026.hsInner X Y = inner Complex (toHS X) (toHS Y) := by
  rw [EuclideanSpace.inner_toLp_toLp]
  simp [GTPSShortTime2026.hsInner, toHS, dotProduct,
    Fintype.sum_prod_type, mul_comm]

/-- Hilbert--Schmidt image of `A + A'`, written directly as a submodule of the
canonical Euclidean matrix carrier. -/
def localPlusCommutantSubmodule {n : Nat}
    (T : GTPSShortTime2026.SourceGTPS n) : Submodule Complex (HSSpace n) where
  carrier := {x | ∃ A, A ∈ T.algebra ∧ ∃ B, B ∈ T.commutant ∧ fromHS x = A + B}
  zero_mem' := by
    refine ⟨0, T.algebra.zero_mem, 0, T.commutant.zero_mem, ?_⟩
    ext i j
    simp [fromHS]
  add_mem' := by
    rintro x y ⟨A, hA, B, hB, hx⟩ ⟨C, hC, D, hD, hy⟩
    refine ⟨A + C, T.algebra.add_mem hA hC,
      B + D, T.commutant.add_mem hB hD, ?_⟩
    ext i j
    have hxij := congrFun (congrFun hx i) j
    have hyij := congrFun (congrFun hy i) j
    simpa [fromHS, add_assoc, add_left_comm, add_comm] using congrArg₂ (· + ·) hxij hyij
  smul_mem' := by
    rintro c x ⟨A, hA, B, hB, hx⟩
    refine ⟨c • A, T.algebra.smul_mem c hA,
      c • B, T.commutant.smul_mem c hB, ?_⟩
    ext i j
    have hxij := congrFun (congrFun hx i) j
    simpa [fromHS, smul_add] using congrArg (c • ·) hxij

/-- Hilbert--Schmidt image of `A` alone. -/
def algebraSubmodule {n : Nat}
    (T : GTPSShortTime2026.SourceGTPS n) : Submodule Complex (HSSpace n) where
  carrier := {x | fromHS x ∈ T.algebra}
  zero_mem' := by simpa [fromHS] using T.algebra.zero_mem
  add_mem' := by
    intro x y hx hy
    simpa [fromHS] using T.algebra.add_mem hx hy
  smul_mem' := by
    intro c x hx
    simpa [fromHS] using T.algebra.smul_mem c hx

/-- Every finite source g-TPS has the exact HS orthogonal projection onto
`A + A'`. -/
noncomputable def localPlusCommutantProjection {n : Nat}
    (T : GTPSShortTime2026.SourceGTPS n) :
    GTPSShortTime2026.LocalPlusCommutantProjection T := by
  classical
  let U := localPlusCommutantSubmodule T
  letI : FiniteDimensional Complex U := Submodule.finiteDimensional_of_le (show U ≤ ⊤ from le_top)
  letI : CompleteSpace U := FiniteDimensional.complete Complex U
  letI : U.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace U
  refine
    { project := fun X => fromHS (U.starProjection (toHS X))
      imageLocalPlusCommutant := ?_
      fixesLocalPlusCommutant := ?_
      residualOrthogonal := ?_ }
  · intro X
    have hp : U.starProjection (toHS X) ∈ U := U.starProjection_apply_mem _
    rcases hp with ⟨A, hA, B, hB, hEq⟩
    exact ⟨A, hA, B, hB, hEq⟩
  · intro A hA B hB
    have hmem : toHS (A + B) ∈ U := by
      exact ⟨A, hA, B, hB, fromHS_toHS (A + B)⟩
    have hfix := U.starProjection_mem_subspace_eq_self ⟨toHS (A + B), hmem⟩
    exact congrArg fromHS hfix
  · intro X A hA B hB
    rw [hsInner_eq_inner_toHS]
    have hmem : toHS (A + B) ∈ U := by
      exact ⟨A, hA, B, hB, fromHS_toHS (A + B)⟩
    have horth := Submodule.starProjection_inner_eq_zero
      (K := U) (toHS X) (toHS (A + B)) hmem
    simpa using horth

/-- Every finite source algebra also has its exact HS orthogonal projection. -/
noncomputable def algebraProjection {n : Nat}
    (T : GTPSShortTime2026.SourceGTPS n) :
    GTPSShortTime2026.AlgebraProjection T := by
  classical
  let U := algebraSubmodule T
  letI : FiniteDimensional Complex U := Submodule.finiteDimensional_of_le (show U ≤ ⊤ from le_top)
  letI : CompleteSpace U := FiniteDimensional.complete Complex U
  letI : U.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace U
  refine
    { project := fun X => fromHS (U.starProjection (toHS X))
      imageAlgebra := ?_
      fixesAlgebra := ?_
      residualOrthogonal := ?_ }
  · intro X
    exact U.starProjection_apply_mem _
  · intro A hA
    have hmem : toHS A ∈ U := by simpa using hA
    have hfix := U.starProjection_mem_subspace_eq_self ⟨toHS A, hmem⟩
    exact congrArg fromHS hfix
  · intro X A hA
    rw [GTPSShortTime2026.hsInner_eq_inner_toHS]
    have hmem : toHS A ∈ U := by simpa using hA
    have horth := Submodule.starProjection_inner_eq_zero
      (K := U) (toHS X) (toHS A) hmem
    simpa using horth

/-- Fully instantiated finite short-time score for every source g-TPS and
finite Hamiltonian matrix. -/
noncomputable def canonicalShortTimeScramblingSq {n : Nat}
    (T : GTPSShortTime2026.SourceGTPS n)
    (H : GTPSShortTime2026.MatrixSpace n) : Real :=
  GTPSShortTime2026.shortTimeScramblingSq (localPlusCommutantProjection T) H

/-- Fully instantiated finite algebra distance between two source g-TPSs. -/
noncomputable def canonicalAlgebraDistanceSq {n : Nat} (hn : 0 < n)
    (A B : GTPSShortTime2026.SourceGTPS n) : Real :=
  GTPSShortTime2026.algebraDistanceSq hn (algebraProjection A) (algebraProjection B)

structure Boundary where
  hilbertSchmidtEuclideanCarrierPaid : Bool := true
  localPlusCommutantProjectorProduced : Bool := true
  algebraProjectorProduced : Bool := true
  finiteSourceGTPSShortTimeScoreFullyInstantiated : Bool := true
  finiteSourceGTPSAlgebraDistanceFullyInstantiated : Bool := true
  physicalSourceGTPSAutomaticallyIdentified : Bool := false
  physicalHamiltonianAutomaticallyAttached : Bool := false
  sourceRiemannianMetricAutomaticallyReconstructed : Bool := false
deriving Repr, DecidableEq

def canonicalBoundary : Boundary := {}

theorem local_plus_commutant_projector_produced :
    canonicalBoundary.localPlusCommutantProjectorProduced = true := rfl

theorem algebra_projector_produced :
    canonicalBoundary.algebraProjectorProduced = true := rfl

theorem finite_source_gtps_short_time_score_fully_instantiated :
    canonicalBoundary.finiteSourceGTPSShortTimeScoreFullyInstantiated = true := rfl

theorem physical_source_gtps_not_automatic :
    canonicalBoundary.physicalSourceGTPSAutomaticallyIdentified = false := rfl

/-- Formal theorem-source attribution for finite-dimensional orthogonal
projection. -/
def mathlibOrthogonalProjectionSourceReceipt : AttributionReceipt where
  role := .importedFormalTheoremSource
  owner := "mathlib v4.28.0: EuclideanSpace/PiLp inner product and Submodule.HasOrthogonalProjection.ofCompleteSpace"
  claim := "Supplies the canonical finite L2 inner-product carrier and orthogonal projection onto every complete finite-dimensional subspace."

/-- DASHI theorem receipt. -/
def dashiGTPSProjectionProducerReceipt : AttributionReceipt where
  role := .newDASHITheorem
  owner := "DASHI Lean"
  claim := "Flattens finite complex matrices into EuclideanSpace indexed by matrix entries, identifies the explicit DASHI Hilbert--Schmidt product with the native Euclidean inner product, constructs the finite subspaces A and A+A', and uses pinned mathlib orthogonal projection to instantiate the exact source projectors. Thus the finite short-time scrambling and algebra-distance formulas no longer require separately supplied projector witnesses. This does not identify a physical algebra/Hamiltonian or reconstruct the source Riemannian susceptibility/m-QPT theorem."

end GTPSProjectionProducer
end QuantumMereology
