import RequestProject.QuantumMereologyGeneralizedTPS2026
import Mathlib.Algebra.Star.Matrix

/-!
# Source-facing generalized TPS, short-time scrambling, and algebra distance

Zanardi--Dallas--Andreadakis formulate a g-TPS from a finite-dimensional
*-subalgebra `A` of `B(H)` together with its actual commutant `A'`.  In general
this yields a direct sum of virtual bipartitions, so the earlier DASHI carrier
consisting of two commuting subalgebras that jointly generate the full matrix
algebra is only a factor-like special case.

The 2026 source restates two exact finite-dimensional formulas used here:

  sigma_s(A,H) = || Q_A(H) ||_2,
  Q_A = 1 - P_{A + A'},

and

  D(A,B) = d^{-1} || P_A - P_B ||_HS.

This module reconstructs the corresponding squared finite-matrix formulas.
Orthogonal projections are proof-carrying inputs: no citation or subalgebra
label manufactures the source projector.  The Riemannian pullback, algebra
susceptibility, thermodynamic-limit singularity and m-QPT claims remain outside
this theorem surface.
-/

namespace QuantumMereology
namespace GTPSShortTime2026

open scoped BigOperators

abbrev MatrixSpace (n : Nat) := Matrix (Fin n) (Fin n) Complex

/-- Source-facing finite generalized TPS: one *-subalgebra plus an explicitly
identified actual commutant.  Unlike the earlier jointly-generating pair, this
carrier permits nontrivial center/direct-sum block structure. -/
structure SourceGTPS (n : Nat) where
  algebra : Subalgebra Complex (MatrixSpace n)
  commutant : Subalgebra Complex (MatrixSpace n)
  algebraStarClosed : ∀ X, X ∈ algebra → star X ∈ algebra
  commutantStarClosed : ∀ X, X ∈ commutant → star X ∈ commutant
  commutantExact :
    ∀ X, X ∈ commutant ↔ ∀ A, A ∈ algebra → Commute X A

/-- Explicit Hilbert--Schmidt inner product on finite matrices. -/
noncomputable def hsInner {n : Nat} (X Y : MatrixSpace n) : Complex :=
  ∑ i : Fin n, ∑ j : Fin n, star (X i j) * Y i j

/-- Squared Hilbert--Schmidt norm. -/
noncomputable def hsNormSq {n : Nat} (X : MatrixSpace n) : Real :=
  ∑ i : Fin n, ∑ j : Fin n, Complex.normSq (X i j)

/-- Proof-carrying orthogonal projection onto the linear subspace `A + A'`.
The witness is intentionally stronger than a bare function named `project`:
its image lies in the declared local+commutant sum, it fixes that sum, and its
residual is Hilbert--Schmidt orthogonal to every declared local+commutant
vector. -/
structure LocalPlusCommutantProjection {n : Nat} (T : SourceGTPS n) where
  project : MatrixSpace n → MatrixSpace n
  imageLocalPlusCommutant :
    ∀ X, ∃ A, A ∈ T.algebra ∧ ∃ B, B ∈ T.commutant ∧ project X = A + B
  fixesLocalPlusCommutant :
    ∀ A, A ∈ T.algebra → ∀ B, B ∈ T.commutant → project (A + B) = A + B
  residualOrthogonal :
    ∀ X A, A ∈ T.algebra → ∀ B, B ∈ T.commutant →
      hsInner (X - project X) (A + B) = 0

/-- Exact squared version of the source short-time scrambling functional.
Because `Q_A(H)=H-P_{A+A'}H`, this is `sigma_s(A,H)^2` in finite coordinates. -/
noncomputable def shortTimeScramblingSq
    {n : Nat} {T : SourceGTPS n}
    (P : LocalPlusCommutantProjection T)
    (H : MatrixSpace n) : Real :=
  hsNormSq (H - P.project H)

/-- Projection witness onto the algebra `A` itself, used by the source
information-geometric distance between g-TPSs. -/
structure AlgebraProjection {n : Nat} (T : SourceGTPS n) where
  project : MatrixSpace n → MatrixSpace n
  imageAlgebra : ∀ X, project X ∈ T.algebra
  fixesAlgebra : ∀ A, A ∈ T.algebra → project A = A
  residualOrthogonal :
    ∀ X A, A ∈ T.algebra → hsInner (X - project X) A = 0

/-- Standard matrix unit used to write the Hilbert--Schmidt norm of a linear
map in coordinates, matching the source's sum over `|l><m|`. -/
def matrixUnit {n : Nat} (l m : Fin n) : MatrixSpace n :=
  fun i j => if i = l then (if j = m then 1 else 0) else 0

/-- Squared Hilbert--Schmidt norm of a map, evaluated on the canonical matrix
units exactly as in the source definition of the map inner product. -/
noncomputable def mapHSNormSq
    {n : Nat} (F : MatrixSpace n → MatrixSpace n) : Real :=
  ∑ l : Fin n, ∑ m : Fin n, hsNormSq (F (matrixUnit l m))

/-- Squared source algebra distance

  D(A,B)^2 = d^{-2} ||P_A-P_B||_HS^2.

`hn` records the nonzero finite Hilbert-space dimension assumed by the source.
No triangle inequality or Riemannian pullback theorem is inferred here. -/
noncomputable def algebraDistanceSq
    {n : Nat} (hn : 0 < n)
    {A B : SourceGTPS n}
    (PA : AlgebraProjection A)
    (PB : AlgebraProjection B) : Real :=
  mapHSNormSq (fun X => PA.project X - PB.project X) / ((n : Real) ^ 2)

/-- Finite source-shaped short-time search.  The projector is supplied for the
same realized candidate and Hamiltonian, so the score is not an unrelated real
label. -/
structure ShortTimeFiniteSearch (n : Nat) where
  Candidate : Type
  realize : Candidate → SourceGTPS n
  admissible : Candidate → Prop
  projector : (c : Candidate) → LocalPlusCommutantProjection (realize c)
  hamiltonian : MatrixSpace n

namespace ShortTimeFiniteSearch

noncomputable def score {n : Nat} (F : ShortTimeFiniteSearch n)
    (c : F.Candidate) : Real :=
  shortTimeScramblingSq (F.projector c) F.hamiltonian

structure SelectionReceipt {n : Nat} (F : ShortTimeFiniteSearch n) where
  selected : F.Candidate
  selectedAdmissible : F.admissible selected
  minimizes : ∀ other, F.admissible other → F.score selected ≤ F.score other

/-- Finite-family minimizer for the reconstructed squared short-time source
functional.  This uses a generic finite-order theorem; it does not prove that a
physical/source-faithful candidate family is finite or nonempty. -/
noncomputable def finiteSelectionReceipt
    {n : Nat}
    (F : ShortTimeFiniteSearch n)
    [Finite F.Candidate]
    (hasAdmissible : ∃ c : F.Candidate, F.admissible c) :
    SelectionReceipt F := by
  classical
  let s : Set F.Candidate := {c | F.admissible c}
  have hsFinite : s.Finite := Set.toFinite s
  have hsNonempty : s.Nonempty := by
    rcases hasAdmissible with ⟨c, hc⟩
    exact ⟨c, hc⟩
  obtain ⟨selected, hSelected, hMinimal⟩ :=
    s.exists_min_image F.score hsFinite hsNonempty
  exact
    { selected := selected
      selectedAdmissible := hSelected
      minimizes := fun other hOther => hMinimal other hOther }

end ShortTimeFiniteSearch

structure Boundary where
  sourceGeneralGTPSCarrierReconstructed : Bool := true
  earlierJointGenerationCarrierCoversEverySourceGTPS : Bool := false
  sourceShortTimeSquaredFunctionalReconstructed : Bool := true
  sourceAlgebraDistanceSquaredFormulaReconstructed : Bool := true
  finiteShortTimeFamilyMinimizerPaid : Bool := true
  sourceProjectorAutomaticallyExistsForEveryCandidate : Bool := false
  sourceMetricAxiomsProved : Bool := false
  sourceRiemannianPullbackReconstructed : Bool := false
  algebraSusceptibilityReconstructed : Bool := false
  thermodynamicLimitMQPTReconstructed : Bool := false
  shortTimeObjectiveEqualsCarrollSinghObjective : Bool := false
deriving Repr, DecidableEq

def canonicalBoundary : Boundary := {}

theorem source_general_gtps_carrier_reconstructed :
    canonicalBoundary.sourceGeneralGTPSCarrierReconstructed = true := rfl

theorem source_short_time_squared_functional_reconstructed :
    canonicalBoundary.sourceShortTimeSquaredFunctionalReconstructed = true := rfl

theorem source_algebra_distance_squared_formula_reconstructed :
    canonicalBoundary.sourceAlgebraDistanceSquaredFormulaReconstructed = true := rfl

theorem source_projector_does_not_automatically_exist :
    canonicalBoundary.sourceProjectorAutomaticallyExistsForEveryCandidate = false := rfl

theorem algebra_susceptibility_not_reconstructed :
    canonicalBoundary.algebraSusceptibilityReconstructed = false := rfl

/-- External scientific/source authority. -/
def zanardiDallasAndreadakisSourceReceipt : AttributionReceipt where
  role := .externalSourceClaim
  owner := "Paolo Zanardi; Emanuel Dallas; Faidon Andreadakis, Mereological Quantum Phase Transitions, Phys. Rev. A 113, 042201 (2026), DOI 10.1103/r193-5s7w; arXiv:2510.06389"
  claim := "Defines g-TPSs by operator *-subalgebras and their commutants/direct-sum virtual bipartitions; restates the short-time A-OTOC scrambling rate sigma_s(A,H)=||Q_A(H)||_2 with Q_A=1-P_{A+A'}, and the algebra distance D(A',A)=d^{-1}||P_{A'}-P_A||_HS. It further develops a Riemannian pullback, algebra susceptibility and m-QPTs; those latter claims are not reconstructed by this module."

/-- Formal donor attribution. -/
def finiteMinimumFormalSourceReceipt : AttributionReceipt where
  role := .importedFormalTheoremSource
  owner := "mathlib v4.28.0, Set.Finite.exists_min_image"
  claim := "Supplies minimum existence for a real-valued score on a nonempty finite admissible set."

/-- DASHI-owned reconstruction. -/
def dashiGTPSShortTime2026Receipt : AttributionReceipt where
  role := .newDASHITheorem
  owner := "DASHI Lean"
  claim := "Reconstructs a source-facing finite g-TPS carrier with an exact commutant witness, proof-carrying orthogonal projections, the squared short-time scrambling functional ||H-P_{A+A'}H||_HS^2, the squared algebra distance d^-2||P_A-P_B||_HS^2, and finite-family minimizer existence. It does not manufacture projectors for arbitrary physical algebras, prove the source Riemannian pullback/algebra susceptibility/m-QPT theorem, or identify the objective with Carroll--Singh selection."

end GTPSShortTime2026
end QuantumMereology
