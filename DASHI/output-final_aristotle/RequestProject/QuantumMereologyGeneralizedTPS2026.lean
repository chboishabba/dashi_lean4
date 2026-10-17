import RequestProject.QuantumMereologySelectionConvergence2026
import Mathlib.Algebra.Algebra.Subalgebra.Matrix
import Mathlib.Data.Set.Finite.Lemmas

/-!
# Finite-dimensional operator-algebra generalized TPS selection

Zanardi--Dallas--Andreadakis (2026) formulate generalized tensor-product
structures through operator-algebra families and select them by minimizing a
scrambling functional.  This module does not reconstruct their paper-specific
functional or information metric.  It pays a narrower formal seam that the
repo previously lacked: a literal finite-dimensional operator-algebra g-TPS
carrier and a generic finite-family minimizer compiler.

A `GeneralizedTPS n` consists of two complex matrix subalgebras that commute
elementwise and jointly generate the whole matrix algebra.  This is a concrete
algebraic carrier, not a claim that every physical subsystem decomposition is
captured by one such pair or that it is equivalent to the Carroll--Singh TPS
surface.
-/

namespace QuantumMereology
namespace GeneralizedTPS2026

/-- Finite-dimensional two-factor generalized TPS as commuting operator
subalgebras that jointly generate the ambient full matrix algebra. -/
structure GeneralizedTPS (n : ℕ) where
  left : Subalgebra ℂ (Matrix (Fin n) (Fin n) ℂ)
  right : Subalgebra ℂ (Matrix (Fin n) (Fin n) ℂ)
  commute : ∀ a ∈ left, ∀ b ∈ right, Commute a b
  jointlyGenerate : left ⊔ right = ⊤

/-- A declared finite candidate family of generalized TPSs together with an
application-specific admissibility predicate and scrambling score.  The score
is intentionally abstract: the Zanardi source functional is not reconstructed
by this owner. -/
structure FiniteSearchFamily (n : ℕ) where
  Candidate : Type
  realize : Candidate → GeneralizedTPS n
  admissible : Candidate → Prop
  scramblingScore : Candidate → ℝ

/-- Proof-relevant selected candidate minimizing the declared scrambling score
on the admissible subset of the finite family. -/
structure SelectionReceipt {n : ℕ} (F : FiniteSearchFamily n) where
  selected : F.Candidate
  selectedAdmissible : F.admissible selected
  minimizes : ∀ other, F.admissible other →
    F.scramblingScore selected ≤ F.scramblingScore other

/-- Generic finite-order compiler: a finite candidate carrier with at least one
admissible candidate has a scrambling-score minimizer.  This is a DASHI/mathlib
finite-order theorem, not a theorem from the 2026 physics paper. -/
noncomputable def finiteSelectionReceipt
    {n : ℕ}
    (F : FiniteSearchFamily n)
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
    s.exists_min_image F.scramblingScore hsFinite hsNonempty
  exact
    { selected := selected
      selectedAdmissible := hSelected
      minimizes := fun other hOther => hMinimal other hOther }

/-- Realized generalized TPS selected by the finite-family minimizer. -/
noncomputable def selectedGTPS
    {n : ℕ}
    (F : FiniteSearchFamily n)
    [Finite F.Candidate]
    (hasAdmissible : ∃ c : F.Candidate, F.admissible c) :
    GeneralizedTPS n :=
  F.realize (finiteSelectionReceipt F hasAdmissible).selected

/-- Parameter-dependent family used as a local carrier for mereological-change
experiments.  The candidate carrier is held fixed so changes can be attributed
to the declared parameter-dependent admissibility/score rather than to changing
the search universe silently. -/
structure ParametricFiniteSearch (Parameter : Type*) (n : ℕ) where
  Candidate : Type
  realize : Candidate → GeneralizedTPS n
  admissible : Parameter → Candidate → Prop
  scramblingScore : Parameter → Candidate → ℝ

/-- Freeze one parameter value into an ordinary finite search family. -/
def ParametricFiniteSearch.at
    {Parameter : Type*} {n : ℕ}
    (F : ParametricFiniteSearch Parameter n)
    (λ : Parameter) : FiniteSearchFamily n where
  Candidate := F.Candidate
  realize := F.realize
  admissible := F.admissible λ
  scramblingScore := F.scramblingScore λ

/-- A local selected-architecture change witness.  It is deliberately weaker
than the source notion of an m-QPT because no information metric, thermodynamic
limit or algebra susceptibility is reconstructed here. -/
structure SelectedArchitectureChange
    {Parameter : Type*} {n : ℕ}
    (F : ParametricFiniteSearch Parameter n)
    [Finite F.Candidate]
    (left right : Parameter)
    (leftNonempty : ∃ c, F.admissible left c)
    (rightNonempty : ∃ c, F.admissible right c) where
  changes :
    (finiteSelectionReceipt (F.at left) leftNonempty).selected ≠
      (finiteSelectionReceipt (F.at right) rightNonempty).selected

structure Boundary where
  operatorAlgebraGTPSCarrierSourceWritten : Bool := true
  finiteGTPSFamilyHasMinimizer : Bool := true
  sourceScramblingFunctionalReconstructed : Bool := false
  sourceInformationMetricReconstructed : Bool := false
  algebraSusceptibilityReconstructed : Bool := false
  finiteSelectedArchitectureChangeCreatesMQPT : Bool := false
  generalizedTPSCreatesPhysicalSubsystemAuthority : Bool := false
  generalizedTPSObjectiveEqualsCarrollSinghObjective : Bool := false
deriving Repr, DecidableEq

def canonicalBoundary : Boundary := {}

theorem operator_algebra_gtps_carrier_source_written :
    canonicalBoundary.operatorAlgebraGTPSCarrierSourceWritten = true := rfl

theorem finite_gtps_family_has_minimizer :
    canonicalBoundary.finiteGTPSFamilyHasMinimizer = true := rfl

theorem source_scrambling_functional_not_reconstructed :
    canonicalBoundary.sourceScramblingFunctionalReconstructed = false := rfl

/-- External source attribution only. -/
def zanardiDallasAndreadakis2026GTPSClaim : AttributionReceipt where
  role := .externalSourceClaim
  owner := "Paolo Zanardi; Emanuel Dallas; Faidon Andreadakis, Phys. Rev. A 113, 042201 (2026), DOI 10.1103/r193-5s7w"
  claim := "Uses variational operator-algebra families as generalized tensor-product structures, selects them by scrambling-functional minimization, and pulls back an information-geometric metric whose singular response is called algebra susceptibility. This module reconstructs only a finite-dimensional commuting/jointly-generating algebra carrier and generic finite minimization, not the source functional, metric or m-QPT theorem."

/-- Formal theorem-source attribution for the finite minimizer step. -/
def mathlibFiniteGTPSMinimumSource : AttributionReceipt where
  role := .importedFormalTheoremSource
  owner := "mathlib v4.28.0, Set.Finite.exists_min_image"
  claim := "Supplies existence of a minimum of a real-valued score on a nonempty finite admissible candidate set."

/-- DASHI-owned reconstruction/theorem receipt. -/
def dashiGeneralizedTPS2026Receipt : AttributionReceipt where
  role := .newDASHITheorem
  owner := "DASHI Lean"
  claim := "Defines a finite-dimensional two-subalgebra generalized-TPS carrier by elementwise commutation plus joint generation of the full matrix algebra, and compiles every finite nonempty admissible candidate family with a declared real scrambling score to a minimizing selection receipt. It does not reconstruct the source scrambling functional, information metric, algebra susceptibility, physical subsystem authority or equivalence with Carroll--Singh selection."

end GeneralizedTPS2026
end QuantumMereology
