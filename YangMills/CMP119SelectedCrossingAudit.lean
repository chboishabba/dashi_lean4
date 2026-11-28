import Mathlib
import YangMills.CMP119PolymerReflectionAudit

/-!
# Exhaustive proof-or-falsification audit for selected CMP119 crossing kernels

Once an actual selected source sector supplies a concrete finite crossing
kernel, there are only two mathematically relevant outcomes: every quadratic
form is nonnegative, or one test vector gives a strictly negative witness.
This file packages that dichotomy without pretending that the source-native
E/R/B kernels have already been extracted.
-/

namespace RequestProject.YangMills

/-- Exact audit result for one finite crossing kernel. -/
inductive CMP119CrossingKernelAuditOutcome
    {ι : Type*} [Fintype ι]
    (kernel : ι → ι → ℝ) : Prop
  | reflectionPositive
      (hRP : ∀ test : ι → ℝ,
        0 ≤ indexedReflectionQuadratic kernel test)
  | counterexample
      (test : ι → ℝ)
      (hneg : indexedReflectionQuadratic kernel test < 0)

/-- Every concrete finite real kernel has a proof-or-falsification audit outcome. -/
theorem cmp119_crossing_kernel_audit_complete
    {ι : Type*} [Fintype ι]
    (kernel : ι → ι → ℝ) :
    CMP119CrossingKernelAuditOutcome kernel := by
  classical
  by_cases hRP : ∀ test : ι → ℝ,
      0 ≤ indexedReflectionQuadratic kernel test
  · exact .reflectionPositive hRP
  · push_neg at hRP
    rcases hRP with ⟨test, htest⟩
    exact .counterexample test (lt_of_not_ge htest)

/-- Eliminate the audit result into the mathematically sharp dichotomy. -/
theorem cmp119_crossing_kernel_audit_dichotomy
    {ι : Type*} [Fintype ι]
    (kernel : ι → ι → ℝ)
    (audit : CMP119CrossingKernelAuditOutcome kernel) :
    (∀ test : ι → ℝ,
      0 ≤ indexedReflectionQuadratic kernel test) ∨
      ∃ test : ι → ℝ,
        indexedReflectionQuadratic kernel test < 0 := by
  cases audit with
  | reflectionPositive hRP => exact Or.inl hRP
  | counterexample test hneg => exact Or.inr ⟨test, hneg⟩

/-- A positive audit produces the exact crossing certificate consumed downstream. -/
def cmp119CrossingCertificateOfPositiveAudit
    {ι : Type*} [Fintype ι]
    (kernel : ι → ι → ℝ)
    (hSymm : ∀ i j, kernel i j = kernel j i)
    (hRP : ∀ test : ι → ℝ,
      0 ≤ indexedReflectionQuadratic kernel test) :
    CMP119SectorReflectionCertificate ι :=
  cmp119CrossingCertificate kernel hSymm hRP

/-- A negative audit formally rules out RP for that same selected kernel. -/
theorem cmp119_negative_audit_rules_out_crossing_rp
    {ι : Type*} [Fintype ι]
    (kernel : ι → ι → ℝ)
    (test : ι → ℝ)
    (hneg : indexedReflectionQuadratic kernel test < 0) :
    ¬ (∀ f : ι → ℝ,
      0 ≤ indexedReflectionQuadratic kernel f) :=
  cmp119_crossing_kernel_falsified_by_negative_quadratic kernel test hneg

/--
Source-facing three-sector audit payload.  Populating these three kernels from
CMP119 is the remaining source extraction task; this structure does not choose
or synthesize them.
-/
structure CMP119SelectedCrossingKernelFamily (ι : Type*) [Fintype ι] where
  regularE : ι → ι → ℝ
  rOperation : ι → ι → ℝ
  boundaryB : ι → ι → ℝ
  regularESymmetric : ∀ i j, regularE i j = regularE j i
  rOperationSymmetric : ∀ i j, rOperation i j = rOperation j i
  boundaryBSymmetric : ∀ i j, boundaryB i j = boundaryB j i

namespace CMP119SelectedCrossingKernelFamily

/-- Exhaustively audit all three nontrivial selected source sectors. -/
noncomputable def auditAll
    {ι : Type*} [Fintype ι]
    (family : CMP119SelectedCrossingKernelFamily ι) :
    CMP119CrossingKernelAuditOutcome family.regularE ×
      CMP119CrossingKernelAuditOutcome family.rOperation ×
      CMP119CrossingKernelAuditOutcome family.boundaryB :=
  ⟨cmp119_crossing_kernel_audit_complete family.regularE,
    cmp119_crossing_kernel_audit_complete family.rOperation,
    cmp119_crossing_kernel_audit_complete family.boundaryB⟩

end CMP119SelectedCrossingKernelFamily

end RequestProject.YangMills
