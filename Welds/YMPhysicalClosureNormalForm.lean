/-
# Yang--Mills physical closure normal form

This module turns the remaining physical Row-A1 wall into a consumer-facing
family theorem rather than another bookkeeping record.

A `RowA1CutoffFamily` is not evidence that Yang--Mills has been constructed: its
members are genuine `RowA1PhysicalGapInstance`s, so every cutoff already carries
an actual self-adjoint partial-domain Hamiltonian, normalized zero-energy vacuum,
and the same-object inequality `bMinus <= gap`.

What this file proves is the missing compiler across cutoffs:

  uniform literal finite instances
    -> one uniform Row-A1 vacuum form gap
    -> continuum graph-limit gap / zero-shift inverse bound
    -> same-evolution/common-core transport to the welded Hamiltonian.

Thus the analytic constant is not renamed or replaced between finite, continuum,
and reconstructed operators.  The physical construction of the family, graph
limit, and YM/OS evolution equality remain explicit hypotheses.
-/
import Welds.YMFinitePhysicalInstantiation

namespace Welds.YMPhysicalClosureNormalForm

open scoped InnerProductSpace
open RequestProject.YangMills.VacuumSectorSpectralGap
open RequestProject.YangMills.UnboundedHamiltonianDomain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A cutoff family whose every member is a genuine physical Row-A1 gap
instance with the same `SU(N)` and source-budget parameters. -/
structure RowA1CutoffFamily (N : ℕ) (r h : ℝ) where
  instance : ∀ n, YMFinitePhysicalInstantiation.RowA1PhysicalGapInstance (E := E) N r h

/-- The literal finite Hamiltonian selected at cutoff `n`. -/
noncomputable def cutoffOp {N : ℕ} {r h : ℝ}
    (F : RowA1CutoffFamily (E := E) N r h) (n : ℕ) : E →ₗ.[ℂ] E :=
  (F.instance n).datum.op

/-- The literal normalized vacuum selected at cutoff `n`. -/
noncomputable def cutoffVac {N : ℕ} {r h : ℝ}
    (F : RowA1CutoffFamily (E := E) N r h) (n : ℕ) : E :=
  (F.instance n).datum.vac

/-- The Row-A1 scalar used uniformly by every cutoff in the family. -/
noncomputable def rowA1Gap {N : ℕ} {r h : ℝ}
    (_F : RowA1CutoffFamily (E := E) N r h) : ℝ :=
  YangMills.bMinus (YangMills.casimirAdjointSU N) r h

/-- The uniform Row-A1 scalar is positive.  No physical spectral claim is made
here: positivity is the already-proved `LocalGap` result carried by any member
of the family. -/
theorem rowA1UniformGapPositive {N : ℕ} {r h : ℝ}
    (F : RowA1CutoffFamily (E := E) N r h) : 0 < rowA1Gap F := by
  simpa [rowA1Gap] using YMFinitePhysicalInstantiation.rowA1GapPositive (F.instance 0)

/-- Every cutoff Hamiltonian in a physical Row-A1 family obeys the *same*
quadratic-form lower bound. -/
theorem rowA1UniformCutoffFormGap {N : ℕ} {r h : ℝ}
    (F : RowA1CutoffFamily (E := E) N r h) :
    ∀ n, HasVacuumFormGap (cutoffOp F n) (cutoffVac F n) (rowA1Gap F) := by
  intro n
  simpa [cutoffOp, cutoffVac, rowA1Gap] using
    (YMFinitePhysicalInstantiation.rowA1VacuumFormGap (F.instance n))

/-- **Finite -> continuum quantitative closure.**  A graph limit of a genuine
uniform Row-A1 physical cutoff family inherits the same zero-shift inverse
budget. -/
theorem rowA1ContinuumZeroShiftBound
    {N : ℕ} {r h : ℝ} (F : RowA1CutoffFamily (E := E) N r h)
    {Hinf : E →ₗ.[ℂ] E} {vac : E}
    (hlim : RequestProject.YangMills.ContinuumGapTransport.IsVacuumGraphLimit
      (cutoffOp F) (cutoffVac F) Hinf vac)
    (hsa : IsSelfAdjoint Hinf) (hmem : vac ∈ Hinf.domain)
    (hunit : ‖vac‖ = 1) (hground : Hinf ⟨vac, hmem⟩ = 0)
    {ψ : Hinf.domain} (hψorth : ⟪vac, (ψ : E)⟫_ℂ = 0) :
    ‖(ψ : E)‖ ≤ (rowA1Gap F)⁻¹ * ‖Hinf ψ‖ := by
  exact YMVacuumGapBackwardBounds.continuumZeroShiftResolventBound
    (hgap := rowA1UniformCutoffFormGap F)
    hlim hsa hmem hunit hground (rowA1UniformGapPositive F) hψorth

/-- **Full operator-side BIDI closure compiler.**

Starting with a genuine uniform finite physical Row-A1 family, an actual
vacuum-sector graph limit, and a genuine equality of YM/OS evolutions on a
common core, the same `bMinus` controls the welded continuum Hamiltonian.

The hypotheses are exactly the remaining physical same-object obligations;
this theorem introduces no substitute gap, Hamiltonian, or reconstruction
receipt. -/
theorem rowA1SameObjectContinuumZeroShiftBound
    {N : ℕ} {r h : ℝ} (F : RowA1CutoffFamily (E := E) N r h)
    {Hinf Hos : E →ₗ.[ℂ] E} {vac : E}
    (hlim : RequestProject.YangMills.ContinuumGapTransport.IsVacuumGraphLimit
      (cutoffOp F) (cutoffVac F) Hinf vac)
    (hsa : IsSelfAdjoint Hinf) (hmem : vac ∈ Hinf.domain)
    (hunit : ‖vac‖ = 1) (hground : Hinf ⟨vac, hmem⟩ = 0)
    {U V : ℝ → E → E} {S : Submodule ℂ E}
    (hUV : U = V)
    (hcInf : Hinf.HasCore S) (hcOS : Hos.HasCore S)
    (hgInf : IsPMapEvolutionGenerator U S Hinf)
    (hgOS : IsPMapEvolutionGenerator V S Hos)
    {ψ : Hos.domain} (hψorth : ⟪vac, (ψ : E)⟫_ℂ = 0) :
    ‖(ψ : E)‖ ≤ (rowA1Gap F)⁻¹ * ‖Hos ψ‖ := by
  exact YMVacuumGapBackwardBounds.chainZeroShiftResolventBound
    (hgap := rowA1UniformCutoffFormGap F)
    hlim hsa hmem hunit hground (rowA1UniformGapPositive F)
    hUV hcInf hcOS hgInf hgOS hψorth

#print axioms rowA1UniformGapPositive
#print axioms rowA1UniformCutoffFormGap
#print axioms rowA1ContinuumZeroShiftBound
#print axioms rowA1SameObjectContinuumZeroShiftBound

end Welds.YMPhysicalClosureNormalForm
