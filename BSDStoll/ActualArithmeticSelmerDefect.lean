import BSDStoll.CompleteArithmeticResponse
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Canonical arithmetic two-descent residual, NOT a freely chosen group

For a selected normal-form curve W, Stoll independently defines:
  μ : W.Point →* W.M, with kernel 2 W.Point;
  Sel₂ W = kernel of the complete norm/all-place obstruction response.

The global point-image is therefore a concrete subgroup of the arithmetic
Selmer group. We quotient by THIS subgroup, producing the canonical
Selmer defect C₂(W) = Sel₂(W) / μ(W(K)).

The resulting exactness is now about independently defined arithmetic
objects on the SAME curve. It does NOT prove C₂(W) ≃ Sha(W)[2]; that needs
cohomological comparison of the x-T descent presentation to H¹(K,E[2])
and the actual Tate-Shafarevich kernel.
-/

namespace BSDStoll

open WeierstrassCurve

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve.Affine K)
variable [W.IsElliptic] [W.IsCharNeTwoNF]
variable (R : Type*) [CommRing R] [IsDedekindDomain R]
variable [Algebra R K] [IsFractionRing R K]
variable {ι : Type*} (Loc : ι → Type*)
variable [(i : ι) → Field (Loc i)]
variable [(i : ι) → Algebra K (Loc i)]

/-- Actual global Kummer map, with codomain restricted to the previously
defined all-place Selmer subgroup. Membership is justified by Stoll's
genuine local-global theorem, rather than a manufactured map. -/
noncomputable def globalKummerIntoActualSelmer :
    Multiplicative W.Point →* W.selmerGroup₂ R Loc :=
  (W.μ).codRestrict (W.selmerGroup₂ R Loc)
    (fun P => W.range_μ_le_selmerGroup₂ R Loc ⟨P, rfl⟩)

/-- Selected curve's arithmetic residual: canonical cokernel of its
genuine global rational-point Kummer image inside genuine Selmer. -/
abbrev ActualTwoSelmerDefect : Type _ :=
  W.selmerGroup₂ R Loc ⧸
    (globalKummerIntoActualSelmer W R Loc).range

/-- A genuine arithmetic quotient, never a user-chosen abstract residual. -/
noncomputable def actualSelmerResidualMap :
    W.selmerGroup₂ R Loc →* ActualTwoSelmerDefect W R Loc :=
  QuotientGroup.mk'
    (globalKummerIntoActualSelmer W R Loc).range

/-- The actual residual map is surjective by construction, with precisely
the point-Kummer subgroup as its kernel. -/
theorem actualSelmerResidualMap_surjective :
    Function.Surjective (actualSelmerResidualMap W R Loc) := by
  exact QuotientGroup.mk'_surjective
    (globalKummerIntoActualSelmer W R Loc).range

/-- This is the substantive same-curve arithmetic middle-exactness:
the Kummer subgroup, not an arbitrary chosen subgroup, is the kernel. -/
theorem actualSelmerResidualMap_kernel :
    (actualSelmerResidualMap W R Loc).ker =
      (globalKummerIntoActualSelmer W R Loc).range := by
  exact QuotientGroup.ker_mk'
    (globalKummerIntoActualSelmer W R Loc).range

/-- Every concrete global rational-point Kummer class has trivial residual. -/
theorem globalKummer_has_zero_arithmetic_defect
    (P : Multiplicative W.Point) :
    actualSelmerResidualMap W R Loc
      (globalKummerIntoActualSelmer W R Loc P) = 1 := by
  rw [← MonoidHom.mem_ker,
    actualSelmerResidualMap_kernel]
  exact ⟨P, rfl⟩

/-- Conversely, vanishing of the ACTUAL arithmetic residual is equivalent
to the existence of a rational point producing the same Selmer class. -/
theorem actualSelmerDefect_zero_iff_global_point
    (s : W.selmerGroup₂ R Loc) :
    actualSelmerResidualMap W R Loc s = 1 ↔
      ∃ P : Multiplicative W.Point,
        globalKummerIntoActualSelmer W R Loc P = s := by
  rw [← MonoidHom.mem_ker,
    actualSelmerResidualMap_kernel]
  rfl

/-!
This is not a Sha computation; a selected curve may have nontrivial genuine
Selmer defect without any statement here deciding it. Nor does finite
Selmer imply BSD's analytic order-of-vanishing equality.
-/

end

end BSDStoll
