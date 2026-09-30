import BSDStoll.ActualArithmeticSelmerDefect
import EllipticCurves.SelmerGroup
import Mathlib.GroupTheory.Coset.Card

/-!
# Genuine finite-level arithmetic factorization

This file extracts unconditional consequences of the independently defined
Stoll arithmetic objects, WITHOUT identifying the residual with Sha[2].

For any selected normal-form curve and all-place Selmer group:
  C₂(W) = Sel₂(W) / im(μ).

Hence, at the level of Nat.card,
  #Sel₂(W) = #C₂(W) * #im(μ).

Stoll independently proves ker μ = 2E(K), so im μ is the actual
E(K)/2E(K) Kummer quotient. The missing cohomological theorem is exactly
C₂(W) ≃ Sha(W)[2]; no abstract residual is substituted here.
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

/-- The genuine residual is automatically finite whenever the genuine
all-place Selmer group is finite. -/
theorem finite_actualTwoSelmerDefect
    [Finite (W.selmerGroup₂ R Loc)] :
    Finite (ActualTwoSelmerDefect W R Loc) := by
  infer_instance

/-- Exact cardinality factorization for the actual arithmetic quotient. -/
theorem card_selmer_eq_card_defect_mul_card_kummerRange :
    Nat.card (W.selmerGroup₂ R Loc)
      =
    Nat.card (ActualTwoSelmerDefect W R Loc)
      *
    Nat.card (globalKummerIntoActualSelmer W R Loc).range := by
  exact
    Subgroup.card_eq_card_quotient_mul_card_subgroup
      (globalKummerIntoActualSelmer W R Loc).range

/-- The point-image subgroup has exactly the cardinality of the quotient
of the genuine rational point group by ker μ. -/
theorem card_globalKummerRange_eq_card_pointQuotient :
    Nat.card (globalKummerIntoActualSelmer W R Loc).range
      =
    Nat.card
      (Multiplicative W.Point ⧸ (W.μ).ker) := by
  let f :
      Multiplicative W.Point →*
        W.selmerGroup₂ R Loc :=
    globalKummerIntoActualSelmer W R Loc
  calc
    Nat.card f.range
        = Nat.card (Multiplicative W.Point ⧸ f.ker) := by
            exact
              (Nat.card_congr
                (QuotientGroup.quotientKerEquivRange f)).symm
    _ = Nat.card (Multiplicative W.Point ⧸ (W.μ).ker) := by
      have hker : f.ker = (W.μ).ker := by
        ext P
        simp [f, globalKummerIntoActualSelmer]
      rw [hker]

/-- Stoll's actual x-T Kummer kernel is the doubled rational-point subgroup.
This exposes the exact arithmetic source of the quotient term. -/
theorem card_globalKummerRange_eq_card_modDoubles :
    Nat.card (globalKummerIntoActualSelmer W R Loc).range
      =
    Nat.card
      (Multiplicative W.Point ⧸
        (nsmulAddMonoidHom (α := W.Point) 2).range.toSubgroup) := by
  rw [card_globalKummerRange_eq_card_pointQuotient]
  rw [W.ker_μ_eq]

/-- Fully expanded finite-level arithmetic factorization:
Selmer size = arithmetic defect size × rational-point mod-doubles size.

No Sha or analytic rank statement is used. -/
theorem card_selmer_eq_card_defect_mul_card_modDoubles :
    Nat.card (W.selmerGroup₂ R Loc)
      =
    Nat.card (ActualTwoSelmerDefect W R Loc)
      *
    Nat.card
      (Multiplicative W.Point ⧸
        (nsmulAddMonoidHom (α := W.Point) 2).range.toSubgroup) := by
  rw [card_selmer_eq_card_defect_mul_card_kummerRange]
  rw [card_globalKummerRange_eq_card_modDoubles]

/-!
This is the strongest finite arithmetic statement available before the
cohomological comparison. Once C₂(W) ≃ Sha(W)[2] is genuinely proved,
the right factor becomes the Tate–Shafarevich two-torsion contribution.
Until then, this file deliberately calls it only the arithmetic defect.
-/

end

end BSDStoll
