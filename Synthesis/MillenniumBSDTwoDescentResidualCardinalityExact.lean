import Synthesis.MillenniumBSDUniversalTwoDescentResidualCarrier
import Mathlib.GroupTheory.Index
import Mathlib.Tactic

/-!
# BSD finite two-descent residual cardinality

The universal two-descent residual carrier already has the exact same-curve
short-exact-sequence shape

  E(Q)/2E(Q) -> Selmer₂(E) -> R₂(E).

This file extracts the first nontrivial quantitative consequence without adding
any Selmer-rank or Sha premise:

  |Selmer₂(E)| = |E(Q)/2E(Q)| * |R₂(E)|

with Nat.card, so the statement remains honest even before finiteness is
installed.  For finite elementary 2-groups this is precisely the cardinal form
of the familiar F₂-dimension additivity.

No identification R₂(E) = Sha(E)[2] is asserted here.
-/

namespace Synthesis.Millennium.BSD

noncomputable section

namespace UniversalTwoDescentResidualOn

variable {E : RationalEllipticCurve}
variable (d : UniversalTwoDescentResidualOn E)

noncomputable local instance : CommGroup d.Selmer :=
  d.selmerGroup

noncomputable local instance : CommGroup d.Residual :=
  d.residualGroup

/-- The Kummer kernel is literally the subgroup of rational doubles. -/
theorem kummerKernel_eq_rationalDoubleSubgroup :
    letI : E.1.IsElliptic := E.2
    d.kummer.ker = rationalDoubleSubgroup E := by
  letI : E.1.IsElliptic := E.2
  ext x
  constructor
  · intro hx
    have hDouble :
        IsRationalPointDouble E x.toAdd :=
      (d.kummerKernelExactlyDoubles x.toAdd).1 hx
    rcases hDouble with ⟨Q, hQ⟩
    exact ⟨Q, hQ⟩
  · intro hx
    exact d.rationalDoubleSubgroup_le_kummerKernel hx

/-- Surjectivity identifies the literal range of the residual map with its
codomain as a plain carrier. -/
noncomputable def residualRangeEquiv :
    d.residualMap.range ≃ d.Residual where
  toFun := fun x => x.1
  invFun := fun y =>
    ⟨y, by
      rcases d.residualSurjective y with ⟨s, hs⟩
      exact ⟨s, hs⟩⟩
  left_inv := by
    intro x
    exact Subtype.ext rfl
  right_inv := by
    intro y
    rfl

/-- First isomorphism theorem plus residual surjectivity. -/
noncomputable def quotientResidualEquiv :
    (d.Selmer ⧸ d.residualMap.ker) ≃ d.Residual :=
  (QuotientGroup.quotientKerEquivRange d.residualMap).toEquiv.trans
    d.residualRangeEquiv

theorem residualKernelIndex_eq_cardResidual :
    d.residualMap.ker.index = Nat.card d.Residual := by
  rw [Subgroup.index_eq_card]
  exact Nat.card_congr d.quotientResidualEquiv

/-- The actual Mordell-Weil-mod-2 quotient is equivalent to the Kummer range. -/
noncomputable def mordellWeilModuloTwoEquivKummerRange :
    letI : E.1.IsElliptic := E.2
    (Multiplicative E.1.toAffine.Point ⧸ rationalDoubleSubgroup E)
      ≃
    d.kummer.range := by
  letI : E.1.IsElliptic := E.2
  exact
    (QuotientGroup.quotientMulEquivOfEq
      (d.kummerKernel_eq_rationalDoubleSubgroup.symm)).toEquiv.trans
      (QuotientGroup.quotientKerEquivRange d.kummer).toEquiv

theorem cardKummerRange_eq_cardMordellWeilModuloTwo :
    letI : E.1.IsElliptic := E.2
    Nat.card d.kummer.range
      =
    Nat.card
      (Multiplicative E.1.toAffine.Point ⧸ rationalDoubleSubgroup E) := by
  letI : E.1.IsElliptic := E.2
  exact
    (Nat.card_congr d.mordellWeilModuloTwoEquivKummerRange).symm

/--
Literal finite-level same-curve defect factorization.

This is the exact group-cardinality consequence of

  ker(residual) = range(kummer)

plus residual surjectivity and the exact Kummer kernel.
-/
theorem selmerCard_eq_mordellWeilModuloTwo_mul_residualCard :
    letI : E.1.IsElliptic := E.2
    Nat.card d.Selmer
      =
    Nat.card
        (Multiplicative E.1.toAffine.Point ⧸ rationalDoubleSubgroup E)
      * Nat.card d.Residual := by
  letI : E.1.IsElliptic := E.2
  have hLagrange :=
    Subgroup.index_mul_card d.residualMap.ker
  have hIndex :
      d.residualMap.ker.index = Nat.card d.Residual :=
    d.residualKernelIndex_eq_cardResidual
  have hKernel :
      Nat.card d.residualMap.ker = Nat.card d.kummer.range := by
    rw [← d.kummer_range_eq_residual_kernel]
  calc
    Nat.card d.Selmer
        =
      d.residualMap.ker.index * Nat.card d.residualMap.ker := by
        exact hLagrange.symm
    _ =
      Nat.card d.Residual * Nat.card d.kummer.range := by
        rw [hIndex, hKernel]
    _ =
      Nat.card d.kummer.range * Nat.card d.Residual := by
        exact Nat.mul_comm _ _
    _ =
      Nat.card
          (Multiplicative E.1.toAffine.Point ⧸ rationalDoubleSubgroup E)
        * Nat.card d.Residual := by
        rw [d.cardKummerRange_eq_cardMordellWeilModuloTwo]

/--
Zero residual is exactly the finite-level case in which the Selmer cardinal is
already the Mordell-Weil-mod-2 cardinal, provided the residual carrier has
cardinality one.
-/
theorem selmerCard_eq_mordellWeilModuloTwo_of_residualCardOne
    (hResidual : Nat.card d.Residual = 1) :
    letI : E.1.IsElliptic := E.2
    Nat.card d.Selmer
      =
    Nat.card
      (Multiplicative E.1.toAffine.Point ⧸ rationalDoubleSubgroup E) := by
  letI : E.1.IsElliptic := E.2
  rw [d.selmerCard_eq_mordellWeilModuloTwo_mul_residualCard, hResidual]
  simp

end UniversalTwoDescentResidualOn

/-!
## Frontier

The abstract rank equation

  selmerRank = mordellWeilRank + defectRank

now has a literal finite-level arithmetic donor:

  |Selmer₂(E)| = |E(Q)/2E(Q)| * |R₂(E)|.

Still unpaid:

* finiteness / elementary-2 structure needed to convert cardinalities to
  F₂-dimensions uniformly;
* identification of R₂(E) with the correct Sha(E)[2];
* passage to the 2^n or 2^infinity tower needed for stable rank control;
* the analytic comparison.

So the next BSD theorem is no longer an abstract defect equation: it is the
tower/identification theorem that promotes this same-curve finite exact sequence
into stable arithmetic rank information.
-/

end

end Synthesis.Millennium.BSD
