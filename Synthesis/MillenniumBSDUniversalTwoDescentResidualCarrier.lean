import Synthesis.MillenniumBSDUniversalRankWeld
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Tactic

/-!
# Universal same-curve two-descent residual carrier

This is the literal arithmetic target suggested by the worked CM development.

For each exact Clay-facing RationalEllipticCurve E, require maps

  E(Q) --kummer--> Selmer₂(E) --residual--> R₂(E)

such that

* ker(kummer) is exactly 2E(Q);
* ker(residual) is exactly range(kummer);
* residual is surjective.

This is the short-exact-sequence content needed before any finite-level defect
can be identified with Sha(E)[2] or promoted to a stable Selmer-rank statement.

No rank equality, Sha identification, or BSD theorem is included.
-/

namespace Synthesis.Millennium.BSD

/-- A point lies in the literal double image 2E(Q). -/
def IsRationalPointDouble
    (E : RationalEllipticCurve) :
    E.1.toAffine.Point → Prop := by
  letI : E.1.IsElliptic := E.2
  exact fun P =>
    ∃ Q : E.1.toAffine.Point, P = Q + Q

structure UniversalTwoDescentResidualOn
    (E : RationalEllipticCurve) where
  Selmer : Type
  Residual : Type

  selmerGroup : CommGroup Selmer
  residualGroup : CommGroup Residual

  kummer :
    letI : E.1.IsElliptic := E.2
    let _ := selmerGroup
    Multiplicative E.1.toAffine.Point →* Selmer

  residualMap :
    let _ := selmerGroup
    let _ := residualGroup
    Selmer →* Residual

  kummerKernelExactlyDoubles :
    letI : E.1.IsElliptic := E.2
    let _ := selmerGroup
    ∀ P : E.1.toAffine.Point,
      kummer (Multiplicative.ofAdd P) = 1
        ↔ IsRationalPointDouble E P

  residualSurjective :
    Function.Surjective residualMap

  exactMiddle :
    letI : E.1.IsElliptic := E.2
    let _ := selmerGroup
    let _ := residualGroup
    ∀ s : Selmer,
      residualMap s = 1
        ↔
      ∃ P : E.1.toAffine.Point,
        kummer (Multiplicative.ofAdd P) = s

/-! ## Literal MW/2 source on the exact point group -/

noncomputable def rationalDoubleSubgroup
    (E : RationalEllipticCurve) :
    letI : E.1.IsElliptic := E.2
    Subgroup (Multiplicative E.1.toAffine.Point) := by
  letI : E.1.IsElliptic := E.2
  exact
    { carrier := {x | ∃ Q : E.1.toAffine.Point, x.toAdd = Q + Q}
      one_mem' := by
        refine ⟨0, ?_⟩
        simp
      mul_mem' := by
        intro x y hx hy
        rcases hx with ⟨P, hP⟩
        rcases hy with ⟨Q, hQ⟩
        refine ⟨P + Q, ?_⟩
        simp only [Multiplicative.toAdd_mul]
        rw [hP, hQ]
        abel
      inv_mem' := by
        intro x hx
        rcases hx with ⟨P, hP⟩
        refine ⟨-P, ?_⟩
        simp only [Multiplicative.toAdd_inv]
        rw [hP]
        abel }

namespace UniversalTwoDescentResidualOn

variable {E : RationalEllipticCurve}
variable (d : UniversalTwoDescentResidualOn E)

theorem rationalDoubleSubgroup_le_kummerKernel :
    letI : E.1.IsElliptic := E.2
    let _ := d.selmerGroup
    rationalDoubleSubgroup E ≤ d.kummer.ker := by
  intro x hx
  rcases hx with ⟨Q, hQ⟩
  have hDouble :
      IsRationalPointDouble E x.toAdd := by
    exact ⟨Q, hQ⟩
  exact (d.kummerKernelExactlyDoubles x.toAdd).2 hDouble

noncomputable def quotientKummerToSelmer :
    letI : E.1.IsElliptic := E.2
    let _ := d.selmerGroup
    (Multiplicative E.1.toAffine.Point ⧸ rationalDoubleSubgroup E) →*
      d.Selmer :=
  QuotientGroup.lift
    (rationalDoubleSubgroup E)
    d.kummer
    d.rationalDoubleSubgroup_le_kummerKernel

theorem quotientKummerToSelmer_injective :
    letI : E.1.IsElliptic := E.2
    let _ := d.selmerGroup
    Function.Injective d.quotientKummerToSelmer := by
  apply
    (QuotientGroup.injective_lift_iff
      d.kummer
      d.rationalDoubleSubgroup_le_kummerKernel).2
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

noncomputable local instance : CommGroup d.Selmer :=
  d.selmerGroup

noncomputable local instance : CommGroup d.Residual :=
  d.residualGroup

theorem kummer_range_eq_residual_kernel :
    letI : E.1.IsElliptic := E.2
    d.kummer.range = d.residualMap.ker := by
  ext s
  constructor
  · rintro ⟨P, rfl⟩
    exact (d.exactMiddle (d.kummer P)).2 ⟨P.toAdd, rfl⟩
  · intro hs
    have h1 : d.residualMap s = 1 := hs
    rcases (d.exactMiddle s).1 h1 with ⟨P, hP⟩
    exact ⟨Multiplicative.ofAdd P, hP⟩

theorem residual_eq_one_iff_in_kummer_range
    (s : d.Selmer) :
    letI : E.1.IsElliptic := E.2
    d.residualMap s = 1 ↔ s ∈ d.kummer.range := by
  constructor
  · intro hs
    rw [d.kummer_range_eq_residual_kernel]
    exact hs
  · intro hs
    rw [d.kummer_range_eq_residual_kernel] at hs
    exact hs

/--
If the residual carrier is trivial, every Selmer element is Kummer-visible.
This is the finite-level exact analogue of "zero defect".
-/
theorem kummer_surjective_of_subsingleton_residual
    [Subsingleton d.Residual] :
    letI : E.1.IsElliptic := E.2
    Function.Surjective d.kummer := by
  intro s
  have hs : d.residualMap s = 1 := Subsingleton.elim _ _
  rcases (d.exactMiddle s).1 hs with ⟨P, hP⟩
  exact ⟨Multiplicative.ofAdd P, hP⟩

/--
Conversely, if the Kummer map already fills Selmer and the residual map is
surjective, the residual carrier is trivial.
-/
theorem residual_subsingleton_of_kummer_surjective
    (hK : letI : E.1.IsElliptic := E.2
      Function.Surjective d.kummer) :
    Subsingleton d.Residual := by
  constructor
  intro left right
  rcases d.residualSurjective left with ⟨sLeft, hsLeft⟩
  rcases d.residualSurjective right with ⟨sRight, hsRight⟩
  letI : E.1.IsElliptic := E.2
  rcases hK sLeft with ⟨pLeft, hpLeft⟩
  rcases hK sRight with ⟨pRight, hpRight⟩
  have hLeftOne : d.residualMap sLeft = 1 := by
    rw [← hpLeft]
    exact (d.exactMiddle (d.kummer pLeft)).2 ⟨pLeft.toAdd, rfl⟩
  have hRightOne : d.residualMap sRight = 1 := by
    rw [← hpRight]
    exact (d.exactMiddle (d.kummer pRight)).2 ⟨pRight.toAdd, rfl⟩
  calc
    left = d.residualMap sLeft := hsLeft.symm
    _ = 1 := hLeftOne
    _ = d.residualMap sRight := hRightOne.symm
    _ = right := hsRight

end UniversalTwoDescentResidualOn

/-- Universal same-curve two-descent construction target. -/
def UniversalTwoDescentResidualCarrier : Prop :=
  ∀ E : RationalEllipticCurve,
    Nonempty (UniversalTwoDescentResidualOn E)

/-!
## Frontier

This file pays the correct universal TYPE of the arithmetic object.

Still open:

* construct UniversalTwoDescentResidualOn E for arbitrary literal E;
* identify Residual with the correct Sha(E)[2] carrier;
* derive finite F₂-dimension additivity when finite-dimensional structures are
  installed;
* build the 2^n / p^infinity tower needed for stable rank control.

The existing CM worked-case exact sequence is the concrete donor for these
fields, now separately pinned to cmRationalEllipticCurve.
-/

end Synthesis.Millennium.BSD
