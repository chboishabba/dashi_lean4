import Synthesis.MillenniumBSDUniversalTwoDescentResidualCarrier
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Tactic

/-!
# BSD: arbitrary-residual countermodels of bare two-descent exactness

For EVERY literal rational elliptic curve E and EVERY commutative group R,
the abstract structure UniversalTwoDescentResidualOn E has the model

    Selmer := (E(Q) / 2 E(Q)) × R,
    Residual := R,
    kummer(P) := ([P], 1),
    residualMap(q, r) := r.

Its Kummer kernel is exactly 2 E(Q), its residual map is onto, and its
middle is exact. This model uses no global/local Selmer cohomology.

Therefore even fixing the curve and Kummer kernel leaves the bare residual
COMPLETELY ARBITRARY: the old interface cannot determine Sha(E)[2], finite
defect, torsion, stable rank, or analytic rank.

This is a genuine family of semantic countermodels, not a reformulation of
a desired rank theorem.
-/

namespace Synthesis.Millennium.BSD

noncomputable section

/-- One and the same rational elliptic curve admits the bare exact sequence
with an arbitrarily chosen residual commutative group. -/
noncomputable def arbitraryResidualTwoDescent
    (E : RationalEllipticCurve)
    (R : Type) [CommGroup R] :
    UniversalTwoDescentResidualOn E := by
  letI : E.1.IsElliptic := E.2
  let G := Multiplicative E.1.toAffine.Point
  let N : Subgroup G := rationalDoubleSubgroup E
  letI : N.Normal := Subgroup.normal_of_comm N
  letI : CommGroup (G ⧸ N) := inferInstance
  let k : G →* (G ⧸ N) × R :=
    { toFun := fun p => (QuotientGroup.mk' N p, 1)
      map_one' := by
        simp
      map_mul' := by
        intro p q
        simp [map_mul] }
  let residual : ((G ⧸ N) × R) →* R :=
    { toFun := Prod.snd
      map_one' := rfl
      map_mul' := by intros; rfl }
  refine
    { Selmer := (G ⧸ N) × R
      Residual := R
      selmerGroup := inferInstance
      residualGroup := inferInstance
      kummer := k
      residualMap := residual
      kummerKernelExactlyDoubles := ?_
      residualSurjective := ?_
      exactMiddle := ?_ }
  · intro P
    change (QuotientGroup.mk' N (Multiplicative.ofAdd P), (1 : R))
        = (1, 1) ↔ IsRationalPointDouble E P
    simp only [Prod.mk.injEq, and_true]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rfl
  · intro r
    exact ⟨(1, r), rfl⟩
  · intro s
    rcases s with ⟨q, r⟩
    change r = 1 ↔
      ∃ P : E.1.toAffine.Point, k (Multiplicative.ofAdd P) = (q, r)
    constructor
    · intro hr
      obtain ⟨p, hp⟩ := QuotientGroup.mk'_surjective N q
      refine ⟨p.toAdd, ?_⟩
      change
        (QuotientGroup.mk' N p, (1 : R)) = (q, r)
      exact Prod.ext hp hr.symm
    · rintro ⟨P, hP⟩
      have hSecond := congrArg Prod.snd hP
      exact hSecond.symm

/-- The chosen residual in the model is definitionally the selected group. -/
theorem arbitraryResidualTwoDescent_residual
    (E : RationalEllipticCurve)
    (R : Type) [CommGroup R] :
    (arbitraryResidualTwoDescent E R).Residual = R :=
  rfl

/-- In particular, bare exactness admits nontrivial two-torsion residual
models, by choosing the additive group Z/2Z and tagging it multiplicatively. -/
noncomputable def twoTorsionResidualCountermodel
    (E : RationalEllipticCurve) :
    UniversalTwoDescentResidualOn E :=
  arbitraryResidualTwoDescent E (Multiplicative (ZMod 2))

theorem twoTorsionResidualCountermodel_nontrivial
    (E : RationalEllipticCurve) :
    Nontrivial (twoTorsionResidualCountermodel E).Residual := by
  change Nontrivial (Multiplicative (ZMod 2))
  infer_instance

/-!
Thus even "there exists an exact sequence with nontrivial residual" is a
tautology under the original interface. Genuine BSD progress requires an
independently defined Sel_2(E) from global cohomology and ALL local Kummer
conditions, together with a proved identification of its cokernel with
Sha(E)[2]. Neither residual=0 nor residual≠0 is the general BSD rank theorem.
-/

end

end Synthesis.Millennium.BSD
