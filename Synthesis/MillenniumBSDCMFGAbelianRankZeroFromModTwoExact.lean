import Synthesis.MillenniumBSDCMOriginalMWTwoTorsionRepresentativesExact
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.Torsion
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.Tactic

/-!
# K3: finite generation plus literal two-torsion modulo-doubles coverage

This file uses Mathlib's genuine structure theorem for finitely
generated abelian groups. It proves a general result:

  If G is finitely generated abelian, and every g is t + 2u
  with 2t=0, then G is finite.

The proof rules out every nonzero free Z-summand: an element with
first free coordinate 1 cannot equal a 2-torsion free coordinate
plus an even free coordinate. This is not a dimension receipt.

The original selected E(Q) source already proves the required
literal equation P=T+2U. The EXACT remaining independent
Mordell–Weil gate is an inhabited AddGroup.FG
RationalProjectivePoint instance/theorem. We do not postulate it
and do not claim it has been produced.

Mathlib attribution: GroupTheory/FiniteAbelian/Basic,
AddCommGroup.equiv_free_prod_directSum_zmod.
Exact-head local Lean kernel run remains pending.
-/

namespace Synthesis.Millennium.BSD

open scoped DirectSum

/-- Genuine f.g. abelian-group finiteness theorem from the
structure theorem: if every mod-2 class has a 2-torsion lift,
no free Z-summand can survive. -/
theorem cmFGAbelian_finite_of_modDoubles_twoTorsion
    (G : Type*) [AddCommGroup G] [AddGroup.FG G]
    (h : ∀ g : G, ∃ t u : G,
      (2 : ℕ) • t = 0 ∧ g = t + (2 : ℕ) • u) :
    Finite G := by
  classical
  obtain ⟨n, ι, hι, p, hp, e, ⟨φ⟩⟩ :=
    AddCommGroup.equiv_free_prod_directSum_zmod G
  letI : Fintype ι := hι
  by_cases hn : n = 0
  · subst n
    haveI : ∀ i : ι, NeZero (p i ^ e i) := fun i =>
      ⟨pow_ne_zero _ (hp i).ne_zero⟩
    haveI : Finite (⨁ i : ι, ZMod (p i ^ e i)) :=
      Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
    haveI : Finite ((Fin 0 →₀ ℤ) ×
        (⨁ i : ι, ZMod (p i ^ e i))) := inferInstance
    exact Finite.of_equiv _ φ.symm
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let i0 : Fin n := ⟨0, hnpos⟩
    let g0 : G :=
      φ.symm (Finsupp.single i0 (1 : ℤ), 0)
    obtain ⟨t, u, ht, hg⟩ := h g0
    have htcoord : (2 : ℕ) • ((φ t).1 i0) = 0 := by
      have hh :=
        congrArg
          (fun z : (Fin n →₀ ℤ) ×
            (⨁ i : ι, ZMod (p i ^ e i)) => z.1 i0)
          (congrArg φ ht)
      simpa using hh
    have hgcoord :
        (1 : ℤ) = ((φ t).1 i0) +
          (2 : ℕ) • ((φ u).1 i0) := by
      have hh :=
        congrArg
          (fun z : (Fin n →₀ ℤ) ×
            (⨁ i : ι, ZMod (p i ^ e i)) => z.1 i0)
          (congrArg φ hg)
      simpa [g0] using hh
    omega

/-- Actual selected-curve consumer. This takes *only* a
finite-generation instance, not an abstract rank or dimension
receipt. The literal modulo-doubles hypothesis is already a
proved source declaration on RationalProjectivePoint. -/
theorem cmSelectedRationalPoints_finite_of_MW_finiteGeneration
    [AddGroup.FG RationalProjectivePoint] :
    Finite RationalProjectivePoint := by
  apply cmFGAbelian_finite_of_modDoubles_twoTorsion
    RationalProjectivePoint
  intro P
  exact cmEveryRationalPoint_eq_twoTorsion_add_double P


/-- Conditional only on the genuine original E(Q) finite-generation
instance, the original Mordell–Weil Z-module has rank ZERO.
No abstract dimension receipt is supplied. The rank deduction
uses the original mathlib finite-abelian group structure theorem,
finite-group torsion, and rank_eq_zero_iff_isTorsion. -/
theorem cmSelectedOriginalMordellWeil_ZRank_zero
    [AddGroup.FG RationalProjectivePoint] :
    Module.rank ℤ RationalProjectivePoint = 0 := by
  letI : Finite RationalProjectivePoint :=
    cmSelectedRationalPoints_finite_of_MW_finiteGeneration
  have hTorsion : Module.IsTorsion ℤ RationalProjectivePoint :=
    (AddMonoid.isTorsion_iff_isTorsion_int).mp
      (AddGroup.is_add_torsion_of_finite :
        AddMonoid.IsTorsion RationalProjectivePoint)
  exact (rank_eq_zero_iff_isTorsion
    (R := ℤ) (M := RationalProjectivePoint)).mpr hTorsion

end Synthesis.Millennium.BSD
