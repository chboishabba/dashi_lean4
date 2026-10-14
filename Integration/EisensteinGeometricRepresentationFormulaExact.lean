import Integration.EisensteinSixUnitOrbitExact
import Integration.EisensteinDivisorCharacterProductExact

namespace Dashi.EisensteinGeometricRepresentationFormulaExact

open Finset
open Dashi.EisensteinLatticeCounting
open Dashi.EisensteinLatticeCountingMaxCut
open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinRepresentationCriterionExact
open Dashi.EisensteinSplitExponentChoiceExact
open Dashi.EisensteinSixUnitOrbitExact
open Dashi.EisensteinDivisorCharacterProductExact

------------------------------------------------------------------------
-- Same-object weld: the bounded coordinate enumerator really is the full
-- positive norm fibre.
------------------------------------------------------------------------

def geometricNormPointSet (n : Nat) : Finset (Int × Int) :=
  let r : Int := n
  let coords : Finset Int := Finset.Icc (-r) r
  (coords.product coords).filter fun p => eisensteinNorm p.1 p.2 = r

def GeometricNormPoint (n : Nat) := {p : Int × Int // p ∈ geometricNormPointSet n}

instance (n : Nat) : Fintype (GeometricNormPoint n) := Fintype.ofFinite _

/-- The coercivity identities force every coordinate of a positive norm-n
point into the enumerator's literal box `[-n,n]`. -/
theorem norm_coordinate_abs_le
    (a b : Int) (n : Nat) (hn : 0 < n)
    (hQ : eisensteinNorm a b = n) : |a| ≤ (n : Int) := by
  have ha := eisensteinNorm_coercive_a a b
  rw [hQ] at ha
  have hnI : (1 : Int) ≤ (n : Int) := by exact_mod_cast hn
  by_contra h
  have hgt : (n : Int) < |a| := lt_of_not_ge h
  have hstep : (n : Int) + 1 ≤ |a| := by omega
  have hsquare : ((n : Int) + 1) ^ 2 ≤ |a| ^ 2 := by
    nlinarith [sq_nonneg (|a| - ((n : Int) + 1))]
  have habs : |a| ^ 2 = a ^ 2 := by simp
  rw [habs] at hsquare
  nlinarith

theorem norm_coordinate_b_abs_le
    (a b : Int) (n : Nat) (hn : 0 < n)
    (hQ : eisensteinNorm a b = n) : |b| ≤ (n : Int) := by
  have hb := eisensteinNorm_coercive_b a b
  rw [hQ] at hb
  have hnI : (1 : Int) ≤ (n : Int) := by exact_mod_cast hn
  by_contra h
  have hgt : (n : Int) < |b| := lt_of_not_ge h
  have hstep : (n : Int) + 1 ≤ |b| := by omega
  have hsquare : ((n : Int) + 1) ^ 2 ≤ |b| ^ 2 := by
    nlinarith [sq_nonneg (|b| - ((n : Int) + 1))]
  have habs : |b| ^ 2 = b ^ 2 := by simp
  rw [habs] at hsquare
  nlinarith

noncomputable def normFiberToGeometricPoint
    (n : Nat) (hn : 0 < n) (H : InertEvenCondition n)
    (z : PositiveNormFiber n hn H) : GeometricNormPoint n := by
  let a := z.1.re
  let b := z.1.im
  have hQ : eisensteinNorm a b = n := by
    simpa [a, b, norm_eq_coordinate_norm] using z.2
  have ha := norm_coordinate_abs_le a b n hn hQ
  have hb := norm_coordinate_b_abs_le a b n hn hQ
  refine ⟨(a, b), ?_⟩
  simp only [geometricNormPointSet, Finset.mem_filter,
    Finset.mem_product, Finset.mem_Icc]
  exact ⟨⟨(abs_le.mp ha).1, (abs_le.mp ha).2⟩,
    ⟨(abs_le.mp hb).1, (abs_le.mp hb).2⟩, hQ⟩

noncomputable def geometricPointToNormFiber
    (n : Nat) (hn : 0 < n) (H : InertEvenCondition n)
    (p : GeometricNormPoint n) : PositiveNormFiber n hn H := by
  let z := asQuadraticAlgebra p.1.1 p.1.2
  refine ⟨z, ?_⟩
  have hQ := (Finset.mem_filter.mp p.2).2
  simpa [geometricNormPointSet, z, norm_asQuadraticAlgebra] using hQ

/-- Exact equivalence between the executable bounded enumerator and the full
ring-theoretic norm fibre. -/
noncomputable def geometricNormPointEquivFiber
    (n : Nat) (hn : 0 < n) (H : InertEvenCondition n) :
    GeometricNormPoint n ≃ PositiveNormFiber n hn H where
  toFun := geometricPointToNormFiber n hn H
  invFun := normFiberToGeometricPoint n hn H
  left_inv := by
    intro p
    apply Subtype.ext
    rcases p with ⟨⟨a, b⟩, hp⟩
    rfl
  right_inv := by
    intro z
    apply Subtype.ext
    rcases z with ⟨⟨a, b⟩, hz⟩
    rfl

/-- The subtype card is definitionally the independent finite enumerator. -/
theorem card_geometricNormPoint (n : Nat) :
    Fintype.card (GeometricNormPoint n) = geometricNormShellCount n := by
  simp [GeometricNormPoint, geometricNormPointSet, geometricNormShellCount]

/-- Representable positive norms have the literal six-unit/split-choice count. -/
theorem geometricNormShellCount_of_inertEven
    (n : Nat) (hn : 0 < n) (H : InertEvenCondition n) :
    geometricNormShellCount n
      = 6 * ∏ p ∈ splitPrimeFactors n, (n.factorization p + 1) := by
  calc
    geometricNormShellCount n = Fintype.card (GeometricNormPoint n) :=
      (card_geometricNormPoint n).symm
    _ = Fintype.card (PositiveNormFiber n hn H) :=
      Fintype.card_congr (geometricNormPointEquivFiber n hn H)
    _ = 6 * ∏ p ∈ splitPrimeFactors n, (n.factorization p + 1) :=
      card_positiveNormFiber n hn H

/-- If an inert exponent is odd, there is no geometric norm point at all. -/
theorem geometricNormShellCount_eq_zero_of_not_inertEven
    (n : Nat) (hn : 0 < n) (H : ¬ InertEvenCondition n) :
    geometricNormShellCount n = 0 := by
  have hempty : geometricNormPointSet n = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro p hp
    have hQ := (Finset.mem_filter.mp hp).2
    let z := asQuadraticAlgebra p.1 p.2
    have hz : QuadraticAlgebra.norm z = n := by
      simpa [geometricNormPointSet, z, norm_asQuadraticAlgebra] using hQ
    exact H ((norm_representable_iff_inert_even n hn).1 ⟨z, hz⟩)
  rw [← card_geometricNormPoint n]
  simp [GeometricNormPoint, hempty]

------------------------------------------------------------------------
-- Character product = the same split-prime product.
------------------------------------------------------------------------

theorem chiMinus3PrimePowerFactor_nonneg
    (p e : Nat) : 0 ≤ chiMinus3PrimePowerFactor p e := by
  have hlt : p % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases hmod : p % 3
  · rw [chiMinus3PrimePowerFactor_ramified hmod]
    norm_num
  · rw [chiMinus3PrimePowerFactor_split hmod]
    exact_mod_cast Nat.zero_le (e + 1)
  · rw [chiMinus3PrimePowerFactor_inert hmod]
    split_ifs <;> norm_num

/-- The signed character divisor sum is nevertheless globally nonnegative;
its local factors are 1, e+1, or 0/1. -/
theorem chiMinus3DivisorSum_nonneg
    (n : Nat) (hn : n ≠ 0) : 0 ≤ chiMinus3DivisorSum n := by
  rw [chiMinus3DivisorSum_factorization n hn]
  exact Finset.prod_nonneg fun p hp =>
    chiMinus3PrimePowerFactor_nonneg p (n.factorization p)

/-- On the represented branch, every non-split local factor is one. -/
theorem chiMinus3DivisorSum_eq_splitProduct
    (n : Nat) (hn : 0 < n) (H : InertEvenCondition n) :
    chiMinus3DivisorSum n
      = (∏ p ∈ splitPrimeFactors n, (n.factorization p + 1) : Nat) := by
  rw [chiMinus3DivisorSum_factorization n hn.ne']
  calc
    (∏ p ∈ n.primeFactors,
        chiMinus3PrimePowerFactor p (n.factorization p))
      = ∏ p ∈ n.primeFactors,
          (if p % 3 = 1 then ((n.factorization p + 1 : Nat) : Int) else 1) := by
          apply Finset.prod_congr rfl
          intro p hpMem
          have hp : p.Prime := Nat.prime_of_mem_primeFactors hpMem
          have hlt : p % 3 < 3 := Nat.mod_lt _ (by norm_num)
          interval_cases hmod : p % 3
          · rw [chiMinus3PrimePowerFactor_ramified hmod]
            simp [hmod]
          · rw [chiMinus3PrimePowerFactor_split hmod]
            simp [hmod]
          · rw [chiMinus3PrimePowerFactor_inert hmod, if_pos (H p hp hmod)]
            simp [hmod]
    _ = ∏ p ∈ splitPrimeFactors n,
          ((n.factorization p + 1 : Nat) : Int) := by
          simp [splitPrimeFactors]
    _ = (∏ p ∈ splitPrimeFactors n, (n.factorization p + 1) : Nat) := by
          simp

/-- Failure of the inert-even criterion forces an actual zero local factor. -/
theorem chiMinus3DivisorSum_eq_zero_of_not_inertEven
    (n : Nat) (hn : 0 < n) (H : ¬ InertEvenCondition n) :
    chiMinus3DivisorSum n = 0 := by
  have hnonneg := chiMinus3DivisorSum_nonneg n hn.ne'
  have hnotpos : ¬ 0 < chiMinus3DivisorSum n := by
    intro hpos
    exact H ((chiMinus3DivisorSum_pos_iff_inert_even n hn).1 hpos)
  omega

------------------------------------------------------------------------
-- Universal positive-n coefficient theorem.
------------------------------------------------------------------------

/-- Classical Eisenstein representation formula on the literal repo objects. -/
theorem geometricNormShell_eq_signedDivisorShell
    (n : Nat) (hn : 0 < n) :
    (geometricNormShellCount n : Int) = signedEisensteinDivisorShellCount n := by
  by_cases H : InertEvenCondition n
  · have hgeo := geometricNormShellCount_of_inertEven n hn H
    have hchi := chiMinus3DivisorSum_eq_splitProduct n hn H
    have hsigned := signedShell_eq_six_mul_character_sum n hn.ne'
    calc
      (geometricNormShellCount n : Int)
          = (6 * ∏ p ∈ splitPrimeFactors n,
              (n.factorization p + 1) : Nat) := by exact_mod_cast hgeo
      _ = 6 * chiMinus3DivisorSum n := by
            rw [hchi]
            norm_num
      _ = signedEisensteinDivisorShellCount n := hsigned.symm
  · rw [geometricNormShellCount_eq_zero_of_not_inertEven n hn H]
    rw [chiMinus3DivisorSum_eq_zero_of_not_inertEven n hn H]
    simp [signedEisensteinDivisorShellCount, chiMinus3DivisorSum,
      signedChiMinus3DivisorSum]

/-- Canonical positive indexing used by the repository bridge. -/
theorem geometricNormShell_eq_signedDivisorShell_positive (n : Nat) :
    (geometricNormShellCount (n + 1) : Int)
      = signedEisensteinDivisorShellCount (n + 1) :=
  geometricNormShell_eq_signedDivisorShell (n + 1) (Nat.succ_pos n)

/-- The formerly-open same-object bridge is now inhabited. -/
def canonicalSignedEisensteinNormRepresentationBridge :
    SignedEisensteinNormRepresentationBridge where
  representationCount := geometricNormShellCount
  representationCount_eq_signed_divisorLaw_positive :=
    geometricNormShell_eq_signedDivisorShell_positive

structure EisensteinGeometricRepresentationBoundary where
  boundedEnumeratorEqualsFullFiberPaid : Bool := true
  representableFiberCardinalityPaid : Bool := true
  nonrepresentableFiberZeroPaid : Bool := true
  characterProductCollapsedToSplitProductPaid : Bool := true
  universalPositiveRepresentationFormulaPaid : Bool := true
  signedSameObjectBridgeInhabited : Bool := true
  analyticDirichletSeriesFactorizationPaid : Bool := false

def canonicalBoundary : EisensteinGeometricRepresentationBoundary := {}

end Dashi.EisensteinGeometricRepresentationFormulaExact
