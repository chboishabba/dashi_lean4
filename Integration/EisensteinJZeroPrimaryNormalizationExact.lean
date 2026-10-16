import Integration.EisensteinSixUnitOrbitExact
import Mathlib.Data.Int.ModEq

namespace Dashi.EisensteinJZeroPrimaryNormalizationExact

open Dashi.EisensteinLatticeCounting
open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinSplitPrimeExact
open Dashi.EisensteinSixUnitsExact

/-!
The normalization here is the element-level form of the classical primary
Eisenstein generator used for the CM Hecke character of the level-36 `j=0`
curve.  In the `1,ω` basis, `a+bω = A+B√-3` has

  `2A = 2a-b`,  `2B = b`.

For odd norm, the source condition "A ≡ 1 (mod 3) and exactly one of A,B is
even" is equivalently captured by: `b` is even and `2a-b ≡ 2 (mod 3)`.

Source context: W.-C. W. Li, L. Long, F.-T. Tu,
"Computing Special L-Values of Certain Modular Forms with Complex
Multiplication", SIGMA 14 (2018), 090, Proposition 4.1/4.4 depending edition,
arXiv:1803.06072.  The proofs below independently discharge the six-unit
normalization on the repository's explicit Eisenstein carrier; the source is
not treated as a Lean proof term.
-/

/-- Twice the `√-3`-basis real coefficient; equivalently the field trace of
`a+bω`. -/
def jZeroTrace (z : EisensteinQA) : Int := 2 * z.re - z.im

/-- Conductor-style primary normalization in the repository's `(1,ω)` basis. -/
def IsJZeroPrimary (z : EisensteinQA) : Prop :=
  Even z.im ∧ jZeroTrace z ≡ 2 [ZMOD 3]

instance (z : EisensteinQA) : Decidable (IsJZeroPrimary z) := inferInstance

/-- The elementary discriminant identity behind the normalization. -/
theorem trace_square_plus_three_im_square (a b : Int) :
    (2 * a - b) ^ 2 + 3 * b ^ 2 = 4 * eisensteinNorm a b := by
  simp [eisensteinNorm]
  ring

/-- If `t²+3c²=4p` with `p ≡ 1 (mod 3)`, then `t` is congruent to either
`1` or `2` modulo three. -/
theorem trace_residue_one_or_two
    (p : Nat) (hmod : p % 3 = 1) (t c : Int)
    (hdisc : t ^ 2 + 3 * c ^ 2 = 4 * (p : Int)) :
    t ≡ 1 [ZMOD 3] ∨ t ≡ 2 [ZMOD 3] := by
  have ht0 : t % 3 ≠ 0 := by
    intro hzero
    have hdivt : (3 : Int) ∣ t := (Int.dvd_iff_emod_eq_zero).2 hzero
    rcases hdivt with ⟨k, hk⟩
    have hdiv4p : (3 : Int) ∣ 4 * (p : Int) := by
      refine ⟨3 * k ^ 2 + c ^ 2, ?_⟩
      rw [← hdisc, hk]
      ring
    have hprime3 : Prime (3 : Int) := by norm_num
    rcases hprime3.dvd_mul.mp hdiv4p with h34 | h3p
    · norm_num at h34
    · have h3pnat : 3 ∣ p := by exact_mod_cast h3p
      have hp0 : p % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp h3pnat
      omega
  have hlo : 0 ≤ t % 3 := Int.emod_nonneg _ (by norm_num)
  have hhi : t % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  have hcases : t % 3 = 1 ∨ t % 3 = 2 := by omega
  rcases hcases with h1 | h2
  · left
    simpa [Int.ModEq, h1]
  · right
    simpa [Int.ModEq, h2]

private theorem neg_modEq_two_of_modEq_one {t : Int} (h : t ≡ 1 [ZMOD 3]) :
    -t ≡ 2 [ZMOD 3] := by
  have hn := h.neg
  exact hn.trans (by norm_num [Int.ModEq])

/-- Every split-prime norm factor admits one of the explicit six unit multiples
in primary form. -/
theorem splitPrime_primary_unit_exists
    (p : Nat) (hp : p.Prime) (hmod : p % 3 = 1)
    (z : EisensteinQA) (hz : QuadraticAlgebra.norm z = p) :
    ∃ u : EisensteinQA, u ∈ eisensteinUnits ∧ IsJZeroPrimary (u * z) := by
  rcases z with ⟨a, b⟩
  have hzQ : eisensteinNorm a b = p := by
    simpa [norm_eq_coordinate_norm] using hz
  by_cases hb : Even b
  · have hdisc : (2 * a - b) ^ 2 + 3 * b ^ 2 = 4 * (p : Int) := by
      rw [trace_square_plus_three_im_square, hzQ]
    rcases trace_residue_one_or_two p hmod (2 * a - b) b hdisc with ht | ht
    · refine ⟨unitNegOne, by simp [eisensteinUnits], ?_⟩
      have hneg := neg_modEq_two_of_modEq_one ht
      constructor
      · simpa [unitNegOne, asQuadraticAlgebra] using hb.neg
      · simpa [jZeroTrace, unitNegOne, asQuadraticAlgebra] using hneg
    · refine ⟨unitOne, by simp [eisensteinUnits], ?_⟩
      constructor
      · simpa [unitOne, asQuadraticAlgebra] using hb
      · simpa [jZeroTrace, unitOne, asQuadraticAlgebra] using ht
  · by_cases hab : Even (a - b)
    · have hdisc : (a + b) ^ 2 + 3 * (a - b) ^ 2 = 4 * (p : Int) := by
        rw [← hzQ]
        simp [eisensteinNorm]
        ring
      rcases trace_residue_one_or_two p hmod (a + b) (a - b) hdisc with ht | ht
      · refine ⟨unitOmega, by simp [eisensteinUnits], ?_⟩
        have hneg := neg_modEq_two_of_modEq_one ht
        constructor
        · simpa [unitOmega, asQuadraticAlgebra] using hab
        · simpa [jZeroTrace, unitOmega, asQuadraticAlgebra] using hneg
      · refine ⟨unitNegOmega, by simp [eisensteinUnits], ?_⟩
        constructor
        · simpa [unitNegOmega, asQuadraticAlgebra] using hab.neg
        · simpa [jZeroTrace, unitNegOmega, asQuadraticAlgebra] using ht
    · have hbOdd : Odd b := (Int.not_even_iff_odd).mp hb
      have habOdd : Odd (a - b) := (Int.not_even_iff_odd).mp hab
      have ha : Even a := by
        rcases hbOdd with ⟨k, hk⟩
        rcases habOdd with ⟨l, hl⟩
        refine ⟨k + l + 1, ?_⟩
        omega
      have hdisc : (a - 2 * b) ^ 2 + 3 * a ^ 2 = 4 * (p : Int) := by
        rw [← hzQ]
        simp [eisensteinNorm]
        ring
      rcases trace_residue_one_or_two p hmod (a - 2 * b) a hdisc with ht | ht
      · refine ⟨unitOmegaSquared, by simp [eisensteinUnits], ?_⟩
        have hneg := neg_modEq_two_of_modEq_one ht
        constructor
        · simpa [unitOmegaSquared, asQuadraticAlgebra] using ha.neg
        · simpa [jZeroTrace, unitOmegaSquared, asQuadraticAlgebra] using hneg
      · refine ⟨unitNegOmegaSquared, by simp [eisensteinUnits], ?_⟩
        constructor
        · simpa [unitNegOmegaSquared, asQuadraticAlgebra] using ha
        · simpa [jZeroTrace, unitNegOmegaSquared, asQuadraticAlgebra] using ht

/-- On an odd split-prime norm shell, the real coefficient is odd once the
imaginary coefficient is even. -/
private theorem re_not_even_of_primary_split_norm
    (p : Nat) (hp : p.Prime) (hmod : p % 3 = 1)
    (z : EisensteinQA) (hz : QuadraticAlgebra.norm z = p)
    (hprimary : IsJZeroPrimary z) :
    ¬ Even z.re := by
  intro ha
  rcases hprimary.1 with ⟨kb, hkb⟩
  rcases ha with ⟨ka, hka⟩
  have hzQ : eisensteinNorm z.re z.im = p := by
    simpa [norm_eq_coordinate_norm] using hz
  have h2pInt : (2 : Int) ∣ (p : Int) := by
    refine ⟨2 * (ka ^ 2 - ka * kb + kb ^ 2), ?_⟩
    rw [← hzQ, hka, hkb]
    simp [eisensteinNorm]
    ring
  have h2p : 2 ∣ p := by exact_mod_cast h2pInt
  have h2prime : Nat.Prime 2 := by norm_num
  have hEq : 2 = p := (Nat.prime_dvd_prime_iff_eq h2prime hp).mp h2p
  subst p
  norm_num at hmod

/-- A primary split-prime element has trivial stabilizer under the six-unit
(or, equivalently, full unit) action. -/
theorem primary_unit_stabilizer_trivial
    (p : Nat) (hp : p.Prime) (hmod : p % 3 = 1)
    (z : EisensteinQA) (hz : QuadraticAlgebra.norm z = p)
    (hprimary : IsJZeroPrimary z)
    (u : EisensteinQA) (hu : IsUnit u)
    (huPrimary : IsJZeroPrimary (u * z)) :
    u = unitOne := by
  have haNotEven := re_not_even_of_primary_split_norm p hp hmod z hz hprimary
  have huClass := unit_classification u hu
  rcases z with ⟨a, b⟩
  rcases huClass with h | h | h | h | h | h
  · exact h
  · have hnegTrace : -(2 * a - b) ≡ 2 [ZMOD 3] := by
      simpa [h, IsJZeroPrimary, jZeroTrace, unitNegOne, asQuadraticAlgebra] using huPrimary.2
    have hback := hnegTrace.neg
    have hc := hprimary.2.symm.trans hback
    norm_num [Int.ModEq] at hc
  · have habEven : Even (a - b) := by
      simpa [h, IsJZeroPrimary, unitOmega, asQuadraticAlgebra] using huPrimary.1
    have hbEven := hprimary.1
    apply (haNotEven)
    rcases habEven with ⟨k, hk⟩
    rcases hbEven with ⟨l, hl⟩
    refine ⟨k + l, ?_⟩
    omega
  · have hbaEven : Even (b - a) := by
      simpa [h, IsJZeroPrimary, unitNegOmega, asQuadraticAlgebra] using huPrimary.1
    have hbEven := hprimary.1
    apply (haNotEven)
    rcases hbaEven with ⟨k, hk⟩
    rcases hbEven with ⟨l, hl⟩
    refine ⟨l - k, ?_⟩
    omega
  · have hnegaEven : Even (-a) := by
      simpa [h, IsJZeroPrimary, unitOmegaSquared, asQuadraticAlgebra] using huPrimary.1
    exact haNotEven hnegaEven.neg
  · have haEven : Even a := by
      simpa [h, IsJZeroPrimary, unitNegOmegaSquared, asQuadraticAlgebra] using huPrimary.1
    exact haNotEven haEven

/-- The primary unit multiplier is unique among the explicit six units. -/
theorem splitPrime_primary_unit_unique
    (p : Nat) (hp : p.Prime) (hmod : p % 3 = 1)
    (z : EisensteinQA) (hz : QuadraticAlgebra.norm z = p)
    (u v : EisensteinQA)
    (huMem : u ∈ eisensteinUnits) (hvMem : v ∈ eisensteinUnits)
    (huPrimary : IsJZeroPrimary (u * z))
    (hvPrimary : IsJZeroPrimary (v * z)) :
    u = v := by
  have huUnit := all_listed_units_are_units u huMem
  have hvUnit := all_listed_units_are_units v hvMem
  rcases huUnit with ⟨U, rfl⟩
  rcases hvUnit with ⟨V, rfl⟩
  let w : EisensteinQAˣ := V * U⁻¹
  have hnormUz : QuadraticAlgebra.norm ((U : EisensteinQA) * z) = p := by
    rw [map_mul, (isUnit_iff_norm_eq_one (U : EisensteinQA)).1 U.isUnit, one_mul, hz]
  have hwPrimary : IsJZeroPrimary ((w : EisensteinQA) * ((U : EisensteinQA) * z)) := by
    have heq : (w : EisensteinQA) * ((U : EisensteinQA) * z) = (V : EisensteinQA) * z := by
      simp [w, mul_assoc, mul_comm, mul_left_comm]
    rwa [heq]
  have hwOne := primary_unit_stabilizer_trivial p hp hmod
    ((U : EisensteinQA) * z) hnormUz huPrimary (w : EisensteinQA) w.isUnit hwPrimary
  have hwUnit : w = 1 := by
    apply Units.ext
    simpa [unitOne] using hwOne
  have hVU : V = U := by
    calc
      V = (V * U⁻¹) * U := by simp
      _ = w * U := by rfl
      _ = U := by rw [hwUnit]; simp
  exact congrArg Units.val hVU

/-- Existence and uniqueness packaged as one exact six-unit normalization
statement. -/
theorem splitPrime_primary_associate_existsUnique
    (p : Nat) (hp : p.Prime) (hmod : p % 3 = 1)
    (z : EisensteinQA) (hz : QuadraticAlgebra.norm z = p) :
    ∃! u : EisensteinQA,
      u ∈ eisensteinUnits ∧ IsJZeroPrimary (u * z) := by
  obtain ⟨u, huMem, huPrimary⟩ := splitPrime_primary_unit_exists p hp hmod z hz
  refine ⟨u, ⟨huMem, huPrimary⟩, ?_⟩
  intro v hv
  exact splitPrime_primary_unit_unique p hp hmod z hz v u hv.1 huMem hv.2 huPrimary

/-- Claim-strength boundary: primary unit normalization is now paid purely
algebraically.  The next theorem must identify the trace of this selected
primary factor with the Frobenius trace of the same `j=0` elliptic curve; that
is the genuine CM/Hecke bridge and is not inferred from norm data alone. -/
structure PrimaryNormalizationBoundary where
  primaryPredicatePaid : Bool := true
  splitPrimePrimaryExistencePaid : Bool := true
  trivialPrimaryUnitStabilizerPaid : Bool := true
  splitPrimePrimaryUniquenessPaid : Bool := true
  frobeniusTraceIdentificationPaid : Bool := false
  heckeCharacterPaid : Bool := false
  globalEllipticHeckeLSeriesIdentityPaid : Bool := false

/-- Exact current primary-normalization frontier. -/
def canonicalBoundary : PrimaryNormalizationBoundary := {}

end Dashi.EisensteinJZeroPrimaryNormalizationExact
