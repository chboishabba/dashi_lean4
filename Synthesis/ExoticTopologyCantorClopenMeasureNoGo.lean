import Mathlib.Tactic
import Synthesis.ExoticTopologyCantorInverseLimit

/-!
# Exact dyadic/clopen obstruction between two Cantor product measures

Existing owners:
- DASHI.Foundations.CantorProjectiveCylinderMeasureExact (dyadic mass);
- dashi_agda PR #1254 variable-length code 3->0,6->10,9->11;
- Integration.Address (finite prefix carrier);
- Synthesis.ExoticTopologyCantorInverseLimit (stream/projective-limit
  EQUIVALENCE; not currently a proved topological homeomorphism).

In the fair binary product measure, each length-n clopen cylinder
has mass 1/2^n, hence a FINITE UNION of equal-depth cylinders has
mass k/2^n. Under the uniform three-symbol product measure, the
first-digit cylinder has mass 1/3. No equality is possible.

The Lean theorem below DISCHARGES THE UNIVERSAL NUMBER-THEORETIC CORE,
not the topological compactness/cylinder-basis lemma or a measure
preserving homeomorphism nonexistence theorem: those remain an external
Mathlib topology + probability supplier obligation.

Primary mathematical source: elementary prime-divisibility / Cantor
clopen product topology. No novel named attribution is claimed.
-/

namespace Synthesis.ExoticTopology

/-- No dyadic cylinder-union numerator, at ANY level, can equal 1/3.
    If k/2^n=1/3 then 3*k=2^n, contradicting primality of 3. -/
theorem noDyadicClopenMassEqualsOneThird (n k : ℕ) :
    3 * k ≠ 2 ^ n := by
  intro h
  have hd : (3 : ℕ) ∣ 2 ^ n := ⟨k, h.symm⟩
  have hprime : Nat.Prime 3 := by norm_num
  have impossible : (3 : ℕ) ∣ 2 :=
    hprime.dvd_of_dvd_pow hd
  norm_num at impossible

/-- The three codeword cylinder masses are 1/2,1/4,1/4,
    not the uniform ternary mass 1/3 each. -/
theorem binaryPrefixCodeMassesNotUniformTernary :
    ((1 : ℚ) / 2 ≠ (1 : ℚ) / 3) ∧
    ((1 : ℚ) / 4 ≠ (1 : ℚ) / 3) := by
  constructor <;> norm_num

end Synthesis.ExoticTopology
