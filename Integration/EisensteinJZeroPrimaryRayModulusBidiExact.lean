import Integration.EisensteinJZeroPrimaryNormalizationExact

/-!
# Original j=0 primary ↔ ray 2√(-3) BIDI, every split prime

This directly consumes the EXISTING #73 theorem
  splitPrime_primary_associate_existsUnique
instead of reproving six-unit normalisation by Jacobi character sums.

For EisensteinQA = ℤ[ω], f = 2+4ω = 2√(-3), norm f=12.
An odd-norm prime element z is primary (Even z.im and
Trace(z)=2*z.re-z.im ≡ 2 mod 3) IFF z≡1 mod f.

As a result: every norm-p Eisenstein element for every rational
split prime p%3=1 admits EXACTLY ONE of the six units yielding
ray-congruence one. This is a norm-prime algebraic theorem, NOT the
claim that the original #69 Jacobi element uses specifically unit -1.

Original #69 canonical Jacobi element belongs to ANOTHER BRANCH:
do not import it here without a source-preserving dependency merge.
This code adds no global Hecke ideal character or L-function theorem.

Source-written, uncompiled: Lean kernel/axioms/CI acceptance OPEN.
-/

namespace Dashi.EisensteinJZeroPrimaryRayModulusBidiExact

open Dashi.EisensteinLatticeCounting
open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinRepresentationCriterionExact
open Dashi.EisensteinSixUnitsExact
open Dashi.EisensteinJZeroPrimaryNormalizationExact

/-- The literal ideal generator f=2(1+2ω), norm 12. -/
def rayModulus : EisensteinQA := asQuadraticAlgebra 2 4

def OneModRay (z : EisensteinQA) : Prop :=
  ∃ w : EisensteinQA, z - 1 = rayModulus * w

theorem rayModulus_norm :
    QuadraticAlgebra.norm rayModulus = 12 := by
  simp [rayModulus, norm_asQuadraticAlgebra, eisensteinNorm]
  norm_num

/-- Converse needs no norm assumption: a ray-one element automatically
has even imaginary coordinate and trace 2 modulo 3. -/
theorem primary_of_ray (z : EisensteinQA)
    (h : OneModRay z) : IsJZeroPrimary z := by
  obtain ⟨w, hw⟩ := h
  have hre : z.re - 1 = 2 * w.re - 4 * w.im := by
    have heq := congrArg QuadraticAlgebra.re hw
    simp [rayModulus, asQuadraticAlgebra] at heq
    omega
  have him : z.im = 4 * w.re - 2 * w.im := by
    have heq := congrArg QuadraticAlgebra.im hw
    simp [rayModulus, asQuadraticAlgebra] at heq
    omega
  constructor
  · refine ⟨2 * w.re - w.im, ?_⟩
    omega
  · change (2 * z.re - z.im) ≡ 2 [ZMOD 3]
    simp only [Int.ModEq]
    omega

/-- Original primary and norm p imply the real coordinate is odd.
This is the existing #73 parity argument, re-exported locally so
the original source module remains unchanged. -/
private theorem original_primary_real_odd
    (p : Nat) (hp : p.Prime) (hmod : p % 3 = 1)
    (z : EisensteinQA) (hz : QuadraticAlgebra.norm z = p)
    (hprimary : IsJZeroPrimary z) : Odd z.re := by
  have hnot : ¬ Even z.re := by
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
    have hEq : 2 = p :=
      (Nat.prime_dvd_prime_iff_eq h2prime hp).mp h2p
    subst p
    norm_num at hmod
  exact (Int.not_even_iff_odd).mp hnot

/-- The forward equivalence is an explicit integral quotient:
z.re=2u+1, z.im=2v, u+v=3k
then (z-1)/f=(v-k)+(k-u)ω. -/
theorem ray_of_primary_odd_real (z : EisensteinQA)
    (hodd : Odd z.re) (hp : IsJZeroPrimary z) :
    OneModRay z := by
  obtain ⟨u, hu⟩ := hodd
  obtain ⟨v, hv⟩ := hp.1
  have htr : (2 * z.re - z.im) % 3 = 2 := by
    simpa [Int.ModEq, jZeroTrace] using hp.2
  have hsum : (u + v) % 3 = 0 := by
    rw [hu, hv] at htr
    omega
  obtain ⟨k, hk⟩ : 3 ∣ u + v :=
    (Int.dvd_iff_emod_eq_zero).2 hsum
  refine ⟨asQuadraticAlgebra (v - k) (k - u), ?_⟩
  ext <;> simp [rayModulus, asQuadraticAlgebra, hu, hv] <;> omega

/-- THE EXACT BIDI for every norm-p element over any rational split prime. -/
theorem primary_iff_ray_of_split_norm
    (p : Nat) (hp : p.Prime) (hmod : p % 3 = 1)
    (z : EisensteinQA) (hz : QuadraticAlgebra.norm z = p) :
    IsJZeroPrimary z ↔ OneModRay z := by
  constructor
  · intro hprimary
    exact ray_of_primary_odd_real z
      (original_primary_real_odd p hp hmod z hz hprimary)
      hprimary
  · exact primary_of_ray z

/-- The old #73 six-unit existence/uniqueness transports unchanged
across the exact primary↔ray BIDI: no all-prime Jacobi congruence
is needed to find a unique primary associate. -/
theorem splitPrime_ray_unit_existsUnique
    (p : Nat) (hp : p.Prime) (hmod : p % 3 = 1)
    (z : EisensteinQA) (hz : QuadraticAlgebra.norm z = p) :
    ∃! u : EisensteinQA, u ∈ eisensteinUnits ∧ OneModRay (u * z) := by
  obtain ⟨u, ⟨hu, huPrimary⟩, hunique⟩ :=
    splitPrime_primary_associate_existsUnique p hp hmod z hz
  have hnorm (v : EisensteinQA) (hv : v ∈ eisensteinUnits) :
      QuadraticAlgebra.norm (v * z) = p := by
    rw [map_mul,
      (isUnit_iff_norm_eq_one v).1 (all_listed_units_are_units v hv),
      one_mul, hz]
  refine ⟨u, ⟨hu,
    (primary_iff_ray_of_split_norm p hp hmod (u * z) (hnorm u hu)).mp huPrimary⟩,
    ?_⟩
  intro v hv
  exact hunique v ⟨hv.1,
    (primary_iff_ray_of_split_norm p hp hmod (v * z) (hnorm v hv.1)).mpr hv.2⟩

#print axioms primary_of_ray
#print axioms original_primary_real_odd
#print axioms ray_of_primary_odd_real
#print axioms primary_iff_ray_of_split_norm
#print axioms splitPrime_ray_unit_existsUnique

end Dashi.EisensteinJZeroPrimaryRayModulusBidiExact
