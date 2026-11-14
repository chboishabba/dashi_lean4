import Integration.EisensteinJZeroCanonicalCubicCharacterExact
import Integration.EisensteinJZeroCubicJacobiExact

/-!
# Generic order-three character certificate for split prime fields

This owner discharges the newer RED contract added on the branch after the
canonical-character tranche.  It strengthens that tranche from one selected
character to ANY multiplicative character of exact order three on `F_p`.

For split primes `p ≡ 1 (mod 3)` we prove:

* the image of the cube map on `F_p^×` is exactly the kernel of every exact
  order-three character;
* consequently the weight `1 + ψ + ψ²` is the literal cube-fibre
  multiplicity, independent of which of the two nontrivial cubic characters
  is chosen;
* every such character therefore satisfies the existing
  `CubicCharacterCertificate` interface;
* the canonical selected certificate gives the unweighted two-Jacobi trace
  formula because `-1=(-1)^3` is a cube.

Attribution: Mathlib owns the cyclic finite-field unit-group, multiplicative
character and group-power infrastructure.  The canonical certificate and
Jacobi compiler are earlier DASHI/Lean owners on this PR.  This file owns only
the generic kernel/reindex specialization and compatibility surface.
-/

namespace Integration.EisensteinJZeroCubicCharacterCertificateExact

open scoped BigOperators
open Finset
open Integration.EisensteinJZeroCubicJacobiExact
open Integration.EisensteinJZeroCanonicalCubicCharacterExact

------------------------------------------------------------------------
-- Cube subgroup of the split prime-field unit group.
------------------------------------------------------------------------

/-- Cubing as a multiplicative endomorphism of the abelian unit group. -/
def cubeMonoidHom (p : Nat) : (ZMod p)ˣ →* (ZMod p)ˣ where
  toFun u := u ^ 3
  map_one' := by simp
  map_mul' x y := by simp [mul_pow]

/-- Nonzero cubes as an actual subgroup. -/
def cubeSubgroup (p : Nat) : Subgroup (ZMod p)ˣ :=
  (cubeMonoidHom p).range

private theorem character_pow_three_eq_one
    (p : Nat) [Fact p.Prime]
    (ψ : MulChar (ZMod p) ℂ) (hψ : orderOf ψ = 3) :
    ψ ^ 3 = 1 := by
  have h := pow_orderOf_eq_one ψ
  simpa [hψ] using h

private theorem generator_value_primitive_three
    (p : Nat) [Fact p.Prime]
    (ψ : MulChar (ZMod p) ℂ) (hψ : orderOf ψ = 3)
    {g : (ZMod p)ˣ} (hg : ∀ u : (ZMod p)ˣ, u ∈ Subgroup.zpowers g) :
    IsPrimitiveRoot (ψ g) 3 := by
  refine ⟨?_, ?_⟩
  · have hpow := character_pow_three_eq_one p ψ hψ
    have hev := congrArg (fun χ : MulChar (ZMod p) ℂ => χ g) hpow
    simpa [MulChar.pow_apply_coe] using hev
  · intro n hn
    have hchar : ψ ^ n = 1 := by
      apply (MulChar.eq_iff hg (ψ ^ n) 1).2
      simpa [MulChar.pow_apply_coe] using hn
    have hd := orderOf_dvd_of_pow_eq_one hchar
    simpa [hψ] using hd

/-- At a split prime, every exact order-three character has kernel equal to
exactly the nonzero cubes. -/
theorem cubeSubgroup_eq_orderThreeCharacterKernel
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1)
    (ψ : MulChar (ZMod p) ℂ) (hψ : orderOf ψ = 3) :
    cubeSubgroup p = ψ.toUnitHom.ker := by
  ext u
  constructor
  · rintro ⟨v, hv⟩
    change ψ u = 1
    rw [← hv]
    have hp3 := character_pow_three_eq_one p ψ hψ
    have hev := congrArg (fun χ : MulChar (ZMod p) ℂ => χ v) hp3
    simpa [map_pow, MulChar.pow_apply_coe, MulChar.one_apply_coe] using hev
  · intro hu
    change ψ u = 1 at hu
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
    obtain ⟨m, hm⟩ := hg u
    have hprim : IsPrimitiveRoot (ψ g) 3 :=
      generator_value_primitive_three p ψ hψ hg
    have hpow : (ψ g) ^ m = 1 := by
      have hmap := congrArg (fun v : (ZMod p)ˣ => ψ.toUnitHom v) hm
      have hval := congrArg (fun z : ℂˣ => (z : ℂ)) hmap
      simpa [map_zpow, MulChar.coe_toUnitHom, hu] using hval
    obtain ⟨k, hk⟩ := (hprim.zpow_eq_one_iff_dvd m).1 hpow
    refine ⟨g ^ k, ?_⟩
    have hkm : k * (3 : ℤ) = m := by
      rw [hk]
      ring
    calc
      (g ^ k) ^ (3 : Nat) = g ^ (k * (3 : ℤ)) := by
        rw [← zpow_natCast, ← zpow_mul]
      _ = g ^ m := by rw [hkm]
      _ = u := hm

------------------------------------------------------------------------
-- The character weight is independent of cubic-character orientation.
------------------------------------------------------------------------

private theorem orderThree_value_weight
    (p : Nat) [Fact p.Prime]
    (ψ : MulChar (ZMod p) ℂ) (hψ : orderOf ψ = 3)
    {t : ZMod p} (ht : t ≠ 0) :
    1 + ψ t + (ψ * ψ) t = if ψ t = 1 then 3 else 0 := by
  have hp3 := character_pow_three_eq_one p ψ hψ
  have hev := congrArg (fun χ : MulChar (ZMod p) ℂ => χ t) hp3
  have h3 : ψ t ^ 3 = 1 := by
    simpa [MulChar.pow_apply', MulChar.one_apply (isUnit_iff_ne_zero.mpr ht)] using hev
  by_cases h1 : ψ t = 1
  · simp [h1]
  · have hfac : (ψ t - 1) * (ψ t ^ 2 + ψ t + 1) = 0 := by
      calc
        (ψ t - 1) * (ψ t ^ 2 + ψ t + 1) = ψ t ^ 3 - 1 := by ring
        _ = 0 := by rw [h3]; ring
    have hquad : ψ t ^ 2 + ψ t + 1 = 0 :=
      (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr h1)
    simp only [h1, if_false, MulChar.mul_apply]
    calc
      1 + ψ t + ψ t * ψ t = ψ t ^ 2 + ψ t + 1 := by ring
      _ = 0 := hquad

private theorem arbitrary_weight_eq_canonical_weight
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1)
    (ψ : MulChar (ZMod p) ℂ) (hψ : orderOf ψ = 3)
    (t : ZMod p) :
    1 + ψ t + (ψ * ψ) t =
      1 +
        Integration.EisensteinJZeroCanonicalCubicCharacterExact.canonicalCubicCharacter
          (F := ZMod p) (by simpa [ZMod.card] using hmod) t +
        (Integration.EisensteinJZeroCanonicalCubicCharacterExact.canonicalCubicCharacter
          (F := ZMod p) (by simpa [ZMod.card] using hmod) *
         Integration.EisensteinJZeroCanonicalCubicCharacterExact.canonicalCubicCharacter
          (F := ZMod p) (by simpa [ZMod.card] using hmod)) t := by
  by_cases ht : t = 0
  · subst t
    simp
  · have hkerψ :
        ψ t = 1 ↔ ∃ x : ZMod p, x ^ 3 = t := by
      let u : (ZMod p)ˣ := Units.mk0 t ht
      have hsub := congrArg (fun H : Subgroup (ZMod p)ˣ => u ∈ H)
        (cubeSubgroup_eq_orderThreeCharacterKernel p hmod ψ hψ)
      simpa [cubeSubgroup, cubeMonoidHom, u, MonoidHom.mem_ker] using hsub
    have hcanon :=
      Integration.EisensteinJZeroCanonicalCubicCharacterExact.canonicalCubicCharacter_eq_one_iff_cube
        (F := ZMod p) (by simpa [ZMod.card] using hmod) ht
    rw [orderThree_value_weight p ψ hψ ht]
    let ψ₀ :=
      Integration.EisensteinJZeroCanonicalCubicCharacterExact.canonicalCubicCharacter
        (F := ZMod p) (by simpa [ZMod.card] using hmod)
    have hψ₀order : orderOf ψ₀ = 3 :=
      Integration.EisensteinJZeroCanonicalCubicCharacterExact.canonicalCubicCharacter_order
        (F := ZMod p) (by simpa [ZMod.card] using hmod)
    rw [orderThree_value_weight p ψ₀ hψ₀order ht]
    simp only [hkerψ, hcanon]

/-- The exact cube-fibre weighted reindexing law holds for EVERY exact
order-three character, not merely the selected canonical one. -/
theorem cubeWeightedReindex_of_orderThree
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1)
    (ψ : MulChar (ZMod p) ℂ) (hψ : orderOf ψ = 3)
    (f : ZMod p → ℂ) :
    (∑ x : ZMod p, f (x ^ 3)) =
      ∑ t : ZMod p, (1 + ψ t + (ψ * ψ) t) * f t := by
  have hcanon :=
    Integration.EisensteinJZeroCanonicalCubicCharacterExact.canonicalCubicCharacter_cubeWeightedReindex
      (F := ZMod p) (by simpa [ZMod.card] using hmod) f
  rw [hcanon]
  apply Finset.sum_congr rfl
  intro t ht
  rw [arbitrary_weight_eq_canonical_weight p hmod ψ hψ t]

------------------------------------------------------------------------
-- Compatibility package and unweighted split Jacobi trace.
------------------------------------------------------------------------

/-- Canonical certificate under the generic owner expected by downstream RED
contracts. -/
noncomputable def splitPrimeCubicCharacterCertificate
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    CubicCharacterCertificate (ZMod p) :=
  Integration.EisensteinJZeroCanonicalCubicCharacterExact.splitPrimeCubicCharacterCertificate
    p hmod

private theorem canonical_character_at_neg_one
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    (splitPrimeCubicCharacterCertificate p hmod).character (-1) = 1 := by
  have hm1 : (-1 : ZMod p) ≠ 0 := by
    simpa using (one_ne_zero : (1 : ZMod p) ≠ 0)
  change
    Integration.EisensteinJZeroCanonicalCubicCharacterExact.canonicalCubicCharacter
      (F := ZMod p) (by simpa [ZMod.card] using hmod) (-1) = 1
  apply
    (Integration.EisensteinJZeroCanonicalCubicCharacterExact.canonicalCubicCharacter_eq_one_iff_cube
      (F := ZMod p) (by simpa [ZMod.card] using hmod) hm1).2
  exact ⟨-1, by ring⟩

/-- On the canonical split certificate the `-1` weights are both one, so the
existing Jacobi compiler becomes the unweighted Jacobi pair. -/
theorem splitPrime_jZeroTrace_eq_unweightedJacobiPair
    (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    ((Integration.EisensteinJZeroFiniteFieldTraceExact.jZeroFrobeniusTraceInt
      (ZMod p) : Int) : ℂ) =
      -(jacobiSum (splitPrimeCubicCharacterCertificate p hmod).character
          quadraticCharComplex
        + jacobiSum
            ((splitPrimeCubicCharacterCertificate p hmod).character *
              (splitPrimeCubicCharacterCertificate p hmod).character)
            quadraticCharComplex) := by
  let cert := splitPrimeCubicCharacterCertificate p hmod
  have hp : 3 ≤ p := by
    have hpPrime : p.Prime := Fact.out
    have hp2 : 2 ≤ p := hpPrime.two_le
    omega
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    intro h
    subst p
    norm_num at hmod
  have hcompile :=
    Integration.EisensteinJZeroCubicJacobiExact.jZeroTrace_cast_eq_cubicJacobiTrace
      (F := ZMod p) hchar cert
  rw [hcompile]
  unfold Integration.EisensteinJZeroCubicJacobiExact.cubicJacobiTrace
  have hm1 : cert.character (-1) = 1 := by
    simpa [cert] using canonical_character_at_neg_one p hmod
  have hm1sq : (cert.character * cert.character) (-1) = 1 := by
    rw [MulChar.mul_apply, hm1]
    simp
  rw [hm1, hm1sq]
  ring

structure CubicCharacterCertificateBoundary where
  arbitraryOrderThreeKernelEqualsCubesPaid : Bool := true
  arbitraryOrderThreeCubeWeightedReindexPaid : Bool := true
  canonicalCertificateCompatibilityPaid : Bool := true
  unweightedJacobiPairTracePaid : Bool := true
  heckeCharacterPaid : Bool := false

/-- Generic split-character compatibility boundary. -/
def canonicalBoundary : CubicCharacterCertificateBoundary := {}

end Integration.EisensteinJZeroCubicCharacterCertificateExact
