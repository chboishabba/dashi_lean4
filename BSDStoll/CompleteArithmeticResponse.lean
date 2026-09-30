import BSDStoll.CompleteLocalObstruction
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Complete Selmer response as ONE independently defined arithmetic homomorphism

The components here are the literal Stoll maps on a fixed normal-form
Weierstrass curve:
  normM : W.M →* Units.modPow K 2;
  localRes L followed by quotient by im(local point Kummer).

The product is indexed by ALL height-one primes of R and the chosen family
of infinite completions. Nothing in its codomain is a user-chosen residual,
and the map is constructed before the kernel comparison.

Mathematical statement:
  ker(completeArithmeticResponse W R Loc) = W.selmerGroup₂ R Loc.

This is Selmer membership, NOT Sha(E)[2]. In particular the quotient of
Selmer by the global image of μ is a later, different arithmetic object.
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

/-- Genuine norm/finite-place/infinite-place output group, with each local
coordinate carrying the entire square-class coset rather than a Boolean
observer that might hide a nontrivial obstruction. -/
abbrev CompleteArithmeticResponseGroup :=
    (Units.modPow K 2) ×
    ((v : HeightOneSpectrum R) →
      LocalKummerObstruction W (v.adicCompletion K)) ×
    ((i : ι) → LocalKummerObstruction W (Loc i))

/-- Full simultaneous arithmetic response. The local components are
independently defined quotient homomorphisms, not selected to force
exactness. -/
noncomputable def completeArithmeticResponse :
    W.M →* CompleteArithmeticResponseGroup W R Loc :=
  (W.normM).prod
    ((MonoidHom.pi fun v : HeightOneSpectrum R =>
      localObstruction W (v.adicCompletion K)).prod
      (MonoidHom.pi fun i : ι => localObstruction W (Loc i)))

/-- A single homomorphism contains the complete local arithmetic balance.
Vanishing is exactly membership in the independently defined Stoll group. -/
theorem mem_ker_completeArithmeticResponse_iff
    (c : W.M) :
    c ∈ (completeArithmeticResponse W R Loc).ker ↔
      c ∈ W.selmerGroup₂ R Loc := by
  rw [MonoidHom.mem_ker]
  change
    (W.normM c,
      ((fun v : HeightOneSpectrum R =>
        localObstruction W (v.adicCompletion K) c),
       (fun i : ι => localObstruction W (Loc i) c))) = 1 ↔
      c ∈ W.selmerGroup₂ R Loc
  rw [show
      (W.normM c,
        ((fun v : HeightOneSpectrum R =>
          localObstruction W (v.adicCompletion K) c),
         (fun i : ι => localObstruction W (Loc i) c))) = 1 ↔
      W.normM c = 1 ∧
      (∀ v : HeightOneSpectrum R,
        localObstruction W (v.adicCompletion K) c = 1) ∧
      (∀ i : ι,
        localObstruction W (Loc i) c = 1) by
    simp only [Prod.mk.injEq, Prod.one_eq_mk, and_assoc, Pi.one_apply, funext_iff]]
  exact (selmer_iff_complete_obstruction_vanishes W R Loc c).symm

/-- The substantive kernel identity, at the level of genuine subgroups. -/
theorem completeArithmeticResponse_ker_eq_selmer :
    (completeArithmeticResponse W R Loc).ker =
      W.selmerGroup₂ R Loc := by
  ext c
  exact mem_ker_completeArithmeticResponse_iff W R Loc c

/-- The global point-Kummer homomorphism is annihilated by the SAME
complete arithmetic response. In particular the norm, finite and infinite
obstructions vanish simultaneously and on the same curve. -/
theorem completeArithmeticResponse_comp_globalKummer_eq_one
    (P : Multiplicative W.Point) :
    completeArithmeticResponse W R Loc (W.μ P) = 1 := by
  apply (MonoidHom.mem_ker).mp
  rw [completeArithmeticResponse_ker_eq_selmer]
  exact W.range_μ_le_selmerGroup₂ R Loc ⟨P, rfl⟩

/-!
Strict frontier: a real cohomological identification is needed to turn
Selmer / im μ into Sha[2]. Higher levels and analytic rank are independent.
-/

end

end BSDStoll
