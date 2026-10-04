import Mathlib.RepresentationTheory.Homological.ContCohomology.Sha
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Genuine degree-one Tate–Shafarevich two-torsion donor

This module uses Mathlib's ACTUAL continuous-cohomology definition

  ContinuousCohomology.tateShafarevich

rather than a DASHI residual record.

For a field K, a family of field extensions f v / K, and a topological
Galois module A for Gal(K̄/K), define

  Sha¹(K,A) = ⋂_v ker(H¹(K,A) → H¹(f v,A))

and then take its genuine 2-torsion subgroup.

This is the correct target SHAPE for the BSD finite-level comparison once
A is instantiated by the elliptic two-torsion Galois module E[2].

What is NOT present in Mathlib/Stoll yet:
* the elliptic E[2] TopRep construction needed for this instantiation;
* the global elliptic Kummer connecting homomorphism into H¹(K,E[2]);
* the proof that Stoll's x-T Selmer presentation matches the cohomological one.

No theorem here identifies Stoll's arithmetic defect with Sha(E)[2].
-/

open CategoryTheory

namespace BSDCohomology

open ContinuousCohomology

universe u v

variable {K : Type u} {V : Type v}
variable [Field K]
variable (f : V → Type u)
variable [∀ v, Field (f v)]
variable [∀ v, Algebra K (f v)]
variable (A : TopRep ℤ (Field.absoluteGaloisGroup K))

/-- Genuine degree-one Tate–Shafarevich subgroup in continuous cohomology. -/
abbrev DegreeOneSha :
    AddSubgroup (continuousCohomology 1 A) :=
  ContinuousCohomology.tateShafarevich f A 1

/-- Genuine 2-torsion subgroup of the actual degree-one Sha group. -/
abbrev DegreeOneShaTwoTorsion :
    AddSubgroup (DegreeOneSha f A) :=
  (nsmulAddMonoidHom (α := DegreeOneSha f A) 2).ker

/-- Membership in genuine Sha¹ is exactly simultaneous vanishing of all
localization maps. -/
theorem mem_degreeOneSha_iff_allLocalizationsZero
    (x : continuousCohomology 1 A) :
    x ∈ DegreeOneSha f A ↔
      ∀ v : V,
        (ContinuousCohomology.map
          (Field.absoluteGaloisGroup.map (algebraMap K (f v)))
          (𝟙 _) 1).hom x = 0 := by
  exact ContinuousCohomology.mem_tateShafarevich f A 1 x

/-- Membership in Sha¹[2] is actual local triviality together with genuine
2-torsion in the Sha subgroup. -/
theorem mem_degreeOneShaTwoTorsion_iff
    (x : DegreeOneSha f A) :
    x ∈ DegreeOneShaTwoTorsion f A ↔
      2 • x = 0 := by
  rfl

/-- Every element of the selected subgroup is locally trivial by its actual
continuous-cohomology construction. -/
theorem degreeOneSha_element_localizesToZero
    (x : DegreeOneSha f A)
    (v : V) :
    (ContinuousCohomology.map
      (Field.absoluteGaloisGroup.map (algebraMap K (f v)))
      (𝟙 _) 1).hom x.1 = 0 := by
  exact
    (mem_degreeOneSha_iff_allLocalizationsZero f A x.1).1 x.2 v

/-- Genuine two-torsion Sha elements are, in particular, killed by two
inside the actual subgroup, not in a freely chosen quotient carrier. -/
theorem degreeOneShaTwoTorsion_killedByTwo
    (x : DegreeOneShaTwoTorsion f A) :
    2 • (x.1 : DegreeOneSha f A) = 0 := by
  exact x.2

/-!
MAX-CUT BSD-C/D BOUNDARY

The next positive theorem must instantiate A with E[2], construct the
global/local Kummer diagram, and prove an equivalence

  StollSelmer(E) / im(kappa_E) ≃+ DegreeOneShaTwoTorsion places E[2].

Until the E[2] Galois module and Kummer comparison exist, there is no honest
term of that type to construct.
-/

end BSDCohomology
